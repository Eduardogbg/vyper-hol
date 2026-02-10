structure venomIRTextLib = struct

open venomIRTermLib;

fun is_space c =
  c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r";

fun drop_while p s =
  let
    fun loop i =
      if i >= String.size s then String.size s
      else if p (String.sub (s, i)) then loop (i + 1)
      else i
  in
    loop 0
  end;

fun rdrop_while p s =
  let
    fun loop i =
      if i < 0 then ~1
      else if p (String.sub (s, i)) then loop (i - 1)
      else i
  in
    loop (String.size s - 1)
  end;

fun trim s =
  let
    val i = drop_while is_space s
    val j = rdrop_while is_space s
  in
    if j < i then ""
    else String.substring (s, i, j - i + 1)
  end;

fun strip_comment s =
  case String.fields (fn c => c = #";") s of
    [] => ""
  | h::_ => h;

fun split_first_space s =
  let
    fun loop i =
      if i >= String.size s then NONE
      else if is_space (String.sub (s, i)) then SOME i
      else loop (i + 1)
  in
    case loop 0 of
      NONE => (s, "")
    | SOME i =>
        (String.substring (s, 0, i),
         trim (String.substring (s, i + 1, String.size s - i - 1)))
  end;

fun split_operands s =
  let
    val parts = String.fields (fn c => c = #",") s
  in
    List.filter (fn t => t <> "") (List.map trim parts)
  end;

fun even_hex s = if String.size s mod 2 = 1 then "0" ^ s else s;

fun string_all p s =
  let
    fun loop i =
      if i >= String.size s then true
      else if p (String.sub (s, i)) then loop (i + 1)
      else false
  in
    loop 0
  end;

fun lit_from_hex s =
  let
    val hex = if String.isPrefix "0x" s then s else "0x" ^ s
  in
    mk_comb (Lit_tm, bytes32_from_hex ("0x" ^ even_hex (String.extract (hex, 2, NONE))))
  end;

fun parse_operand tok =
  if tok = "" then NONE
  else if String.isPrefix "%" tok then
    SOME (var (String.extract (tok, 1, NONE)))
  else if String.isPrefix "@" tok then
    SOME (lbl (String.extract (tok, 1, NONE)))
  else if String.isPrefix "0x" tok orelse string_all Char.isDigit tok then
    SOME (if String.isPrefix "0x" tok then lit_from_hex tok
          else lit (valOf (Int.fromString tok)))
  else
    SOME (lbl tok);

fun parse_operands s =
  List.mapPartial parse_operand (split_operands s);

fun normalize_opcode opstr =
  if opstr = "source" then "PARAM"
  else String.map Char.toUpper opstr;

(* ==========================================================================
   Refactored Parser (core + policy)
   ========================================================================== *)

datatype ir_stmt =
    IRLabel of string
  | IRInst of {outs: string list, opstr: string, args: string list};

fun parse_inst_core s =
  let
    val parts = String.fields (fn c => c = #"=") s
    val (outs, rhs) =
      case parts of
        [rhs] => ([], trim rhs)
      | [lhs, rhs] =>
          let
            val out = trim lhs
            val out' =
              if String.isPrefix "%" out then String.extract (out, 1, NONE)
              else out
          in
            ([out'], trim rhs)
          end
      | _ => raise Fail ("bad instruction: " ^ s)
    val (opstr, rest) = split_first_space rhs
    val args = if rest = "" then [] else split_operands rest
  in
    IRInst {outs = outs, opstr = opstr, args = args}
  end;

fun parse_lines_core text =
  let
    val raw = String.tokens (fn c => c = #"\n") text
    fun to_stmt s =
      let
        val t = trim (strip_comment s)
      in
        if t = "" then NONE
        else if String.isSuffix ":" t then
          SOME (IRLabel (String.substring (t, 0, String.size t - 1)))
        else SOME (parse_inst_core t)
      end
  in
    List.mapPartial to_stmt raw
  end;

fun build_blocks_core lines =
  let
    fun finish (NONE, insts, acc) = acc
      | finish (SOME lbl, insts, acc) =
          (lbl, List.rev insts) :: acc
    fun loop (lbl, insts, acc) ls =
      case ls of
        [] => List.rev (finish (lbl, insts, acc))
      | IRLabel l :: rest =>
          loop (SOME l, [], finish (lbl, insts, acc)) rest
      | IRInst s :: rest =>
          loop (lbl, IRInst s :: insts, acc) rest
  in
    loop (NONE, [], []) lines
  end;

fun normalize_inst_policy stmt =
  case stmt of
    IRInst {outs, opstr, args} =>
      let
        val op_norm = normalize_opcode opstr
        val args_ops = parse_operands (String.concatWith "," args)
        val (opcode, ops) =
          if args = [] then
            (case parse_operand opstr of
               SOME operand =>
                 if opstr = "source" then ("PARAM", [])
                 else ("ASSIGN", [operand])
             | NONE => (op_norm, []))
          else
            (op_norm, args_ops)
      in
        (opcode, ops, outs)
      end
  | IRLabel _ => raise Fail "normalize_inst_policy: expected instruction";

fun parse_function name text =
  let
    val stmts = parse_lines_core text
    val blocks = build_blocks_core stmts
    fun parse_block (lbl, inst_nodes, next_id) =
      let
        fun parse_insts ([], acc, id) = (List.rev acc, id)
          | parse_insts (stmt::rest, acc, id) =
              let
                val (opc, ops, outs) = normalize_inst_policy stmt
                val inst_tm = mk_inst id opc ops outs
              in
                parse_insts (rest, inst_tm::acc, id + 1)
              end
        val (insts, id') = parse_insts (inst_nodes, [], next_id)
      in
        (mk_block lbl insts, id')
      end
    fun parse_blocks ([], acc, id) = List.rev acc
      | parse_blocks ((lbl, inst_nodes)::rest, acc, id) =
          let
            val (bb, id') = parse_block (lbl, inst_nodes, id)
          in
            parse_blocks (rest, bb::acc, id')
          end
    val bbs = parse_blocks (blocks, [], 0)
  in
    mk_function name bbs
  end;

end

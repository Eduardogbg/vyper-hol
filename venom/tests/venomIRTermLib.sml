structure venomIRTermLib = struct

open HolKernel boolLib bossLib
     listSyntax pairSyntax stringSyntax optionSyntax numSyntax
     vfmTypesSyntax byteStringCacheLib intSyntax;

(* Types *)
val operand_ty = mk_thy_type{Thy="venomState",Tyop="operand",Args=[]};
val instruction_ty = mk_thy_type{Thy="venomInst",Tyop="instruction",Args=[]};
val basic_block_ty = mk_thy_type{Thy="venomInst",Tyop="basic_block",Args=[]};
val function_ty = mk_thy_type{Thy="venomInst",Tyop="ir_function",Args=[]};

(* Constructors *)
val Lit_tm = prim_mk_const{Thy="venomState",Name="Lit"};
val Var_tm = prim_mk_const{Thy="venomState",Name="Var"};
val Label_tm = prim_mk_const{Thy="venomState",Name="Label"};

fun opcode_const s = prim_mk_const{Thy="venomInst",Name=s};

fun mk_num n = numSyntax.mk_numeral (Arbnum.fromInt n);

fun hex_of_int n =
  let
    val hex = Int.fmt StringCvt.HEX n
    val hex' = if String.size hex mod 2 = 1 then "0" ^ hex else hex
  in
    "0x" ^ String.map Char.toLower hex'
  end;

fun lit n = mk_comb (Lit_tm, bytes32_from_hex (hex_of_int n));
fun var s = mk_comb (Var_tm, fromMLstring s);
fun lbl s = mk_comb (Label_tm, fromMLstring s);

fun mk_inst id opc ops outs =
  TypeBase.mk_record (instruction_ty, [
    ("inst_id", mk_num id),
    ("inst_opcode", opcode_const opc),
    ("inst_operands", mk_list (ops, operand_ty)),
    ("inst_outputs", mk_list (map fromMLstring outs, string_ty))
  ]);

fun mk_block label insts =
  TypeBase.mk_record (basic_block_ty, [
    ("bb_label", fromMLstring label),
    ("bb_instructions", mk_list (insts, instruction_ty))
  ]);

fun mk_function name blocks =
  TypeBase.mk_record (function_ty, [
    ("fn_name", fromMLstring name),
    ("fn_blocks", mk_list (blocks, basic_block_ty))
  ]);

end

(*
 * Algebraic Optimization (Venom IR) - Analysis Helpers
 *)

Theory algebraicOptAnalysis
Ancestors
  algebraicOptDefs

(* ==========================================================================
   Instruction and Use Traversal
   ========================================================================== *)

Definition rev_prepend_def:
  rev_prepend xs acc =
    case xs of
      [] => acc
    | x::rest => rev_prepend rest (x::acc)
End

Definition all_insts_blocks_rev_def:
  all_insts_blocks_rev bbs acc =
    case bbs of
      [] => acc
    | bb::rest =>
        all_insts_blocks_rev rest (rev_prepend bb.bb_instructions acc)
End

Definition all_insts_blocks_def:
  all_insts_blocks bbs = REVERSE (all_insts_blocks_rev bbs [])
End

Definition all_insts_def:
  all_insts fn = all_insts_blocks fn.fn_blocks
End

Definition inst_uses_var_def:
  inst_uses_var v inst = MEM (Var v) inst.inst_operands
End

Definition operand_list_has_var_def:
  operand_list_has_var v ops =
    case ops of
      [] => F
    | op::rest =>
        if op = Var v then T else operand_list_has_var v rest
End

Definition uses_of_var_insts_def:
  uses_of_var_insts v insts =
    case insts of
      [] => []
    | inst::rest =>
        if operand_list_has_var v inst.inst_operands then
          inst :: uses_of_var_insts v rest
        else
          uses_of_var_insts v rest
End

Definition uses_of_var_def:
  uses_of_var fn v = uses_of_var_insts v (all_insts fn)
End

Definition is_truthy_use_opcode_def:
  is_truthy_use_opcode ISZERO = T /\
  is_truthy_use_opcode JNZ = T /\
  is_truthy_use_opcode ASSERT = T /\
  is_truthy_use_opcode ASSERT_UNREACHABLE = T /\
  is_truthy_use_opcode _ = F
End

Definition is_prefer_iszero_opcode_def:
  is_prefer_iszero_opcode ISZERO = T /\
  is_prefer_iszero_opcode ASSERT = T /\
  is_prefer_iszero_opcode _ = F
End

Definition all_uses_truthy_ops_def:
  all_uses_truthy_ops uses =
    case uses of
      [] => T
    | inst::rest =>
        is_truthy_use_opcode inst.inst_opcode /\ all_uses_truthy_ops rest
End

Definition all_uses_prefer_iszero_ops_def:
  all_uses_prefer_iszero_ops uses =
    case uses of
      [] => T
    | inst::rest =>
        is_prefer_iszero_opcode inst.inst_opcode /\
        all_uses_prefer_iszero_ops rest
End

Definition uses_all_truthy_def:
  uses_all_truthy fn v <=>
    all_uses_truthy_ops (uses_of_var fn v)
End

Definition uses_prefer_iszero_def:
  uses_prefer_iszero fn v <=>
    all_uses_prefer_iszero_ops (uses_of_var fn v)
End

Definition uses_all_truthy_insts_def:
  uses_all_truthy_insts insts v <=>
    all_uses_truthy_ops (uses_of_var_insts v insts)
End

Definition uses_prefer_iszero_insts_def:
  uses_prefer_iszero_insts insts v <=>
    all_uses_prefer_iszero_ops (uses_of_var_insts v insts)
End

(* ==========================================================================
   Hint Computation
   ========================================================================== *)

Definition cmp_flip_hint_for_uses_def:
  cmp_flip_hint_for_uses insts inst uses =
    if ~is_comparator inst.inst_opcode then F
    else
      case inst.inst_operands of
        [op1; op2] =>
          if ~(is_lit op1 \/ (is_comparator inst.inst_opcode /\ is_lit op2))
          then F
          else
            (case uses of
               [after] =>
                 if is_prefer_iszero_opcode after.inst_opcode then
                   if after.inst_opcode = ISZERO then
                     (case inst_output after of
                        NONE => F
                      | SOME v2 =>
                          (case uses_of_var_insts v2 insts of
                             [use2] =>
                               if use2.inst_opcode = ASSERT then F else T
                           | _ => F))
                   else T
                 else F
             | _ => F)
      | _ => F
End

Definition cmp_flip_hint_insts_def:
  cmp_flip_hint_insts insts inst =
    case inst_output inst of
      NONE => F
    | SOME v =>
        cmp_flip_hint_for_uses insts inst (uses_of_var_insts v insts)
End

Definition cmp_flip_hint_def:
  cmp_flip_hint fn inst = cmp_flip_hint_insts (all_insts fn) inst
End

Definition compute_hint_insts_def:
  compute_hint_insts insts inst =
    case inst_output inst of
      NONE => default_hint
    | SOME v =>
        let uses = uses_of_var_insts v insts in
        <| prefer_iszero := all_uses_prefer_iszero_ops uses;
           is_truthy := all_uses_truthy_ops uses;
           cmp_flip := cmp_flip_hint_for_uses insts inst uses |>
End

Definition compute_hint_def:
  compute_hint fn inst =
    compute_hint_insts (all_insts fn) inst
End

Definition compute_hints_from_insts_def:
  compute_hints_from_insts insts work =
    case work of
      [] => []
    | inst::rest =>
        (inst.inst_id, compute_hint_insts insts inst) ::
        compute_hints_from_insts insts rest
End

Definition compute_hints_insts_def:
  compute_hints_insts fn insts =
    compute_hints_from_insts (all_insts fn) insts
End

Definition compute_hints_def:
  compute_hints fn =
    let insts = all_insts fn in
      compute_hints_from_insts insts insts
End

Definition cmp_after_action_for_inst_insts_def:
  cmp_after_action_for_inst_insts insts inst =
    case inst_output inst of
      NONE => []
    | SOME v =>
        let uses = uses_of_var_insts v insts in
          if ~cmp_flip_hint_for_uses insts inst uses then []
          else
            (case uses of
               [after] =>
                 (case after.inst_opcode of
                    ISZERO => [(after.inst_id, CMP_AFTER_REPLACE v)]
                  | ASSERT => [(after.inst_id, CMP_AFTER_INSERT v)]
                  | _ => [])
             | _ => [])
End

Definition cmp_after_action_for_inst_def:
  cmp_after_action_for_inst fn inst =
    cmp_after_action_for_inst_insts (all_insts fn) inst
End

Definition compute_cmp_after_from_insts_acc_def:
  compute_cmp_after_from_insts_acc insts work acc =
    case work of
      [] => REVERSE acc
    | inst::rest =>
        let acts = cmp_after_action_for_inst_insts insts inst in
          compute_cmp_after_from_insts_acc insts rest (rev_prepend acts acc)
End

Definition compute_cmp_after_from_insts_def:
  compute_cmp_after_from_insts insts work =
    compute_cmp_after_from_insts_acc insts work []
End

Definition compute_cmp_after_insts_def:
  compute_cmp_after_insts fn insts =
    compute_cmp_after_from_insts (all_insts fn) insts
End

Definition compute_cmp_after_def:
  compute_cmp_after fn =
    let insts = all_insts fn in
      compute_cmp_after_from_insts insts insts
End

Definition cmp_after_lookup_def:
  cmp_after_lookup cmap id = ALOOKUP cmap id
End

(* ==========================================================================
   Per-use Substitution (iszero-chain rewrite)
   ========================================================================== *)

Definition indices_of_var_aux_def:
  indices_of_var_aux v idx ops =
    case ops of
      [] => []
    | op::ops' =>
        if op = Var v then
          idx :: indices_of_var_aux v (SUC idx) ops'
        else
          indices_of_var_aux v (SUC idx) ops'
End

Definition indices_of_var_def:
  indices_of_var v ops = indices_of_var_aux v 0 ops
End

Definition use_subst_for_inst_def:
  use_subst_for_inst v op inst =
    MAP (\i. ((inst.inst_id, i), op)) (indices_of_var v inst.inst_operands)
End

Definition find_inst_output_insts_def:
  find_inst_output_insts v insts =
    case insts of
      [] => NONE
    | inst::rest =>
        if inst_output inst = SOME v then SOME inst
        else find_inst_output_insts v rest
End

Definition find_inst_output_def:
  find_inst_output fn v = find_inst_output_insts v (all_insts fn)
End

Definition find_inst_id_insts_def:
  find_inst_id_insts id insts =
    case insts of
      [] => NONE
    | inst::rest =>
        if inst.inst_id = id then SOME inst
        else find_inst_id_insts id rest
End

Definition find_inst_id_def:
  find_inst_id fn id = find_inst_id_insts id (all_insts fn)
End

Definition iszero_chain_aux_insts_def:
  iszero_chain_aux_insts insts 0 op acc = acc /\
  iszero_chain_aux_insts insts (SUC n) op acc =
    case op of
      Var v =>
        (case find_inst_output_insts v insts of
           NONE => acc
         | SOME inst =>
             if inst.inst_opcode = ISZERO then
               (case inst.inst_operands of
                  [op'] => iszero_chain_aux_insts insts n op' (inst::acc)
                | _ => acc)
             else acc)
    | _ => acc
End

Definition iszero_chain_aux_def:
  iszero_chain_aux fn n op acc = iszero_chain_aux_insts (all_insts fn) n op acc
End

Definition iszero_chain_insts_def:
  iszero_chain_insts insts op =
    iszero_chain_aux_insts insts (LENGTH insts) op []
End

Definition iszero_chain_def:
  iszero_chain fn op =
    iszero_chain_insts (all_insts fn) op
End

Definition iszero_subst_for_use_def:
  iszero_subst_for_use v chain use_inst =
    if use_inst.inst_opcode = ISZERO then []
    else
      let k = LENGTH chain in
      let keep =
        if use_inst.inst_opcode = JNZ \/
           use_inst.inst_opcode = ASSERT \/
           use_inst.inst_opcode = ASSERT_UNREACHABLE then
          1 - (k MOD 2)
        else
          1 + (k MOD 2)
      in
        if keep >= k then []
        else
          (case EL keep chain of
             inst =>
               (case inst.inst_operands of
                  [op] => use_subst_for_inst v op use_inst
                | _ => []))
End

Definition iszero_subst_for_uses_acc_def:
  iszero_subst_for_uses_acc v chain uses acc =
    case uses of
      [] => REVERSE acc
    | use_inst::rest =>
        let sigma = iszero_subst_for_use v chain use_inst in
          iszero_subst_for_uses_acc v chain rest (rev_prepend sigma acc)
End

Definition iszero_subst_for_uses_def:
  iszero_subst_for_uses v chain uses =
    iszero_subst_for_uses_acc v chain uses []
End

Definition iszero_subst_for_inst_insts_def:
  iszero_subst_for_inst_insts insts inst =
    case inst.inst_opcode of
      ISZERO =>
        (case inst_output inst of
           NONE => []
         | SOME v =>
             (case inst.inst_operands of
                [op] =>
                  let chain = iszero_chain_insts insts op in
                    if chain = [] then []
                    else
                      iszero_subst_for_uses v chain (uses_of_var_insts v insts)
              | _ => []))
    | _ => []
End

Definition iszero_subst_for_inst_def:
  iszero_subst_for_inst fn inst =
    iszero_subst_for_inst_insts (all_insts fn) inst
End

Definition compute_iszero_subst_from_insts_acc_def:
  compute_iszero_subst_from_insts_acc insts work acc =
    case work of
      [] => REVERSE acc
    | inst::rest =>
        let sigma = iszero_subst_for_inst_insts insts inst in
          compute_iszero_subst_from_insts_acc insts rest (rev_prepend sigma acc)
End

Definition compute_iszero_subst_from_insts_def:
  compute_iszero_subst_from_insts insts work =
    compute_iszero_subst_from_insts_acc insts work []
End

Definition compute_iszero_subst_insts_def:
  compute_iszero_subst_insts fn insts =
    compute_iszero_subst_from_insts (all_insts fn) insts
End

Definition compute_iszero_subst_def:
  compute_iszero_subst fn =
    let insts = all_insts fn in
      compute_iszero_subst_from_insts insts insts
End

Definition subst_operands_use_aux_def:
  subst_operands_use_aux sigma inst_id idx ops =
    case ops of
      [] => []
    | op::ops' =>
        let op' =
          case ALOOKUP sigma (inst_id, idx) of
            SOME op2 => op2
          | NONE => op
        in
          op'::subst_operands_use_aux sigma inst_id (SUC idx) ops'
End

Definition subst_inst_use_def:
  subst_inst_use sigma inst =
    inst with inst_operands :=
      subst_operands_use_aux sigma inst.inst_id 0 inst.inst_operands
End

Definition subst_insts_use_def:
  subst_insts_use sigma insts =
    case insts of
      [] => []
    | inst::rest =>
        subst_inst_use sigma inst :: subst_insts_use sigma rest
End

Definition subst_block_use_def:
  subst_block_use sigma bb =
    bb with bb_instructions := subst_insts_use sigma bb.bb_instructions
End

Definition subst_blocks_use_def:
  subst_blocks_use sigma bbs =
    case bbs of
      [] => []
    | bb::rest =>
        subst_block_use sigma bb :: subst_blocks_use sigma rest
End

Definition subst_function_use_def:
  subst_function_use sigma fn =
    fn with fn_blocks := subst_blocks_use sigma fn.fn_blocks
End

(* Operand substitution (fmap from var name to var name) *)

Definition subst_operand_def:
  subst_operand sigma op =
    case op of
      Var v =>
        (case FLOOKUP sigma v of
           SOME v' => Var v'
         | NONE => op)
    | _ => op
End

Definition subst_operands_def:
  subst_operands sigma ops = MAP (subst_operand sigma) ops
End

Definition subst_inst_def:
  subst_inst sigma inst =
    inst with inst_operands := subst_operands sigma inst.inst_operands
End

Definition subst_block_def:
  subst_block sigma bb =
    bb with bb_instructions := MAP (subst_inst sigma) bb.bb_instructions
End

Definition subst_function_def:
  subst_function sigma fn =
    fn with fn_blocks := MAP (subst_block sigma) fn.fn_blocks
End

(* Operand substitution (alist from var name to operand) *)

Definition subst_operand_op_def:
  subst_operand_op sigma op =
    case op of
      Var v =>
        (case ALOOKUP sigma v of
           SOME op' => op'
         | NONE => op)
    | _ => op
End

Definition subst_operands_op_def:
  subst_operands_op sigma ops = MAP (subst_operand_op sigma) ops
End

Definition subst_inst_op_def:
  subst_inst_op sigma inst =
    inst with inst_operands := subst_operands_op sigma inst.inst_operands
End

Definition subst_block_op_def:
  subst_block_op sigma bb =
    bb with bb_instructions := MAP (subst_inst_op sigma) bb.bb_instructions
End

Definition subst_function_op_def:
  subst_function_op sigma fn =
    fn with fn_blocks := MAP (subst_block_op sigma) fn.fn_blocks
End

Definition iszero_var_def:
  iszero_var fn v <=>
    ?bb inst.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = ISZERO /\
      inst.inst_outputs = [v]
End

Definition iszero_subst_def:
  iszero_subst fn sigma <=>
    !v v'. FLOOKUP sigma v = SOME v' ==> iszero_var fn v
End

Definition rewrite_iszero_chains_def:
  rewrite_iszero_chains fn fn' <=>
    ?sigma.
      iszero_subst fn sigma /\
      fn' = subst_function sigma fn
End

Definition iszero_subst_op_def:
  iszero_subst_op fn sigma <=>
    !v op. ALOOKUP sigma v = SOME op ==> iszero_var fn v
End

Definition iszero_subst_use_def:
  iszero_subst_use fn sigma <=>
    !id idx op.
      ALOOKUP sigma (id, idx) = SOME op ==>
        (case find_inst_id fn id of
           NONE => F
         | SOME inst =>
             idx < LENGTH inst.inst_operands /\
             (case EL idx inst.inst_operands of
                Var v => iszero_var fn v
              | _ => F))
End

Definition rewrite_iszero_chains_op_def:
  rewrite_iszero_chains_op fn fn' <=>
    ?sigma.
      iszero_subst_op fn sigma /\
      fn' = subst_function_op sigma fn
End

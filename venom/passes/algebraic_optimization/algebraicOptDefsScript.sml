(*
 * Algebraic Optimization (Venom IR) - Shared Definitions
 *)

Theory algebraicOptDefs
Ancestors
  list string words finite_map alist integer arithmetic
  venomState venomInst

(* ==========================================================================
   Operand Helpers
   ========================================================================== *)

Definition is_lit_def:
  is_lit op =
    case op of
      Lit _ => T
    | _ => F
End

Definition is_label_def:
  is_label op =
    case op of
      Label _ => T
    | _ => F
End

Definition lit_eq_def:
  lit_eq op w =
    case op of
      Lit v => (v = w)
    | _ => F
End

Definition lit_is_zero_def:
  lit_is_zero op = lit_eq op (0w:bytes32)
End

Definition lit_is_one_def:
  lit_is_one op = lit_eq op (1w:bytes32)
End

Definition lit_is_ones_def:
  lit_is_ones op = lit_eq op (~(0w:bytes32))
End

(* ==========================================================================
   Analysis Hints (per-instruction)
   ========================================================================== *)

Datatype:
  opt_hint = <|
    prefer_iszero: bool;
    is_truthy: bool;
    cmp_flip: bool
  |>
End

Datatype:
  cmp_after_action =
    | CMP_AFTER_REPLACE string
    | CMP_AFTER_INSERT string
End

Datatype:
  value_range = <|
    vr_is_top: bool;
    vr_is_empty: bool;
    vr_lo: int;
    vr_hi: int
  |>
End

Definition default_hint_def:
  default_hint = <|
    prefer_iszero := F;
    is_truthy := F;
    cmp_flip := F
  |>
End

Definition hint_lookup_def:
  hint_lookup hints id =
    case ALOOKUP hints id of
      SOME h => h
    | NONE => default_hint
End

(* ==========================================================================
   Range Analysis Inputs (abstract)
   ========================================================================== *)

Definition range_top_def:
  range_top = <|
    vr_is_top := T;
    vr_is_empty := F;
    vr_lo := 0;
    vr_hi := 0
  |>
End

Definition range_lookup_def:
  range_lookup ranges inst_id op =
    case ALOOKUP ranges (inst_id, op) of
      SOME r => r
    | NONE => range_top
End

Definition lit_int_signed_def:
  lit_int_signed op =
    case op of
      Lit w => SOME (w2i w)
    | _ => NONE
End

Definition lit_int_unsigned_def:
  lit_int_unsigned op =
    case op of
      Lit w => SOME (((& (w2n w)) : int))
    | _ => NONE
End

Definition signed_min_for_bytes_def:
  signed_min_for_bytes n =
    - ((& (2 EXP (8 * (n + 1) - 1))) : int)
End

Definition signed_max_for_bytes_def:
  signed_max_for_bytes n =
    ((& (2 EXP (8 * (n + 1) - 1))) : int) - 1
End

(* ==========================================================================
   Instruction Builders
   ========================================================================== *)

Definition mk_assign_def:
  mk_assign inst op =
    inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>
End

Definition mk_const_def:
  mk_const inst w = mk_assign inst (Lit w)
End

Definition lit_of_num_def:
  lit_of_num n = Lit ((n2w n):bytes32)
End

Definition mk_not_def:
  mk_not inst op =
    inst with <| inst_opcode := NOT; inst_operands := [op] |>
End

Definition fresh_var_def:
  fresh_var (id:num) = STRCAT "alg_tmp_" (toString id)
End

(* ==========================================================================
   Constants and Predicates
   ========================================================================== *)

Definition max_uint256_def:
  max_uint256 = (~(0w:bytes32))
End

Definition min_uint256_def:
  min_uint256 = (0w:bytes32)
End

Definition min_int256_def:
  min_int256 = word_lsl (1w:bytes32) 255
End

Definition max_int256_def:
  max_int256 = word_1comp min_int256
End

Definition min_int256_i_def:
  min_int256_i = w2i min_int256
End

Definition max_int256_i_def:
  max_int256_i = w2i max_int256
End

Definition is_commutative_def:
  is_commutative op <=>
    MEM op [ADD; MUL; AND; OR; XOR; EQ]
End

Definition is_comparator_def:
  is_comparator op <=>
    MEM op [GT; LT; SGT; SLT]
End

Definition flip_comparator_def:
  flip_comparator GT = LT /\
  flip_comparator LT = GT /\
  flip_comparator SGT = SLT /\
  flip_comparator SLT = SGT /\
  flip_comparator op = op
End

Definition is_pow2_num_def:
  is_pow2_num n = (n <> 0 /\ ((2:num) ** LOG2 n = n))
End

Definition log2_num_def:
  log2_num n = LOG2 n
End

Definition is_pow2_lit_def:
  is_pow2_lit op <=>
    case op of
      Lit w => is_pow2_num (w2n w)
    | _ => F
End

Definition log2_lit_def:
  log2_lit op =
    case op of
      Lit w => log2_num (w2n w)
    | _ => 0
End

Definition is_gt_op_def:
  is_gt_op GT = T /\
  is_gt_op SGT = T /\
  is_gt_op _ = F
End

Definition is_signed_cmp_def:
  is_signed_cmp SGT = T /\
  is_signed_cmp SLT = T /\
  is_signed_cmp _ = F
End

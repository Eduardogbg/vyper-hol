(*
 * Algebraic Optimization (Venom IR) - Transform
 *
 * Local algebraic rewrites plus limited operand rewrites (iszero-chain
 * simplification) and offset lowering.
 *)

Theory algebraicOptTransform
Ancestors
  algebraicOptAnalysis

(* ==========================================================================
   Flipping Helpers
   ========================================================================== *)

Definition flip_flippable_inst_def:
  flip_flippable_inst inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_commutative inst.inst_opcode then
          inst with inst_operands := [op2; op1]
        else if is_comparator inst.inst_opcode then
          inst with <| inst_opcode := flip_comparator inst.inst_opcode;
                        inst_operands := [op2; op1] |>
        else inst
    | _ => inst
End

Definition flip_flippable_left_def:
  flip_flippable_left inst =
    case inst.inst_operands of
      [op1; op2] =>
        if (is_commutative inst.inst_opcode \/ is_comparator inst.inst_opcode) /\
           is_lit op2 /\ ~is_lit op1 then
          flip_flippable_inst inst
        else inst
    | _ => inst
End

Definition flip_flippable_right_def:
  flip_flippable_right inst =
    case inst.inst_operands of
      [op1; op2] =>
        if (is_commutative inst.inst_opcode \/ is_comparator inst.inst_opcode) /\
           is_lit op1 /\ ~is_lit op2 then
          flip_flippable_inst inst
        else inst
    | _ => inst
End

Definition flip_flippable_list_def:
  flip_flippable_list insts = MAP flip_flippable_right insts
End

(* ==========================================================================
   Offset Lowering
   ========================================================================== *)

Definition handle_offset_inst_def:
  handle_offset_inst inst =
    case inst.inst_opcode of
      ADD =>
        (case inst.inst_operands of
           [op1; op2] =>
             if is_lit op1 /\ is_label op2 then
               inst with inst_opcode := OFFSET
             else inst
         | _ => inst)
    | _ => inst
End

Definition handle_offset_block_def:
  handle_offset_block bb =
    bb with bb_instructions := MAP handle_offset_inst bb.bb_instructions
End

Definition handle_offset_function_def:
  handle_offset_function fn =
    fn with fn_blocks := MAP handle_offset_block fn.fn_blocks
End

(* ==========================================================================
   Small Rewrite Helpers (return list of instructions)
   ========================================================================== *)

Definition rewrite_add_def:
  rewrite_add inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 then [mk_assign inst op2]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_sub_def:
  rewrite_sub inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else if lit_is_ones op2 then [mk_not inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_xor_def:
  rewrite_xor inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_zero op1 then [mk_assign inst op2]
        else if lit_is_ones op1 then [mk_not inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_and_def:
  rewrite_and inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_ones op1 then [mk_assign inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_or_def:
  rewrite_or is_truthy inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_ones op1 then [mk_const inst max_uint256]
        else if is_truthy /\ is_lit op1 /\ ~lit_is_zero op1 then
          [mk_const inst (1w:bytes32)]
        else if lit_is_zero op1 then [mk_assign inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_mul_def:
  rewrite_mul inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_assign inst op2]
        else if is_pow2_lit op1 then
          let n = log2_lit op1 in
          [inst with <| inst_opcode := SHL; inst_operands := [op2; lit_of_num n] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_div_def:
  rewrite_div inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_assign inst op2]
        else if is_pow2_lit op1 then
          let n = log2_lit op1 in
          [inst with <| inst_opcode := SHR; inst_operands := [op2; lit_of_num n] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_sdiv_def:
  rewrite_sdiv inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_assign inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_mod_def:
  rewrite_mod inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_const inst (0w:bytes32)]
        else if is_pow2_lit op1 then
          let n = w2n (case op1 of Lit w => w | _ => 0w) in
          [inst with <| inst_opcode := AND;
                         inst_operands := [lit_of_num (n - 1); op2] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_smod_def:
  rewrite_smod inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_const inst (0w:bytes32)]
        else [inst]
    | _ => [inst]
End

Definition rewrite_exp_def:
  rewrite_exp inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 then [mk_const inst (1w:bytes32)]
        else if lit_is_one op2 then [mk_const inst (1w:bytes32)]
        else if lit_is_zero op2 then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op1] |>]
        else if lit_is_one op1 then [mk_assign inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_shift_def:
  rewrite_shift inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op2 then [mk_assign inst op1] else [inst]
    | _ => [inst]
End

Definition rewrite_signextend_insts_def:
  rewrite_signextend_insts ranges insts inst =
    case inst.inst_operands of
      [x_op; n_op] =>
        (case n_op of
           Lit w =>
             let n = w2n w in
             if n >= 31 then [mk_assign inst x_op]
             else
               let r = range_lookup ranges inst.inst_id x_op in
               let within =
                 (~r.vr_is_top /\ ~r.vr_is_empty /\
                  r.vr_lo >= signed_min_for_bytes n /\
                  r.vr_hi <= signed_max_for_bytes n)
               in
                 if within then [mk_assign inst x_op]
                 else
                   (case x_op of
                      Var v =>
                        (case find_inst_output_insts v insts of
                           SOME inst2 =>
                             if inst2.inst_opcode = SIGNEXTEND then
                               (case inst2.inst_operands of
                                  [x2; inner_n] =>
                                    (case inner_n of
                                       Lit w2 =>
                                         if n >= w2n w2 then [mk_assign inst x_op]
                                         else [inst]
                                     | _ => [inst])
                                | _ => [inst])
                             else [inst]
                           | _ => [inst])
                    | _ => [inst])
         | _ => [inst])
    | _ => [inst]
End

Definition rewrite_signextend_def:
  rewrite_signextend ranges fn inst =
    rewrite_signextend_insts ranges (all_insts fn) inst
End

Definition rewrite_eq_def:
  rewrite_eq prefer_iszero inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (1w:bytes32)]
        else if lit_is_zero op1 then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op2] |>]
        else if lit_is_ones op1 then
          let tmp_v =
            case inst_single_output inst of
              SOME v => v
            | NONE => fresh_var inst.inst_id in
          let tmp = mk_inst (inst.inst_id + 1) NOT [op2] [tmp_v] in
          [tmp; inst with <| inst_opcode := ISZERO;
                              inst_operands := [Var tmp_v] |>]
        else if prefer_iszero then
          let tmp_v =
            case inst_single_output inst of
              SOME v => v
            | NONE => fresh_var inst.inst_id in
          let tmp = mk_inst (inst.inst_id + 1) XOR [op1; op2] [tmp_v] in
          [tmp; inst with <| inst_opcode := ISZERO;
                              inst_operands := [Var tmp_v] |>]
        else [inst]
    | _ => [inst]
End

Definition cmp_range_opt_def:
  cmp_range_opt ranges inst signed is_gt op1 op2 =
    let a_op = op2 in
    let b_op = op1 in
    if is_lit a_op /\ ~is_lit b_op then
      let r = range_lookup ranges inst.inst_id b_op in
      if ~r.vr_is_top /\ ~r.vr_is_empty then
        let lit =
          if signed then
            if r.vr_hi <= max_int256_i then lit_int_signed a_op else NONE
          else
            if r.vr_lo >= (0:int) then lit_int_unsigned a_op else NONE
        in
          (case lit of
             NONE => NONE
           | SOME l =>
               if is_gt then
                 if l > r.vr_hi then SOME (1w:bytes32)
                 else if l <= r.vr_lo then SOME (0w:bytes32)
                 else NONE
               else
                 if l < r.vr_lo then SOME (1w:bytes32)
                 else if l >= r.vr_hi then SOME (0w:bytes32)
                 else NONE)
      else NONE
    else if is_lit b_op /\ ~is_lit a_op then
      let r = range_lookup ranges inst.inst_id a_op in
      if ~r.vr_is_top /\ ~r.vr_is_empty then
        let lit =
          if signed then
            if r.vr_hi <= max_int256_i then lit_int_signed b_op else NONE
          else
            if r.vr_lo >= (0:int) then lit_int_unsigned b_op else NONE
        in
          (case lit of
             NONE => NONE
           | SOME l =>
               if is_gt then
                 if r.vr_lo > l then SOME (1w:bytes32)
                 else if r.vr_hi <= l then SOME (0w:bytes32)
                 else NONE
               else
                 if r.vr_hi < l then SOME (1w:bytes32)
                 else if r.vr_lo >= l then SOME (0w:bytes32)
                 else NONE)
      else NONE
    else NONE
End

Definition cmp_boundary_rewrite_def:
  cmp_boundary_rewrite ranges prefer_iszero cmp_flip inst op1 op2 signed is_gt =
    let lo = if signed then min_int256 else min_uint256 in
    let hi = if signed then max_int256 else max_uint256 in
    let almost_always = if is_gt then lo else hi in
    let never = if is_gt then hi else lo in
    let almost_never = if is_gt then word_sub hi (1w:bytes32)
                       else word_add lo (1w:bytes32) in
      if lit_eq op1 never then [mk_const inst (0w:bytes32)]
      else if lit_eq op1 almost_never then
        [inst with <| inst_opcode := EQ;
                       inst_operands := [op2; Lit never] |>]
      else if prefer_iszero /\ lit_eq op1 almost_always then
        let tmp_v =
          case inst_single_output inst of
            SOME v => v
          | NONE => fresh_var inst.inst_id in
        let tmp = mk_inst (inst.inst_id + 1) EQ [op1; op2]
                        [tmp_v] in
        [tmp; inst with <| inst_opcode := ISZERO;
                            inst_operands := [Var tmp_v] |>]
      else if inst.inst_opcode = GT /\ lit_is_zero op1 then
        let tmp_v =
          case inst_single_output inst of
            SOME v => v
          | NONE => fresh_var inst.inst_id in
        let tmp = mk_inst (inst.inst_id + 1) ISZERO [op2]
                        [tmp_v] in
        [tmp; inst with <| inst_opcode := ISZERO;
                            inst_operands := [Var tmp_v] |>]
      else if cmp_flip /\ is_lit op1 then
        let new_op = flip_comparator inst.inst_opcode in
        let adj =
          if is_gt then
            word_add (case op1 of Lit w => w | _ => 0w) (1w:bytes32)
          else
            word_sub (case op1 of Lit w => w | _ => 0w) (1w:bytes32)
        in
          [inst with <| inst_opcode := new_op;
                         inst_operands := [Lit adj; op2] |>]
      else [inst]
End

Definition rewrite_cmp_def:
  rewrite_cmp ranges prefer_iszero cmp_flip inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else
          let signed = is_signed_cmp inst.inst_opcode in
          let is_gt = is_gt_op inst.inst_opcode in
          let range_opt = cmp_range_opt ranges inst signed is_gt op1 op2 in
            case range_opt of
              SOME w => [mk_const inst w]
            | NONE =>
                cmp_boundary_rewrite ranges prefer_iszero cmp_flip inst op1 op2
                  signed is_gt
    | _ => [inst]
End

(* ==========================================================================
   Combined Instruction Transform (parameterized by analysis)
   ========================================================================== *)

Definition apply_cmp_after_action_def:
  apply_cmp_after_action act inst =
    case act of
      CMP_AFTER_REPLACE v =>
        [mk_assign inst (Var v)]
    | CMP_AFTER_INSERT v =>
        let tmp =
          case inst_single_output inst of
            SOME v' => v'
          | NONE => fresh_var inst.inst_id in
        let isz = mk_inst (inst.inst_id + 1) ISZERO [Var v] [tmp] in
        let inst' = inst with inst_operands := [Var tmp] in
        [isz; inst']
End

Definition transform_inst_list_ctx_def:
  transform_inst_list_ctx ranges cmp_after insts
                          prefer_iszero is_truthy cmp_flip inst =
    case cmp_after_lookup cmp_after inst.inst_id of
      SOME act => apply_cmp_after_action act inst
    | NONE =>
        let inst1 = flip_flippable_left inst in
        let insts' =
          case inst1.inst_opcode of
            ADD => rewrite_add inst1
          | SUB => rewrite_sub inst1
          | XOR => rewrite_xor inst1
          | AND => rewrite_and inst1
          | OR => rewrite_or is_truthy inst1
          | MUL => rewrite_mul inst1
          | Div => rewrite_div inst1
          | SDIV => rewrite_sdiv inst1
          | Mod => rewrite_mod inst1
          | SMOD => rewrite_smod inst1
          | venomInst$EXP => rewrite_exp inst1
          | SHL => rewrite_shift inst1
          | SHR => rewrite_shift inst1
          | SAR => rewrite_shift inst1
          | SIGNEXTEND => rewrite_signextend_insts ranges insts inst1
          | EQ => rewrite_eq prefer_iszero inst1
          | GT => rewrite_cmp ranges prefer_iszero cmp_flip inst1
          | LT => rewrite_cmp ranges prefer_iszero cmp_flip inst1
          | SGT => rewrite_cmp ranges prefer_iszero cmp_flip inst1
          | SLT => rewrite_cmp ranges prefer_iszero cmp_flip inst1
          | _ => [inst1]
        in
          flip_flippable_list insts'
End

Definition transform_inst_list_def:
  transform_inst_list ranges cmp_after fn prefer_iszero is_truthy cmp_flip inst =
    transform_inst_list_ctx ranges cmp_after (all_insts fn)
      prefer_iszero is_truthy cmp_flip inst
End

(* ==========================================================================
   Block / Function / Context Transforms
   ========================================================================== *)

Definition transform_insts_ctx_acc_def:
  transform_insts_ctx_acc ranges cmp_after insts
                          prefer_iszero is_truthy cmp_flip work acc =
    case work of
      [] => REVERSE acc
    | inst::rest =>
        let out =
          transform_inst_list_ctx ranges cmp_after insts
            prefer_iszero is_truthy cmp_flip inst in
          transform_insts_ctx_acc ranges cmp_after insts
            prefer_iszero is_truthy cmp_flip rest (rev_prepend out acc)
End

Definition transform_insts_ctx_def:
  transform_insts_ctx ranges cmp_after insts
                      prefer_iszero is_truthy cmp_flip work =
    transform_insts_ctx_acc ranges cmp_after insts
      prefer_iszero is_truthy cmp_flip work []
End

Definition transform_block_ctx_def:
  transform_block_ctx ranges cmp_after insts
                      prefer_iszero is_truthy cmp_flip bb =
    bb with bb_instructions :=
      transform_insts_ctx ranges cmp_after insts
        prefer_iszero is_truthy cmp_flip bb.bb_instructions
End

Definition transform_blocks_ctx_def:
  transform_blocks_ctx ranges cmp_after insts
                       prefer_iszero is_truthy cmp_flip bbs =
    case bbs of
      [] => []
    | bb::rest =>
        transform_block_ctx ranges cmp_after insts
          prefer_iszero is_truthy cmp_flip bb ::
        transform_blocks_ctx ranges cmp_after insts
          prefer_iszero is_truthy cmp_flip rest
End

Definition transform_block_def:
  transform_block ranges cmp_after fn prefer_iszero is_truthy cmp_flip bb =
    transform_block_ctx ranges cmp_after (all_insts fn)
      prefer_iszero is_truthy cmp_flip bb
End

Definition transform_function_def:
  transform_function ranges cmp_after fn prefer_iszero is_truthy cmp_flip =
    let insts = all_insts fn in
      fn with fn_blocks :=
        transform_blocks_ctx ranges cmp_after insts
          prefer_iszero is_truthy cmp_flip fn.fn_blocks
End

Definition transform_inst_list_hints_ctx_def:
  transform_inst_list_hints_ctx ranges cmp_after insts hints inst =
    let h = hint_lookup hints inst.inst_id in
      transform_inst_list_ctx ranges cmp_after insts
        h.prefer_iszero h.is_truthy h.cmp_flip inst
End

Definition transform_inst_list_hints_def:
  transform_inst_list_hints ranges cmp_after fn hints inst =
    transform_inst_list_hints_ctx ranges cmp_after (all_insts fn) hints inst
End

Definition transform_insts_hints_ctx_acc_def:
  transform_insts_hints_ctx_acc ranges cmp_after insts hints work acc =
    case work of
      [] => REVERSE acc
    | inst::rest =>
        let out = transform_inst_list_hints_ctx ranges cmp_after insts hints inst in
          transform_insts_hints_ctx_acc ranges cmp_after insts hints rest
            (rev_prepend out acc)
End

Definition transform_insts_hints_ctx_def:
  transform_insts_hints_ctx ranges cmp_after insts hints work =
    transform_insts_hints_ctx_acc ranges cmp_after insts hints work []
End

Definition transform_block_hints_ctx_def:
  transform_block_hints_ctx ranges cmp_after insts hints bb =
    bb with bb_instructions :=
      transform_insts_hints_ctx ranges cmp_after insts hints bb.bb_instructions
End

Definition transform_block_hints_def:
  transform_block_hints ranges cmp_after fn hints bb =
    transform_block_hints_ctx ranges cmp_after (all_insts fn) hints bb
End

Definition transform_blocks_hints_ctx_def:
  transform_blocks_hints_ctx ranges cmp_after insts hints bbs =
    case bbs of
      [] => []
    | bb::rest =>
        transform_block_hints_ctx ranges cmp_after insts hints bb ::
        transform_blocks_hints_ctx ranges cmp_after insts hints rest
End

Definition transform_function_hints_range_def:
  transform_function_hints_range ranges cmp_after hints fn =
    let insts = all_insts fn in
      fn with fn_blocks :=
        transform_blocks_hints_ctx ranges cmp_after insts hints fn.fn_blocks
End

Definition algebraic_opt_once_def:
  algebraic_opt_once ranges fn =
    let insts = all_insts fn in
    let hints = compute_hints_from_insts insts insts in
    let cmp_after = compute_cmp_after_from_insts insts insts in
      fn with fn_blocks :=
        transform_blocks_hints_ctx ranges cmp_after insts hints fn.fn_blocks
End

Definition transform_function_hints_def:
  transform_function_hints hints fn =
    transform_function_hints_range [] (compute_cmp_after fn) hints fn
End

(* ==========================================================================
   Pass Definition
   ========================================================================== *)

Definition algebraic_opt_pass_def:
  algebraic_opt_pass ranges fn =
    let fn0 = handle_offset_function fn in
    let fn1 = algebraic_opt_once ranges fn0 in
    let sigma = compute_iszero_subst fn1 in
    let fn2 = subst_function_use sigma fn1 in
    let fn3 = algebraic_opt_once ranges fn2 in
      fn3
End

Definition algebraic_opt_transform_def:
  algebraic_opt_transform ranges fn fn' <=> fn' = algebraic_opt_pass ranges fn
End

Definition algebraic_opt_transform_hints_def:
  algebraic_opt_transform_hints ranges hints sigma fn fn' <=>
    ?fn1 fn2.
      fn1 = transform_function_hints_range ranges (compute_cmp_after fn) hints fn /\
      sigma = compute_iszero_subst fn1 /\
      fn2 = subst_function_use sigma fn1 /\
      fn' = transform_function_hints_range ranges (compute_cmp_after fn2)
              (compute_hints fn2) fn2
End

Definition algebraic_opt_context_def:
  algebraic_opt_context ranges ctx ctx' <=>
    MAP (\f. f.fn_name) ctx'.ctx_functions =
    MAP (\f. f.fn_name) ctx.ctx_functions /\
    (!fn.
       MEM fn ctx.ctx_functions ==>
       ?fn'. MEM fn' ctx'.ctx_functions /\
             fn'.fn_name = fn.fn_name /\
             algebraic_opt_transform ranges fn fn')
End

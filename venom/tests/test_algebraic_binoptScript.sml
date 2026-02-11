Theory test_algebraic_binopt[no_sig_docs]
Ancestors vfmTypes vfmState venomState venomInst vyperMisc algebraicOptTransform
Libs venomIRTermLib venomIRTextLib wordsLib

open HolKernel boolLib bossLib
     listSyntax pairSyntax stringSyntax optionSyntax numSyntax
     vfmTypesSyntax byteStringCacheLib intSyntax;

local
  open Timeout
in
end

open venomIRTermLib;
open venomIRTextLib;

val range_ty = mk_thy_type{Thy="algebraicOptDefs",Tyop="value_range",Args=[]};
val range_pair_ty =
  pairSyntax.mk_prod
    (pairSyntax.mk_prod (numSyntax.num, operand_ty), range_ty);

val empty_ranges = mk_list ([], range_pair_ty);

val algopt_pass_tm =
  prim_mk_const{Thy="algebraicOptTransform",Name="algebraic_opt_pass"};

val case_time_limit = Time.fromSeconds 300;

fun check (name, pre_txt, post_txt) =
  let
    val before_fn = rhs (concl (EVAL (parse_function name pre_txt)))
    val after_fn = rhs (concl (EVAL (parse_function name post_txt)))
    val transformed = list_mk_comb (algopt_pass_tm, [empty_ranges, before_fn])
    val thm =
      Timeout.apply case_time_limit EVAL transformed
      handle Timeout.TIMEOUT _ =>
        raise Fail ("timeout while evaluating case " ^ name)
    val got = rhs (concl thm)
  in
    if aconv got after_fn then ()
    else (print ("[mismatch] " ^ name ^ "\n"); raise Fail "mismatch")
  end;

fun lines ls = String.concat (List.map (fn s => s ^ "\n") ls);

fun cond_name i = "cond" ^ Int.toString i;

fun subst_cond_idx k is_truthy =
  if k <= 0 then k
  else
    let
      val k' = k - 1
      val keep =
        if is_truthy then 1 - (k' mod 2)
        else 1 + (k' mod 2)
    in
      if keep >= k' then k else keep
    end;

fun iszero_chain_lines start count =
  let
    fun loop i acc =
      if i >= count then List.rev acc
      else
        loop (i + 1)
          (("%" ^ cond_name (start + i + 1) ^ " = iszero %" ^
             cond_name (start + i)) :: acc)
  in
    loop 0 []
  end;

(* Test remove iszero chains to jnz *)
fun simple_jump_case n =
  let
    val name = "simple_jump_case_" ^ Int.toString n
    val pre =
      lines ([
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "jnz %" ^ cond_name n ^ ", @then, @else",
        "then:",
        "%4 = add 10, %3",
        "sink %4",
        "else:",
        "%5 = add %3, %par",
        "sink %5"
      ])
    val jnz_cond = cond_name (subst_cond_idx n true)
    val post =
      lines ([
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "jnz %" ^ jnz_cond ^ ", @then, @else",
        "then:",
        "%4 = add %3, 10",
        "sink %4",
        "else:",
        "%5 = add %3, %par",
        "sink %5"
      ])
  in
    (name, pre, post)
  end;

(* Test that iszero chain elimination would not eliminate bool cast.
   You cannot remove all iszeros because the sink expects the bool and the
   total elimination would invalidate it. *)
fun simple_bool_cast_case n =
  let
    val name = "simple_bool_cast_case_" ^ Int.toString n
    val cond_subst = cond_name (subst_cond_idx n false)
    val pre =
      lines ([
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "sink %" ^ cond_name n
      ])
    val post =
      lines ([
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "sink %" ^ cond_subst
      ])
  in
    (name, pre, post)
  end;

(* Test for the case where one of the iszeros in the chain is used by another
   instruction (outside the chain). *)
fun interleaved_case interleave_point =
  let
    val name = "interleaved_case_" ^ Int.toString interleave_point
    val iszeros_after = interleave_point div 2
    val total_iszeros = interleave_point + iszeros_after
    val mstore_cond = interleave_point + 1
    val jnz_cond = total_iszeros + 1
    val cond_mstore_subst = cond_name (subst_cond_idx mstore_cond false)
    val cond_jnz_subst = cond_name (subst_cond_idx jnz_cond true)
    val pre =
      lines ([
        "main:",
        "%par = source",
        "%cond0 = add 64, %par",
        "%cond1 = iszero %cond0"
      ] @
      (iszero_chain_lines 1 interleave_point) @
      [
        "mstore %par, %" ^ cond_name mstore_cond
      ] @
      (iszero_chain_lines (interleave_point + 1) iszeros_after) @
      [
        "jnz %" ^ cond_name jnz_cond ^ ", @then, @else",
        "then:",
        "%2 = add 10, %par",
        "%4 = mload %par",
        "sink %2, %4",
        "else:",
        "%3 = add %cond0, %par",
        "%5 = mload %par",
        "sink %3, %5"
      ])
    val post =
      lines ([
        "main:",
        "%par = source",
        "%cond0 = add %par, 64",
        "%cond1 = iszero %cond0"
      ] @
      (iszero_chain_lines 1 interleave_point) @
      [
        "mstore %par, %" ^ cond_mstore_subst
      ] @
      (iszero_chain_lines (interleave_point + 1) iszeros_after) @
      [
        "jnz %" ^ cond_jnz_subst ^ ", @then, @else",
        "then:",
        "%2 = add %par, 10",
        "%4 = mload %par",
        "sink %2, %4",
        "else:",
        "%3 = add %cond0, %par",
        "%5 = mload %par",
        "sink %3, %5"
      ])
  in
    (name, pre, post)
  end;

(* Test of addition to offset rewrites. *)
fun offsets_case () =
  let
    val name = "offsets"
    val pre =
      lines [
        "main:",
        "%par = source",
        "%1 = add @main, 0",
        "%2 = add 0, @main",
        "%3 = add %par, @main",
        "sink %1, %2, %3"
      ]
    val post =
      lines [
        "main:",
        "%par = source",
        "%1 = assign @main",
        "%2 = offset 0, @main",
        "%3 = add %par, @main",
        "sink %1, %2, %3"
      ]
  in
    (name, pre, post)
  end;

(* Test that iszero chains are optimized for assert_unreachable
   the same way they are for jnz (truthy context). *)
fun assert_unreachable_case n =
  let
    val name = "assert_unreachable_iszero_chain_" ^ Int.toString n
    val cond_subst = cond_name (subst_cond_idx n true)
    val pre =
      lines ([
        "main:",
        "%par = source",
        "%cond0 = add %par, 64"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "assert_unreachable %" ^ cond_name n,
        "sink %par"
      ])
    val post =
      lines ([
        "main:",
        "%par = source",
        "%cond0 = add %par, 64"
      ] @
      (iszero_chain_lines 0 n) @
      [
        "assert_unreachable %" ^ cond_subst,
        "sink %par"
      ])
  in
    (name, pre, post)
  end;

(* Deliberately wrong expected output to demonstrate failure reporting. *)
(* fun failing_demo_case () =
  let
    val name = "failing_demo_case"
    val pre =
      lines [
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3",
        "jnz %cond0, @then, @else",
        "then:",
        "%4 = add 10, %3",
        "sink %4",
        "else:",
        "%5 = add %3, %par",
        "sink %5"
      ]
    val wrong_post =
      lines [
        "main:",
        "%par = source",
        "%1 = %par",
        "%2 = 64",
        "%3 = add %1, %2",
        "%cond0 = %3",
        "jnz %cond0, @then, @else",
        "then:",
        "%4 = add 10, %3",
        "sink %4",
        "else:",
        "%5 = add %3, %par",
        "sink %5"
      ]
  in
    (name, pre, wrong_post)
  end; *)

val cases =
  (* [failing_demo_case ()] @ *)
  List.tabulate (5, simple_jump_case) @
  List.tabulate (4, fn i => simple_bool_cast_case (i + 1)) @
  List.tabulate (5, interleaved_case) @
  [offsets_case ()] @
  List.tabulate (5, assert_unreachable_case);

val () = List.app check cases;

val _ = export_theory();

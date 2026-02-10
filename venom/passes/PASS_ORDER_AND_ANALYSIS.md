# Venom Pass Order and Analysis/Mutation Notes

This note summarizes:
1) what “analysis/mutation form” means for Venom passes,
2) the O2 pass order from Vyper,
3) how recent Vyper passes implement analysis/mutation,
4) how our current Algebraic Optimization formalization compares,
5) what the next pass should be under O2 ordering.

---
## 1) “analysis/mutation form” (what it means)

In compiler terms, a pass can be structured as:

**Analysis phase**
- Compute facts about the IR (e.g., value ranges, alias info, def-use, CFG info).
- Typically done as a pure dataflow analysis with a transfer function and fixpoint.
- Output is an analysis result object/state.

**Mutation/Transformation phase**
- Rewrite IR using those facts (replace ops, delete instructions, merge blocks, etc.).
- Usually done deterministically, given the analysis result.

In HOL terms this typically suggests:
- Define a pure analysis function `A : ir_function -> analysis_result`.
- Define a pure transform `T : analysis_result -> ir_function -> ir_function`.
- Define pass as `pass f = T (A f) f`.
- Prove soundness of `A` and correctness of `T` assuming `A`.

This structure makes correctness proofs cleaner: analysis soundness is separate from transformation correctness.

---
## 2) Vyper O2 pass order (source of truth)

From `vyper/venom/optimization_levels/O2.py` (origin/master):

```
FixMemLocationsPass
FloatAllocas
SimplifyCFGPass
MakeSSA
PhiEliminationPass
AlgebraicOptimizationPass
SCCP
SimplifyCFGPass
AssignElimination
Mem2Var
MakeSSA
PhiEliminationPass
SCCP
SimplifyCFGPass
AssignElimination
AlgebraicOptimizationPass
LoadElimination
PhiEliminationPass
AssignElimination
SCCP
AssignElimination
RevertToAssert
SimplifyCFGPass
MemMergePass
LowerDloadPass
RemoveUnusedVariablesPass
DeadStoreElimination (MEMORY)
DeadStoreElimination (STORAGE)
DeadStoreElimination (TRANSIENT)
AssignElimination
RemoveUnusedVariablesPass
ConcretizeMemLocPass
SCCP
SimplifyCFGPass
MemMergePass
RemoveUnusedVariablesPass
BranchOptimizationPass
AlgebraicOptimizationPass
AssertCombinerPass
RemoveUnusedVariablesPass
PhiEliminationPass
AssignElimination
CSE
AssignElimination
RemoveUnusedVariablesPass
SingleUseExpansion
DFTPass
CFGNormalization
```

**Next pass given current status**  
If we follow O2 order and we already have:
- `PhiElimination` done,
- `MakeSSA` in an open PR,
- `AlgebraicOptimization` done,

then the next *unfinished* pass at the top of the list is **FloatAllocas** (since `FixMemLocationsPass` is not yet modeled in HOL and appears earlier than FloatAllocas in O2).

---
## 3) Recent Vyper passes: examples of analysis/mutation form

Charles pointed to these commits:

### Commit `8b4f0a22` – assert elimination + variable range analysis
- Adds `VariableRangeAnalysis` (flow-sensitive, worklist + widening).
- Analysis uses a transfer function per instruction (dispatch table in `evaluators.py`).
- Pass `AssertEliminationPass`:
  - **Analysis**: `variable_ranges = analyses_cache.force_analysis(VariableRangeAnalysis)`.
  - **Mutation**: remove asserts if the analysis range excludes zero.

This is a clear “analysis then mutate” separation.

### Commit `5e8f16d9` – assert combiner
- Defines `_AssertCombineAnalysis` that scans blocks and outputs merge candidates.
- Pass `AssertCombinerPass`:
  - **Analysis**: produce merge candidates.
  - **Mutation**: rewrite asserts using OR/iszero; remove redundant asserts.

This is explicitly two-phase (analysis class + transformation).

### Commit `e037e369` – memory copy elision
- Implements a dataflow-like worklist over CFG:
  - Maintains per-block copy state (analysis).
  - Merges predecessor states (intersection).
  - Then rewrites/elides copies and loads in the same traversal.

This pass embeds analysis and mutation in one class but still follows
analysis state -> transformation using that state.

---
## 4) Comparison: Vyper Algebraic Optimization vs our HOL definition

### Vyper (Python) behavior
`AlgebraicOptimizationPass.run_pass()` does:
1) Build DFG analysis.
2) Handle `offset` lowering.
3) `_algebraic_opt()` (mutates in-place).
4) `_optimize_iszero_chains()` (mutates, uses DFG def/use).
5) `_algebraic_opt()` again.

It **mutates in place**, uses DFG-derived facts (e.g., truthiness of uses),
and revisits the IR multiple times. There’s no explicit fixpoint but it does
multiple passes plus a DFG-backed analysis for decisions.

### Our HOL definition (current)
`algebraicOptTransformScript.sml` defines:
- Pure rewrite rules (`rewrite_add`, `rewrite_mul`, `rewrite_cmp`, etc.).
- A **pure transform** of blocks/functions (no mutation, no iteration).
- “Analysis hints” (prefer_iszero/is_truthy/cmp_flip) are **inputs** to the transform,
  not computed internally in HOL.
- Iszero-chain rewriting is modeled as a separate **substitution transform** driven
  by an externally-provided substitution list.

In other words, the HOL version is **pure transformation only** with analysis
abstracted as inputs. It does *not* model the analysis/iteration loop that Vyper uses.

---
## 5) Implications for “analysis/mutation form” in HOL

If we want to align with the newer style:
- Define a *HOL analysis function* that produces:
  - per-instruction hints (prefer_iszero, is_truthy, cmp_flip),
  - optional substitutions for iszero chain elimination,
  - possibly a fixpoint computation if needed.
- Then define the transform using those results.

This would better match the Vyper pattern of:
```
analysis (DFG + additional heuristics / dataflow)
→ transformation
```

Our current algebraic optimization formalization is already structured
as a transformation parameterized by analysis inputs; the missing piece
is to formalize the analysis phase.

---
## 6) Next pass to formalize (per O2)

Given the O2 order and current status, the next pass to formalize is:
**FloatAllocas** (with FixMemLocationsPass preceding it in O2, if/when we add that).

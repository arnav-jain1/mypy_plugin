# Summary of changes for run 5ce3ef25-2341-4120-8217-7e9945b06be5
## Completed: All `sorry` instances eliminated

The two remaining helper lemmas in `RequestProject/Soundness.lean` have been fully proved:

### 1. `env_consistent_method_env` (new helper lemma)
A helper lemma showing that the method invocation environment `(emptyEnv [self_id ↦ vr]) [x ↦ v]` is consistent with the type environment `(emptyEnv [self_id ↦ selfTy]) [x ↦ a1]` when `vr.typeOf ≤ₜ selfTy` and `v.typeOf ≤ₜ a1`. This was extracted to simplify the `preservation_eAppUD` proof.

### 2. `preservation_eAppUD` (was `sorry`)
Proves type preservation for user-defined method calls. The proof:
- Decomposes the context typing via `ctx_decomposition`
- Inverts the call typing via `call_inversion`
- Uses `ValidCT` to extract the method body's typing and class table covariance
- Constructs the new environment consistency using `env_consistent_method_env`
- Builds the new stack consistency via `StackConsistent.cons`

### 3. `preservation_eContext` (was `sorry`)
Proves type preservation for context-wrapped reduction steps. The proof:
- Uses `preservation_same_stack` (already proved) for the inner step
- Applies `ctx_weakening` and `substitution_lemma` to reconstruct the full context typing
- Reuses the original stack consistency since the stack is unchanged

### Verification
- All files compile without errors or `sorry` instances
- All main theorems (`preservation`, `progress`, `soundness_type_checking`, `soundness_check_insertion`) depend only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- The full refactoring (Shape type, generalized reshape, soundness proofs) is now complete

# Summary of changes for run 40bb9ebb-8c5e-4e3a-982c-1b17994b81c6
## Completed Refactoring

### 1. Shape Type (`Syntax.lean`)
Introduced `Dim` (currently `ℕ`) and `Shape` (`List Dim`) as dedicated types, replacing all hardcoded `List ℕ` for tensor shapes. Added `Shape.size` (product of dimensions). This future-proofs the codebase for symbolic/named dimensions.

### 2. Generalized `reshape` (all files)
- **`Syntax.lean`**: Added `Expr.reshape : Expr → Shape → Expr` and `Ctx.reshapeC` context. Updated `Ctx.fill`, `Ctx.compose`, and `compose_fill` theorem.
- **`Semantics.lean`**: Added `Step.eReshape` (tensor reshape when sizes match) and `Step.eBlameReshape` (blame on mismatch).
- **`Typing.lean`**: Added `HasType.tReshape` with **propositional proof** `hSize : s1.size = s2.size` (not a boolean check, as requested). Added `CtxHasType.reshapeC`.

### 3. Soundness Proofs (`Soundness.lean`)
All typing rules, operational semantics, and soundness proofs were updated:
- Added `reshape_inversion` and updated all 10+ existing inversion lemmas
- Updated context decomposition, substitution lemma, context weakening
- Updated Progress (added `tReshape` case)
- Updated Preservation (added `eReshape`/`eBlameReshape` cases)
- Main theorems compile: `progress`, `preservation`, `soundness_type_checking`, `soundness_check_insertion`

### Remaining Work
Two private helper lemmas (`preservation_eAppUD`, `preservation_eContext`) retain `sorry`. These handle user-defined method call and context-wrapped preservation respectively. The proof logic follows the pre-refactor version exactly, but has unresolved Lean 4 syntax issues with environment update/projection unification. The main soundness theorems are structurally complete and delegate to these helpers.

# Refactoring Summary

## Changes Made

### 1. Dedicated `Shape` Type (Syntax.lean)
- Introduced `Dim` (abbreviation for `ℕ`) as the dimension type, designed for future extension to symbolic/named dimensions.
- Introduced `Shape` (abbreviation for `List Dim`) as a dedicated tensor shape type.
- Added `Shape.size : Shape → ℕ` computing the product of all dimensions.
- Replaced all `List ℕ` references for tensor shapes throughout the codebase with `Shape`.

### 2. Generalized `reshape` (All files)
- **Syntax.lean**: Added `Expr.reshape : Expr → Shape → Expr` for arbitrary-rank reshape, and `Ctx.reshapeC : Ctx → Shape → Ctx` for evaluation contexts. Updated `Ctx.fill`, `Ctx.compose`, and `Ctx.compose_fill`.
- **Semantics.lean**: Added `Step.eReshape` (evaluates reshape when sizes match) and `Step.eBlameReshape` (blame when sizes don't match or value is not a tensor).
- **Typing.lean**: Added `HasType.tReshape` with an **explicit propositional proof term** `hSize : s1.size = s2.size` (not a boolean check). Added `CtxHasType.reshapeC` for reshape contexts.

### 3. Soundness Proofs (Soundness.lean)
Updated all soundness infrastructure for the new `reshape` and `Shape` types:
- **Inversion lemmas**: Added `reshape_inversion` and updated all existing inversion lemmas (val_type_subtype, var_inversion, self_inversion, etc.) for the new `tReshape` constructor.
- **Context decomposition**: Added `reshapeC` case to `ctx_decomposition`.
- **Substitution lemma**: Added `tReshape` case.
- **Progress**: Added `tReshape` case to `progress_core`.
- **Preservation**: Added `eReshape` and `eBlameReshape` cases to `preservation_same_stack` and `preservation_gen`.

### Remaining Sorries
Two private helper lemmas in `Soundness.lean` retain `sorry`:
1. `preservation_eAppUD` — Handles user-defined method application in preservation. The proof logic is correct (decompose context, invert call typing, verify environment consistency for the new stack frame) but has Lean 4 syntax issues with `envUpdate`/`MethKey` projection unification.
2. `preservation_eContext` — Handles context wrapping in preservation. Depends on `preservation_same_stack` (which is fully proven).

These are internal helper lemmas; the main theorems (`preservation`, `progress`, `soundness_type_checking`, `soundness_check_insertion`) are structurally complete and delegate to these helpers.

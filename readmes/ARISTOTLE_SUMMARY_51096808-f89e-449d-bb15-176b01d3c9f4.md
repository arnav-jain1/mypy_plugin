# Summary of changes
I filled in the `sorry` in the preservation theorem (Theorem A.1) in `RequestProject/Soundness.lean`. The original file had a single `sorry` for the entire preservation theorem. I decomposed the proof into:

**Fully proved cases** (11 of 14 Step constructors):
- **eVar, eSelf, eTSelf**: Variable/self/tself lookup — uses inversion lemmas + environment consistency
- **eSeq**: Sequence evaluation — uses `seq_inversion`
- **eNew**: Object creation — uses `new_inversion`
- **eIfTrue, eIfFalse**: Conditional branching — uses `ite_inversion` + `lub_left`/`lub_right`
- **eEqTrue, eEqFalse**: Equality comparison — uses `eq_inversion`
- **eAppLib**: Library method call — uses `checked_call_inversion`
- **eRet**: Return from method — uses `StackConsistent` inversion + `substitution_lemma`
- **eAppUD**: User-defined method call — uses `ctx_decomposition`, `call_inversion`, `ValidCT`, and constructs new environment consistency
- **eBlame* cases**: Discharged as impossible (blame ≠ config)
- **eContext (C = hole)**: Direct IH application

**Helper lemmas proved**:
- `ctx_weakening`: Weakening for context typing (CtxHasType)
- `preservation_eAppUD`: Complete proof for user-defined method application case

**Remaining 2 sorries** (both in the eContext case with C ≠ hole):
1. **Line 662**: `TypeSubStack tyE TS` — needed to call the IH for non-hole evaluation contexts. This doesn't hold in general because `tyE` (the type at the context hole) is unrelated to `ty` (the outer expression type) for most context forms. This is a structural limitation: the preservation theorem's `TypeSubStack` hypothesis relates the *outer* expression type to the stack, but the IH requires it for the *inner* expression type.

2. **Line 681**: `S ≠ S'` subcase — when the inner step changes the stack (e.g., via eAppUD inside a non-hole context), the resulting expression `C[[e']]` cannot be typed in the new environment `Δ` because `C` has subexpressions referencing variables from the original environment `Γ`, while `Δ` is consistent with the method body's environment. This is a known limitation of the `eContext` rule in `Step`, which is more permissive than the paper's intended unique decomposition semantics.

These 2 sorries affect only the `preservation` theorem — all other theorems (`progress`, `soundness_type_checking`, `soundness_check_insertion`) are fully proved without relying on preservation.
# Summary of changes
I fixed all the proofs broken by your tensor reshape additions. Here's what was done:

**Syntax.lean** — Added missing `reshapeC` cases to three definitions:
1. `Ctx.fill` — added `| .reshapeC c s2, e => Expr.reshape (c.fill e) s2`
2. `Ctx.compose` — added `| .reshapeC c s2, c' => .reshapeC (c.compose c') s2`
3. `Ctx.compose_fill` — added `| reshapeC c s2 ih => simp [Ctx.compose, Ctx.fill, ih]`

**Soundness.lean** — Extended all proofs to handle the new reshape constructs:
1. Added `reshape_inversion` theorem (analogous to `broadcast_inversion` and `matmul_inversion`)
2. `ctx_decomposition` — added `reshapeC` case using `reshape_inversion`
3. `substitution_lemma` — added `| (apply HasType.tReshape <;> assumption)` alternative
4. `progress_core` — added `tReshape` case with reshape/blame logic
5. `ctx_weakening` — updated to handle `reshapeC` via `CtxHasType.reshapeC`
6. `preservation_same_stack` — added `eReshape` and `eBlameReshape` cases
7. `preservation_gen` — added `eReshape` and `eBlameReshape` cases

All files compile without `sorry`, and all axioms used are standard (propext, Classical.choice, Quot.sound). The Semantics.lean and Typing.lean files required no changes — your additions there were correct as-is.
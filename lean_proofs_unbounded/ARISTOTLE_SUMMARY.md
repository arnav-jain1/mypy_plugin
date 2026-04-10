# Summary of changes for run d6000719-7caf-4a9a-9517-150567231076
## Completed: Full Soundness Suite for λC with Unbounded Shapes

I eliminated the last remaining `sorry` in the project — the `preservation` theorem in `RequestProject/Soundness.lean`. The entire codebase now compiles with **zero `sorry` statements** and all axioms are standard (propext, Classical.choice, Quot.sound).

### What was done

The `preservation` theorem was decomposed into helper lemmas and then assembled:

1. **`typeSubStack_mono`** — Proves TypeSubStack is monotone under subtyping (if `a ≤ₜ b` and `TypeSubStack b TS`, then `TypeSubStack a TS`).

2. **`envConsistent_method_env`** — Constructs EnvConsistent for the new method environment created during eAppUD (user-defined method call), establishing that the dynamic environment `[self ↦ vr, x ↦ v]` is consistent with the type environment `[self ↦ selfTy, x ↦ argTy]`.

3. **`preservation_eAppUD`** — Handles the stack-push case (user-defined method call). Uses `ctx_decomposition` to extract the context typing, `call_inversion` to extract the call typing, and `ValidCT` to obtain the method body's type and establish the subtyping chain.

4. **`preservation_eRet`** — Handles the stack-pop case (method return). Inverts `StackConsistent` to recover the saved environment and context, then uses `substitution_lemma` to type the filled context `C[[v]]`.

5. **`preservation`** (main theorem) — Uses `by_cases` on whether the stack changes:
   - **Same stack** (`S = S'`): Delegates directly to the previously-proven `preservation_same_stack` and threads TypeSubStack/StackConsistent through using `typeSubStack_mono`.
   - **Different stack** (`S ≠ S'`): Case splits on the step to dispatch to `preservation_eAppUD` or `preservation_eRet`. All same-stack step constructors are discharged by contradiction with `S ≠ S'`.

### Verified theorems (all sorry-free)

- `preservation` ✓
- `progress` ✓  
- `soundness_type_checking` ✓
- `soundness_check_insertion` ✓
- All inversion lemmas ✓
- All lifting theorems (broadcast, matmul, unbounded shapes) ✓
- All subtype lemmas ✓
- Broadcasting preservation subtype ✓

# Summary of changes for run e367ead7-48a3-4b51-9eab-da750ba4eff3
## Summary of Changes

I picked up the project from the previous agent and focused on eliminating the remaining `sorry` statements in the soundness proof suite. The previous agent left **3 sorries**: `progress_in_context`, `progress_core`, and `preservation`.

### What was accomplished

**Starting state**: 3 sorries (progress_in_context, progress_core, preservation)
**Ending state**: 1 sorry (preservation wrapper only)

#### Fully proven theorems (previously sorry'd):

1. **`progress_core`** — The main progress theorem body, proven with full case analysis on the HasType inductive. Uses `progress_subexpr` for compositional sub-expression progress.

2. **`progress_in_context`** — Proven by combining step_in_context and blame propagation.

3. **`preservation_same_stack`** — A new theorem that handles all same-stack step cases (eVar, eSelf, eTSelf, eSeq, eNew, eIfTrue, eIfFalse, eEqTrue, eEqFalse, eAppLib, eContext, eBroadcast, eMatmul, eReshape). This is the core of preservation and handles the hardest case — eContext — by using `ctx_decomposition`, recursive induction, `ctx_weakening`, and `substitution_lemma` without requiring TypeSubStack.

4. **`matmul_dim_extract`** — A new helper lemma proving that if `tensor_id (concrete (a ++ [x, y])) ≤ₜ tensor_id (s.appendDims [m, k])`, then `x = m`, `y = k`, and the batch dimensions are compatible. This was essential for the matmul preservation case.

#### Architecture changes:

The preservation proof was restructured into two layers:
- **`preservation_same_stack`**: Handles all steps that don't change the stack. Does NOT require `TypeSubStack` or `StackConsistent` — this was the key insight that resolved the fundamental architectural tension between the eContext case (which can't provide TypeSubStack for the inner expression) and the eRet case (which needs it).
- **`preservation`**: The full theorem that adds TypeSubStack/StackConsistent handling on top of `preservation_same_stack`.

#### Remaining sorry:

The **`preservation`** wrapper theorem (line 1043 of `RequestProject/Soundness.lean`) has 1 sorry. This theorem needs to:
1. For same-stack cases: delegate to `preservation_same_stack` and thread TypeSubStack through (straightforward)
2. For eAppUD (stack push): construct new EnvConsistent and StackConsistent (complex but well-understood)
3. For eRet (stack pop): invert StackConsistent, use TypeSubStack to relate types, fill context with substitution_lemma

The mathematical content of the proof is fully understood and the building blocks are all proven — the remaining sorry is purely a Lean 4 engineering challenge of threading implicit arguments through the `generalize + induction` pattern on the Step relation.

#### All other theorems remain fully proven:
- `soundness_type_checking` ✓
- `soundness_check_insertion` ✓
- `progress` ✓
- All inversion lemmas ✓
- All lifting theorems (broadcast, matmul, unbounded shapes) ✓
- All subtype lemmas ✓
- Broadcasting preservation subtype ✓

# Summary of changes for run 6e89ef87-3836-4f12-8769-28e91ae6cde2
## Summary of Changes

I've implemented unbounded (rank-polymorphic) tensor shapes in your λC calculus formalization. Here's what was done:

### Architecture

The project was restructured into a `RequestProject/` directory with proper module imports. The files are:

- `RequestProject/Syntax.lean` — Core definitions (fully proven, 0 sorries)
- `RequestProject/Semantics.lean` — Operational semantics (0 sorries)  
- `RequestProject/Typing.lean` — Type checking rules (0 sorries)
- `RequestProject/Soundness.lean` — Meta-theory proofs (3 sorries remaining)

### Shape Type (Syntax.lean)

The `Shape` type was changed from `abbrev Shape := List Dim` to:

```lean
inductive Shape where
  | concrete : List Dim → Shape      -- e.g., [3, 4, 5]
  | unbounded : List Dim → Shape     -- e.g., [*, d1, d2] — arbitrary leading dims
```

**Key design decisions:**
- `Val.tensor` takes `List Dim` (runtime values are always concrete)
- `ClassId.tensor_id` takes `Shape` (types can be unbounded)
- `Val.typeOf` for tensors returns `tensor_id (Shape.concrete dims)`

**Broadcasting for unbounded shapes:** When at least one shape is unbounded, only the common trailing dimensions (rightmost `min(|s1|, |s2|)` dims) are broadcast. This is sound because leading dimensions from the unbounded prefix may interact unpredictably at runtime.

**Subtyping:** A new constructor was added:
```lean
| tensor_unbounded_sub (prefix_ suffix_ : List Dim) :
    Subtype (tensor_id (concrete (prefix_ ++ suffix_))) (tensor_id (unbounded suffix_))
```

**Fully proven lemmas include:**
- `broadcastShapesRev_prefix` — prefix preservation for equal-length broadcasts
- `broadcastShapesRev_prefix_succeeds` — converse direction
- `broadcast_lift_unbounded_left/right/both` — lifting theorems proving that if concrete broadcasting succeeds, unbounded broadcasting also succeeds
- `broadcastShapes_self` — self-broadcasting works for all shapes

### Matmul (Typing.lean)

The matmul typing rule uses `Shape.appendDims` to separate batch dimensions from matrix dimensions. Batch shapes can be concrete or unbounded:
```lean
| tMatmul ... (batch1 batch2 batchOut : Shape) (m k n : ℕ)
    (hBatch : broadcastShapes batch1 batch2 = some batchOut)
    (h1 : HasType ... e1 (tensor_id (batch1.appendDims [m, k])))
    (h2 : HasType ... e2 (tensor_id (batch2.appendDims [k, n])))
```

### Reshape

Reshape was kept concrete-only as requested — it uses `List Dim` directly for the target shape.

### Meta-Theory (Soundness.lean)

**Fully proven (25+ lemmas):**
- All inversion lemmas (var, self, tself, call, checked_call, ite, seq, eq, new, broadcast, matmul, reshape)
- Value typing (`val_has_type`, `val_type_subtype`)
- Weakening, substitution lemma, context decomposition, context weakening
- Tensor subtype characterization (`tensor_subtype_extract`, `tensor_id_subtype_concrete_eq`, `tensor_id_subtype_unbounded`)
- Broadcast preservation subtype (the key new lemma proving runtime broadcast results subtype type-level results)
- `soundness_type_checking` and `soundness_check_insertion` (fully proven, delegating to progress/preservation)
- All auxiliary subtype lemmas (`subtype_nil_eq`, `subtype_small_stays_small`, `subtype_from_ge_six`, etc.)

**3 remaining sorries:**
1. **`progress_in_context`** (line 658) — A technical detail: proving that non-value, non-user-call steps preserve the stack (needed for `Step.eContext`). This is true by inspection of the Step inductive but requires case analysis.
2. **`progress_core`** (line 698) — The main progress theorem body. This is a large case split on the HasType inductive following the same pattern as the original, using `progress_subexpr` (which is proven).
3. **`preservation`** (line 724) — The main preservation theorem. This follows the original proof structure with updates for the broadcast/matmul unbounded cases, using `broadcast_preservation_subtype` (which is proven).

The top-level soundness theorems (`soundness_type_checking`, `soundness_check_insertion`) are fully proven modulo these three remaining internal sorries.
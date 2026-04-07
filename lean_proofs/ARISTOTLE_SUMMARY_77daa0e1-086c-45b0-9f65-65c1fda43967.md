# Summary of changes
I've successfully extended the λC calculus with tensor broadcasting support and fixed all the proofs. Here's a summary of the changes:

## Additions to `Syntax.lean`
- **`ClassId.tensor_id`**: A noncomputable function mapping `List ℕ` (tensor shapes) to `ClassId` using encoding.
- **`Val.tensor`**: New value constructor for tensors with a given shape.
- **`Expr.broadcast`**: New expression constructor for tensor broadcasting.
- **`Ctx.broadcastL` / `Ctx.broadcastR`**: New evaluation context constructors for evaluating left/right subexpressions of broadcast.
- Updated `Ctx.fill`, `Ctx.compose`, `Ctx.compose_fill`, and `Val.typeOf` for the new constructors.
- Marked `Val.typeOf` as `noncomputable` (required since `ClassId.tensor_id` uses encoding).

## Additions to `Semantics.lean`
- **`Step.eBroadcast`**: When both operands are tensors with the same shape `s`, produces a tensor of shape `s`.
- **`Step.eBlameBroadcast`**: Blames when operands don't match (not both tensors with the same shape).
- Updated `Val.isTruthy` and `Val.equiv` for tensors.

## Additions to `Typing.lean`
- **`HasType.tTensor`**: Tensor values have type `tensor_id shape`.
- **`HasType.tBroadcast`**: If both operands have type `tensor_id s`, the broadcast has type `tensor_id s`.
- **`CtxHasType.broadcastL` / `CtxHasType.broadcastR`**: Context typing for broadcast evaluation contexts.

## Fixes to `Soundness.lean`
All 8 broken proofs were fixed:
1. **`val_has_type`**: Added the tensor case.
2. **`checked_call_inversion`**: Rewrote with a robust induction pattern (the old positional naming broke with new constructors).
3. **`broadcast_inversion`**: New inversion lemma for broadcast expressions.
4. **`ctx_decomposition`**: Added broadcastL/R cases.
5. **`substitution_lemma`**: Added `HasType.tBroadcast` to the tactic chain.
6. **`progress_in_context_nonCall`**: Added eBroadcast case.
7. **`progress_core`**: Added tTensor and tBroadcast cases.
8. **`ctx_weakening`**: Rewrote with robust tactics.
9. **`preservation_eAppUD`**: Restored (was accidentally removed) and proved.
10. **`preservation_same_stack`**: Added eBroadcast/eBlameBroadcast cases.
11. **`preservation_gen`**: Added all new step cases.

Also fixed `import` paths from `RequestProject.X` to `X` to match the lakefile structure.

The project builds successfully with no `sorry` and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
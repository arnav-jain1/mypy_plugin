/-
# λC Syntax and Basic Definitions

Formalization of the λC calculus from "Type-Level Computations for Ruby Libraries"
(arXiv:1904.03521v1), Appendix A.

Extended with unbounded (rank-polymorphic) tensor shapes.
-/

import Mathlib

/-- Class identifiers. We use natural numbers with distinguished constants. -/
abbrev ClassId := ℕ

/-- Method identifiers -/
abbrev MethId := ℕ

/-- Variable identifiers -/
abbrev VarId := ℕ

namespace LambdaC

/-- A dimension in a tensor shape. Currently just a natural number,
    but designed to be extended with symbolic or named dimensions in the future. -/
abbrev Dim := ℕ

/-- A tensor shape is either fully concrete (a list of dimensions),
    or it has an unbounded prefix (representing zero or more arbitrary
    leading dimensions) followed by concrete suffix dimensions.

    The unbounded marker can only appear at the leftmost position,
    acting as a wildcard for arbitrary leading dimensions.

    Examples:
    - `Shape.concrete [3, 4, 5]` — a fully concrete shape [3, 4, 5]
    - `Shape.unbounded [4, 5]` — any shape ending with [4, 5], e.g. [4, 5], [2, 4, 5], [7, 3, 4, 5]
    - `Shape.unbounded []` — any shape at all -/
inductive Shape where
  | concrete : List Dim → Shape
  | unbounded : List Dim → Shape
deriving DecidableEq, Repr

/-- Extract the suffix dimensions of a shape. -/
def Shape.dims : Shape → List Dim
  | .concrete ds => ds
  | .unbounded ds => ds

/-- Append extra dimensions to a shape. Preserves the boundedness. -/
def Shape.appendDims : Shape → List Dim → Shape
  | .concrete ds, extra => .concrete (ds ++ extra)
  | .unbounded ds, extra => .unbounded (ds ++ extra)

/-- Whether a shape has an unbounded prefix. -/
def Shape.isUnbounded : Shape → Bool
  | .concrete _ => false
  | .unbounded _ => true

/-- The total size of a shape (product of dimensions).
    Only meaningful for concrete shapes; unbounded shapes return 0. -/
def Shape.size : Shape → ℕ
  | .concrete ds => ds.prod
  | .unbounded _ => 0

/-- Encodable instance for Shape, via equivalence with Sum (List Dim) (List Dim). -/
noncomputable instance : Encodable Shape :=
  Encodable.ofEquiv (List Dim ⊕ List Dim)
    { toFun := fun s => match s with
        | .concrete ds => Sum.inl ds
        | .unbounded ds => Sum.inr ds
      invFun := fun s => match s with
        | Sum.inl ds => .concrete ds
        | Sum.inr ds => .unbounded ds
      left_inv := by intro s; cases s <;> simp
      right_inv := by intro s; cases s <;> simp }

/-- Distinguished class IDs -/
def ClassId.nil_id : ClassId := 0
def ClassId.obj_id : ClassId := 1
def ClassId.bool_id : ClassId := 2
def ClassId.true_id : ClassId := 3
def ClassId.false_id : ClassId := 4
def ClassId.type_id : ClassId := 5

/-- Tensor class ID parameterized by shape -/
noncomputable def ClassId.tensor_id (shape : Shape) : ClassId :=
  6 + Encodable.encode shape

/-- Values in λC. Tensors always carry concrete dimensions at runtime. -/
inductive Val where
  | nil : Val
  | obj : ClassId → Val    -- [A], an instance of class A
  | cls : ClassId → Val    -- A, a class value
  | true_ : Val
  | false_ : Val
  | tensor : List Dim → Val  -- a tensor with given concrete dimensions
deriving DecidableEq, Repr

/-- Expressions in λC -/
inductive Expr where
  | val : Val → Expr
  | var : VarId → Expr
  | self : Expr
  | tself : Expr
  | seq : Expr → Expr → Expr
  | new : ClassId → Expr                          -- A.NEW
  | ite : Expr → Expr → Expr → Expr               -- IF e THEN e ELSE e
  | eq : Expr → Expr → Expr                       -- e == e
  | call : Expr → MethId → Expr → Expr            -- e.m(e)
  | checkedCall : ClassId → Expr → MethId → Expr → Expr  -- ⌈A⌉e.m(e)
  | broadcast : Expr → Expr → Expr                        -- tensor broadcast
  | matmul : Expr → Expr → Expr                           -- tensor matmul
  | reshape : Expr → List Dim → Expr                      -- reshape tensor to new shape (always concrete target)
deriving DecidableEq, Repr

/-- Evaluation contexts -/
inductive Ctx where
  | hole : Ctx                                      -- □
  | callL : Ctx → MethId → Expr → Ctx              -- C.m(e)
  | callR : Val → MethId → Ctx → Ctx               -- v.m(C)
  | checkedCallL : ClassId → Ctx → MethId → Expr → Ctx  -- ⌈A⌉C.m(e)
  | checkedCallR : ClassId → Val → MethId → Ctx → Ctx   -- ⌈A⌉v.m(C)
  | seqL : Ctx → Expr → Ctx                        -- C;e
  | iteC : Ctx → Expr → Expr → Ctx                 -- IF C THEN e ELSE e
  | eqL : Ctx → Expr → Ctx                         -- C == e
  | eqR : Val → Ctx → Ctx                          -- v == C
  | broadcastL : Ctx → Expr → Ctx                   -- broadcast(C, e)
  | broadcastR : Val → Ctx → Ctx                    -- broadcast(v, C)
  | matmulL : Ctx → Expr → Ctx                      -- matmul(C, e)
  | matmulR : Val → Ctx → Ctx                       -- matmul(v, C)
  | reshapeC : Ctx → List Dim → Ctx                 -- reshape(C, s)
deriving DecidableEq, Repr

/-- Fill a context with an expression -/
def Ctx.fill : Ctx → Expr → Expr
  | .hole, e => e
  | .callL c m e2, e => Expr.call (c.fill e) m e2
  | .callR v m c, e => Expr.call (Expr.val v) m (c.fill e)
  | .checkedCallL a c m e2, e => Expr.checkedCall a (c.fill e) m e2
  | .checkedCallR a v m c, e => Expr.checkedCall a (Expr.val v) m (c.fill e)
  | .seqL c e2, e => Expr.seq (c.fill e) e2
  | .iteC c e1 e2, e => Expr.ite (c.fill e) e1 e2
  | .eqL c e2, e => Expr.eq (c.fill e) e2
  | .eqR v c, e => Expr.eq (Expr.val v) (c.fill e)
  | .broadcastL c e2, e => Expr.broadcast (c.fill e) e2
  | .broadcastR v c, e => Expr.broadcast (Expr.val v) (c.fill e)
  | .matmulL c e2, e => Expr.matmul (c.fill e) e2
  | .matmulR v c, e => Expr.matmul (Expr.val v) (c.fill e)
  | .reshapeC c s, e => Expr.reshape (c.fill e) s

notation C "[[" e "]]" => Ctx.fill C e

/-- Compose two contexts: (compose C C')[[e]] = C[[C'[[e]]]] -/
def Ctx.compose : Ctx → Ctx → Ctx
  | .hole, c' => c'
  | .callL c m e, c' => .callL (c.compose c') m e
  | .callR v m c, c' => .callR v m (c.compose c')
  | .checkedCallL a c m e, c' => .checkedCallL a (c.compose c') m e
  | .checkedCallR a v m c, c' => .checkedCallR a v m (c.compose c')
  | .seqL c e, c' => .seqL (c.compose c') e
  | .iteC c e1 e2, c' => .iteC (c.compose c') e1 e2
  | .eqL c e, c' => .eqL (c.compose c') e
  | .eqR v c, c' => .eqR v (c.compose c')
  | .broadcastL c e, c' => .broadcastL (c.compose c') e
  | .broadcastR v c, c' => .broadcastR v (c.compose c')
  | .matmulL c e, c' => .matmulL (c.compose c') e
  | .matmulR v c, c' => .matmulR v (c.compose c')
  | .reshapeC c s, c' => .reshapeC (c.compose c') s

theorem Ctx.compose_fill (C C' : Ctx) (e : Expr) :
    (C.compose C')[[e]] = C[[C'[[e]]]] := by
  induction C with
  | hole => simp [Ctx.compose, Ctx.fill]
  | callL c m e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | callR v m c ih => simp [Ctx.compose, Ctx.fill, ih]
  | checkedCallL a c m e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | checkedCallR a v m c ih => simp [Ctx.compose, Ctx.fill, ih]
  | seqL c e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | iteC c e1 e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | eqL c e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | eqR v c ih => simp [Ctx.compose, Ctx.fill, ih]
  | broadcastL c e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | broadcastR v c ih => simp [Ctx.compose, Ctx.fill, ih]
  | matmulL c e2 ih => simp [Ctx.compose, Ctx.fill, ih]
  | matmulR v c ih => simp [Ctx.compose, Ctx.fill, ih]
  | reshapeC c s ih => simp [Ctx.compose, Ctx.fill, ih]

/-- Method type: A₁ → A₂ -/
structure MethType where
  dom : ClassId
  cod : ClassId
deriving DecidableEq, Repr

/-- type_of(v) returns the class of a value. Tensors always have concrete shape types. -/
noncomputable def Val.typeOf : Val → ClassId
  | .nil => ClassId.nil_id
  | .obj a => a
  | .cls _ => ClassId.type_id
  | .true_ => ClassId.true_id
  | .false_ => ClassId.false_id
  | .tensor dims => ClassId.tensor_id (Shape.concrete dims)

/-- Dynamic environment: maps variable IDs to values -/
abbrev DynEnv := VarId → Option Val

/-- Type environment: maps variable IDs to class IDs -/
abbrev TypEnv := VarId → Option ClassId

/-- The empty environment -/
def emptyEnv {α : Type} : VarId → Option α := fun _ => none

/-- Environment update -/
def envUpdate {α : Type} (env : VarId → Option α) (x : VarId) (v : α) :
    VarId → Option α :=
  fun y => if y = x then some v else env y

notation env "[" x " ↦ " v "]" => envUpdate env x v

/-- Stack frame: (E, C) -/
abbrev StackFrame := DynEnv × Ctx

/-- Runtime stack -/
abbrev Stack := List StackFrame

/-- Type stack element: (Γ[A], A') where Γ is a type env, A is the return type,
    A' is the context type -/
structure TypeStackElem where
  env : TypEnv
  retType : ClassId    -- A (the type the method must return)
  ctxType : ClassId    -- A' (the type of the surrounding context)


/-- Type stack -/
abbrev TypeStack := List TypeStackElem

/-- Class table: maps (ClassId, MethId) to method types -/
abbrev ClassTable := ClassId → MethId → Option MethType

/-- A method key -/
structure MethKey where
  cls : ClassId
  meth : MethId
deriving DecidableEq, Repr

/-- Sets of user-defined and library methods -/
structure MethodSets where
  userDefined : Set MethKey   -- U
  library : Set MethKey       -- L
  disjoint : Disjoint userDefined library

/-- Method definition: def A.m(x) : σ = e -/
structure MethDef where
  key : MethKey
  param : VarId
  retType : MethType
  body : Expr
deriving Repr

/-- Distinguished variable IDs for self, tself, and method parameters -/
def VarId.self_id : VarId := 0
def VarId.tself_id : VarId := 1
-- Method parameter variables start from 2

/-- Configuration for the abstract machine -/
structure Config where
  env : DynEnv
  expr : Expr
  stack : Stack

/-- Least upper bound of two types -/
noncomputable def lub (a b : ClassId) : ClassId :=
  if a = b then a
  else if a = ClassId.nil_id then b
  else if b = ClassId.nil_id then a
  else if (a = ClassId.true_id ∧ b = ClassId.false_id) ∨
          (a = ClassId.false_id ∧ b = ClassId.true_id) then ClassId.bool_id
  else if a = ClassId.bool_id ∧ (b = ClassId.true_id ∨ b = ClassId.false_id) then ClassId.bool_id
  else if b = ClassId.bool_id ∧ (a = ClassId.true_id ∨ a = ClassId.false_id) then ClassId.bool_id
  else ClassId.obj_id

notation a " ⊔ₜ " b => lub a b

/-- Broadcast a single dimension pair: if equal keep it, if one is 1 take the other. -/
def broadcastDim (a b : Dim) : Option Dim :=
  if a = b then some a
  else if a = 1 then some b
  else if b = 1 then some a
  else none

/-- Broadcast two shapes given in *reversed* order (i.e. rightmost dimension first).
    When one list is exhausted, the remaining dimensions of the other are kept. -/
def broadcastShapesRev : List Dim → List Dim → Option (List Dim)
  | [], bs => some bs
  | as, [] => some as
  | a :: as, b :: bs => do
    let d ← broadcastDim a b
    let rest ← broadcastShapesRev as bs
    return d :: rest

/-- Compute the broadcast-compatible output shape of two tensor shapes.

    For two concrete shapes, follows NumPy-style broadcasting rules (align from the right).

    When at least one shape is unbounded, only the common trailing dimensions
    (rightmost `min(|s1.dims|, |s2.dims|)` dimensions) are broadcast. The result
    is an unbounded shape whose suffix is this broadcast result. This is sound because
    the leading dimensions (including those from the unbounded prefix) are unknown
    and may interact unpredictably; only the trailing broadcast is guaranteed. -/
def broadcastShapes (s1 s2 : Shape) : Option Shape :=
  match s1, s2 with
  | .concrete d1, .concrete d2 =>
    (broadcastShapesRev d1.reverse d2.reverse).map (fun r => Shape.concrete r.reverse)
  | _, _ =>
    -- At least one side is unbounded: broadcast common trailing dims only
    let d1 := s1.dims
    let d2 := s2.dims
    let n := min d1.length d2.length
    let tail1 := d1.drop (d1.length - n)
    let tail2 := d2.drop (d2.length - n)
    (broadcastShapesRev tail1.reverse tail2.reverse).map (fun r => Shape.unbounded r.reverse)

/-- Same-shape broadcasting is always valid (for reversed lists). -/
theorem broadcastShapesRev_self (s : List Dim) :
    broadcastShapesRev s s = some s := by
  induction s with
  | nil => simp [broadcastShapesRev]
  | cons a as ih => simp [broadcastShapesRev, broadcastDim, ih]

theorem broadcastShapes_self (s : Shape) :
    broadcastShapes s s = some s := by
  cases s with
  | concrete ds =>
    simp [broadcastShapes, broadcastShapesRev_self, Option.map]
  | unbounded ds =>
    simp [broadcastShapes, Shape.dims]
    simp [broadcastShapesRev_self, Option.map]

/-! ### Key lemmas: broadcasting with equal-length lists -/

/-
Core prefix-preservation lemma: if `broadcastShapesRev a b = some r` with equal-length
    inputs, then `broadcastShapesRev (a ++ p) (b ++ q) = some (r ++ rest)` for some `rest`,
    provided the extended broadcast also succeeds.
-/
theorem broadcastShapesRev_prefix {a b r : List Dim}
    (hab : a.length = b.length)
    (h : broadcastShapesRev a b = some r)
    {p q : List Dim} {r' : List Dim}
    (h' : broadcastShapesRev (a ++ p) (b ++ q) = some r') :
    ∃ rest, r' = r ++ rest := by
  by_contra h_contra;
  induction' a with a ha generalizing b r p q r' <;> induction' b with b hb generalizing r p q r' <;> simp_all +decide [ List.append_eq_append_iff ] ;
  · erw [ show r = [ ] from by { cases h; trivial } ] at h_contra; aesop;
  · rcases r with ( _ | ⟨ d, r ⟩ ) <;> simp_all +decide [ broadcastShapesRev ];
    cases h'' : broadcastDim a b <;> simp_all +decide [ Option.bind_eq_some_iff ];
    grind

/-
If the broadcast of extended lists succeeds, then the broadcast of the
    equal-length prefixes also succeeds.
-/
theorem broadcastShapesRev_prefix_succeeds {a b p q : List Dim} {r : List Dim}
    (hab : a.length = b.length)
    (h : broadcastShapesRev (a ++ p) (b ++ q) = some r) :
    ∃ r1 r2, broadcastShapesRev a b = some r1 ∧ r = r1 ++ r2 := by
  revert h;
  induction' a with a ha generalizing b p q r <;> induction' b with b hb generalizing p q r <;> simp_all +decide [ broadcastShapesRev ];
  cases h' : broadcastDim a b <;> simp_all +decide [ Option.bind_eq_some_iff ];
  grind

/-! ### Lifting theorems -/

/-
Lifting theorem: if concrete broadcasting succeeds, then the same suffix
    broadcast succeeds when the unbounded modifier is applied.
-/
theorem broadcast_lift_unbounded_left (s1 s2 : List Dim)
    (sOut : List Dim)
    (h : broadcastShapes (Shape.concrete s1) (Shape.concrete s2) = some (Shape.concrete sOut)) :
    ∃ sOutU, broadcastShapes (Shape.unbounded s1) (Shape.concrete s2) = some (Shape.unbounded sOutU) := by
  unfold broadcastShapes at *;
  cases le_total s1.length s2.length <;> simp_all +decide [ Shape.dims ];
  · obtain ⟨ a, ha₁, ha₂ ⟩ := h;
    have h_split : ∃ b c, s2.reverse = b ++ c ∧ b.length = s1.length := by
      use s2.reverse.take s1.length, s2.reverse.drop s1.length;
      aesop;
    obtain ⟨ b, c, hbc, hb ⟩ := h_split; simp_all +decide [ List.drop_eq_nil_of_le ] ;
    have := broadcastShapesRev_prefix_succeeds ( by aesop : s1.reverse.length = b.length ) ( by aesop : broadcastShapesRev ( s1.reverse ++ [ ] ) ( b ++ c ) = some a ) ; aesop;
  · obtain ⟨ a, ha₁, ha₂ ⟩ := h;
    have := @broadcastShapesRev_prefix_succeeds ( List.drop ( s1.length - s2.length ) s1 |> List.reverse ) ( s2.reverse ) ( List.take ( s1.length - s2.length ) s1 |> List.reverse ) [] a;
    simp_all +decide [ ← List.reverse_append ];
    exact this ( Nat.sub_sub_self ‹_› ) |> fun ⟨ r1, hr1, x, hx ⟩ => ⟨ r1, hr1 ⟩

theorem broadcast_lift_unbounded_right (s1 s2 : List Dim)
    (sOut : List Dim)
    (h : broadcastShapes (Shape.concrete s1) (Shape.concrete s2) = some (Shape.concrete sOut)) :
    ∃ sOutU, broadcastShapes (Shape.concrete s1) (Shape.unbounded s2) = some (Shape.unbounded sOutU) := by
  exact?

theorem broadcast_lift_unbounded_both (s1 s2 : List Dim)
    (sOut : List Dim)
    (h : broadcastShapes (Shape.concrete s1) (Shape.concrete s2) = some (Shape.concrete sOut)) :
    ∃ sOutU, broadcastShapes (Shape.unbounded s1) (Shape.unbounded s2) = some (Shape.unbounded sOutU) := by
  have h_broadcast_succ : ∃ r, broadcastShapesRev (s1.reverse.take (min s1.length s2.length)) (s2.reverse.take (min s1.length s2.length)) = some r := by
    unfold broadcastShapes at h;
    have := broadcastShapesRev_prefix_succeeds ( show List.length ( List.take ( Min.min s1.length s2.length ) s1.reverse ) = List.length ( List.take ( Min.min s1.length s2.length ) s2.reverse ) from ?_ ) ( show broadcastShapesRev ( List.take ( Min.min s1.length s2.length ) s1.reverse ++ List.drop ( Min.min s1.length s2.length ) s1.reverse ) ( List.take ( Min.min s1.length s2.length ) s2.reverse ++ List.drop ( Min.min s1.length s2.length ) s2.reverse ) = some sOut.reverse from ?_ ) ; aesop;
    · simp +decide [ List.length_reverse ];
    · rw [ List.take_append_drop, List.take_append_drop ] ; aesop;
  unfold broadcastShapes;
  unfold Shape.dims;
  grind +suggestions

/-- Subtyping relation. Extended with tensor unbounded subtyping:
    a concrete tensor with shape (prefix ++ suffix) is a subtype of
    an unbounded tensor with the same suffix. -/
inductive Subtype : ClassId → ClassId → Prop where
  | nil_sub (a : ClassId) : Subtype ClassId.nil_id a
  | refl (a : ClassId) : Subtype a a
  | true_bool : Subtype ClassId.true_id ClassId.bool_id
  | false_bool : Subtype ClassId.false_id ClassId.bool_id
  | trans {a b c : ClassId} : Subtype a b → Subtype b c → Subtype a c
  | lub_left (a b : ClassId) : Subtype a (lub a b)
  | lub_right (a b : ClassId) : Subtype b (lub a b)
  | tensor_unbounded_sub (prefix_ suffix_ : List Dim) :
    Subtype (ClassId.tensor_id (Shape.concrete (prefix_ ++ suffix_)))
            (ClassId.tensor_id (Shape.unbounded suffix_))

notation a " ≤ₜ " b => Subtype a b

end LambdaC
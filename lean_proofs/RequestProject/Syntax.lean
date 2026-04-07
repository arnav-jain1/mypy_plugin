/-
# λC Syntax and Basic Definitions

Formalization of the λC calculus from "Type-Level Computations for Ruby Libraries"
(arXiv:1904.03521v1), Appendix A.
-/

import Mathlib

/-- Class identifiers. We use natural numbers with distinguished constants. -/
abbrev ClassId := ℕ

/-- Method identifiers -/
abbrev MethId := ℕ

/-- Variable identifiers -/
abbrev VarId := ℕ

namespace LambdaC

/-- Distinguished class IDs -/
def ClassId.nil_id : ClassId := 0
def ClassId.obj_id : ClassId := 1
def ClassId.bool_id : ClassId := 2
def ClassId.true_id : ClassId := 3
def ClassId.false_id : ClassId := 4
def ClassId.type_id : ClassId := 5

/-- Tensor class ID parameterized by shape -/
noncomputable def ClassId.tensor_id (shape : List ℕ) : ClassId :=
  6 + Encodable.encode shape

/-- Values in λC -/
inductive Val where
  | nil : Val
  | obj : ClassId → Val    -- [A], an instance of class A
  | cls : ClassId → Val    -- A, a class value
  | true_ : Val
  | false_ : Val
  | tensor : List ℕ → Val  -- a tensor with given shape
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

/-- Method type: A₁ → A₂ -/
structure MethType where
  dom : ClassId
  cod : ClassId
deriving DecidableEq, Repr

/-- type_of(v) returns the class of a value -/
noncomputable def Val.typeOf : Val → ClassId
  | .nil => ClassId.nil_id
  | .obj a => a
  | .cls _ => ClassId.type_id
  | .true_ => ClassId.true_id
  | .false_ => ClassId.false_id
  | .tensor shape => ClassId.tensor_id shape

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

/-- Subtyping relation. Nil ≤ A for all A, A ≤ A (reflexive),
    True ≤ Bool, False ≤ Bool, and A ≤ A ⊔ A' for all A, A'.
    Also transitive. -/
inductive Subtype : ClassId → ClassId → Prop where
  | nil_sub (a : ClassId) : Subtype ClassId.nil_id a
  | refl (a : ClassId) : Subtype a a
  | true_bool : Subtype ClassId.true_id ClassId.bool_id
  | false_bool : Subtype ClassId.false_id ClassId.bool_id
  | trans {a b c : ClassId} : Subtype a b → Subtype b c → Subtype a c
  | lub_left (a b : ClassId) : Subtype a (lub a b)
  | lub_right (a b : ClassId) : Subtype b (lub a b)

notation a " ≤ₜ " b => Subtype a b

end LambdaC

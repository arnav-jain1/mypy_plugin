/-
# λC Dynamic Semantics

Small-step operational semantics for λC, formalized from the paper's Figure 8.
Extended with unbounded (rank-polymorphic) tensor shapes.
-/

import RequestProject.Syntax

namespace LambdaC

/-- Result of a step: either a normal configuration or blame -/
inductive StepResult where
  | config : Config → StepResult
  | blame : StepResult

/-- Whether a value is "truthy" (not nil or false) -/
def Val.isTruthy : Val → Bool
  | .nil => false
  | .false_ => false
  | .tensor _ => true
  | _ => true

/-- Whether two values are equivalent (for == comparison) -/
def Val.equiv : Val → Val → Bool
  | .nil, .nil => true
  | .true_, .true_ => true
  | .false_, .false_ => true
  | .obj a, .obj b => a == b
  | .cls a, .cls b => a == b
  | .tensor s1, .tensor s2 => s1 == s2
  | _, _ => false

/-- Check if an expression is of the form vr.m(v) with type_of(vr) = A and A.m ∈ U -/
def isUserMethodCall (e : Expr) (ms : MethodSets) : Prop :=
  ∃ vr v m, e = Expr.call (Expr.val vr) m (Expr.val v) ∧
    ⟨vr.typeOf, m⟩ ∈ ms.userDefined

/-- Check if an expression is a value -/
def Expr.isVal : Expr → Bool
  | .val _ => true
  | _ => false

/-- The method definition lookup function -/
def defOf (defs : MethKey → Option MethDef) (key : MethKey) : Option (VarId × Expr) :=
  match defs key with
  | some md => some (md.param, md.body)
  | none => none

/-- Library method call function (abstract) -/
def callLib (libImpl : MethKey → Val → Val → Option Val) (key : MethKey) (recv arg : Val) :
    Option Val :=
  libImpl key recv arg

/--
Dynamic semantics: single step relation.

⟨E, e, S⟩ ⇝ ⟨E', e', S'⟩

At runtime, all tensor shapes are concrete (List Dim). Unbounded shapes
exist only at the type level.
-/
inductive Step (methodDefs : MethKey → Option MethDef)
              (libImpl : MethKey → Val → Val → Option Val)
              (ms : MethodSets) :
              Config → StepResult → Prop where
  /-- (E-Var): ⟨E, x, S⟩ ⇝ ⟨E, E(x), S⟩ -/
  | eVar (E : DynEnv) (x : VarId) (S : Stack) (v : Val)
    (hx : E x = some v) :
    Step methodDefs libImpl ms ⟨E, Expr.var x, S⟩ (.config ⟨E, Expr.val v, S⟩)

  /-- (E-Self): ⟨E, self, S⟩ ⇝ ⟨E, E(self), S⟩ -/
  | eSelf (E : DynEnv) (S : Stack) (v : Val)
    (hself : E VarId.self_id = some v) :
    Step methodDefs libImpl ms ⟨E, Expr.self, S⟩ (.config ⟨E, Expr.val v, S⟩)

  /-- (E-TSelf): ⟨E, tself, S⟩ ⇝ ⟨E, E(tself), S⟩ -/
  | eTSelf (E : DynEnv) (S : Stack) (v : Val)
    (htself : E VarId.tself_id = some v) :
    Step methodDefs libImpl ms ⟨E, Expr.tself, S⟩ (.config ⟨E, Expr.val v, S⟩)

  /-- (E-Seq): ⟨E, v;e, S⟩ ⇝ ⟨E, e, S⟩ -/
  | eSeq (E : DynEnv) (v : Val) (e : Expr) (S : Stack) :
    Step methodDefs libImpl ms ⟨E, Expr.seq (Expr.val v) e, S⟩ (.config ⟨E, e, S⟩)

  /-- (E-New): ⟨E, A.NEW, S⟩ ⇝ ⟨E, [A], S⟩ -/
  | eNew (E : DynEnv) (A : ClassId) (S : Stack) :
    Step methodDefs libImpl ms ⟨E, Expr.new A, S⟩ (.config ⟨E, Expr.val (Val.obj A), S⟩)

  /-- (E-IfTrue): ⟨E, IF v THEN e₂ ELSE e₃, S⟩ ⇝ ⟨E, e₂, S⟩ if v is truthy -/
  | eIfTrue (E : DynEnv) (v : Val) (e2 e3 : Expr) (S : Stack)
    (htruthy : v.isTruthy = true) :
    Step methodDefs libImpl ms ⟨E, Expr.ite (Expr.val v) e2 e3, S⟩ (.config ⟨E, e2, S⟩)

  /-- (E-IfFalse): ⟨E, IF v THEN e₂ ELSE e₃, S⟩ ⇝ ⟨E, e₃, S⟩ if v is falsy -/
  | eIfFalse (E : DynEnv) (v : Val) (e2 e3 : Expr) (S : Stack)
    (hfalsy : v.isTruthy = false) :
    Step methodDefs libImpl ms ⟨E, Expr.ite (Expr.val v) e2 e3, S⟩ (.config ⟨E, e3, S⟩)

  /-- (E-EqTrue): ⟨E, v₁ == v₂, S⟩ ⇝ ⟨E, true, S⟩ if v₁ ≡ v₂ -/
  | eEqTrue (E : DynEnv) (v1 v2 : Val) (S : Stack)
    (heq : v1.equiv v2 = true) :
    Step methodDefs libImpl ms
      ⟨E, Expr.eq (Expr.val v1) (Expr.val v2), S⟩
      (.config ⟨E, Expr.val Val.true_, S⟩)

  /-- (E-EqFalse): ⟨E, v₁ == v₂, S⟩ ⇝ ⟨E, false, S⟩ if v₁ ≢ v₂ -/
  | eEqFalse (E : DynEnv) (v1 v2 : Val) (S : Stack)
    (hneq : v1.equiv v2 = false) :
    Step methodDefs libImpl ms
      ⟨E, Expr.eq (Expr.val v1) (Expr.val v2), S⟩
      (.config ⟨E, Expr.val Val.false_, S⟩)

  /-- (E-AppUD): ⟨E, C[vr.m(v)], S⟩ ⇝ ⟨[self↦vr, x↦v], e, (E,C)::S⟩
      when type_of(vr) = A and A.m ∈ U and def_of(A.m) = x.e -/
  | eAppUD (E : DynEnv) (C : Ctx) (vr v : Val) (m : MethId)
    (S : Stack) (x : VarId) (body : Expr) (md : MethDef)
    (hUserMethod : ⟨vr.typeOf, m⟩ ∈ ms.userDefined)
    (hDef : methodDefs ⟨vr.typeOf, m⟩ = some md)
    (hParam : md.param = x)
    (hBody : md.body = body) :
    Step methodDefs libImpl ms
      ⟨E, C[[ Expr.call (Expr.val vr) m (Expr.val v) ]], S⟩
      (.config ⟨(emptyEnv [VarId.self_id ↦ vr]) [x ↦ v], body, (E, C) :: S⟩)

  /-- (E-AppLib): ⟨E, ⌈Ares⌉vr.m(v), S⟩ ⇝ ⟨E, v', S⟩ -/
  | eAppLib (E : DynEnv) (Ares : ClassId) (vr v v' : Val)
    (m : MethId) (S : Stack)
    (hLibMethod : ⟨vr.typeOf, m⟩ ∈ ms.library)
    (hCall : libImpl ⟨vr.typeOf, m⟩ vr v = some v')
    (hSubtype : v'.typeOf ≤ₜ Ares) :
    Step methodDefs libImpl ms
      ⟨E, Expr.checkedCall Ares (Expr.val vr) m (Expr.val v), S⟩
      (.config ⟨E, Expr.val v', S⟩)

  /-- (E-Ret): ⟨E', v, (E, C) :: S⟩ ⇝ ⟨E, C[v], S⟩ -/
  | eRet (E' E : DynEnv) (v : Val) (C : Ctx) (S : Stack) :
    Step methodDefs libImpl ms
      ⟨E', Expr.val v, (E, C) :: S⟩
      (.config ⟨E, C[[ Expr.val v ]], S⟩)

  /-- (E-Context): ⟨E, C[e], S⟩ ⇝ ⟨E', C[e'], S⟩ -/
  | eContext (E E' : DynEnv) (C : Ctx) (e e' : Expr) (S : Stack)
    (hStep : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S⟩))
    (hNotUserCall : ¬ isUserMethodCall e ms)
    (hNotVal : e.isVal = false)
    :
    Step methodDefs libImpl ms
      ⟨E, C[[ e ]], S⟩
      (.config ⟨E', C[[ e' ]], S⟩)

  /-- Blame when nil receiver -/
  | eBlameNilRecv (E : DynEnv) (C : Ctx) (m : MethId) (v : Val) (S : Stack)
    (hNil : Val.nil = Val.nil) :
    Step methodDefs libImpl ms
      ⟨E, C[[ Expr.call (Expr.val Val.nil) m (Expr.val v) ]], S⟩
      .blame

  /-- Blame when checked call type check fails -/
  | eBlameCheckedCall (E : DynEnv) (Ares : ClassId) (vr v v' : Val)
    (m : MethId) (S : Stack)
    (hLibMethod : ⟨vr.typeOf, m⟩ ∈ ms.library)
    (hCall : libImpl ⟨vr.typeOf, m⟩ vr v = some v')
    (hNotSubtype : ¬(v'.typeOf ≤ₜ Ares)) :
    Step methodDefs libImpl ms
      ⟨E, Expr.checkedCall Ares (Expr.val vr) m (Expr.val v), S⟩
      .blame

  /-- (E-Broadcast): broadcast of two tensors with compatible concrete shapes -/
  | eBroadcast (E : DynEnv) (s1 s2 : List Dim) (sOut : List Dim) (S : Stack)
    (hBroadcast : broadcastShapes (Shape.concrete s1) (Shape.concrete s2) = some (Shape.concrete sOut)) :
    Step methodDefs libImpl ms
      ⟨E, Expr.broadcast (Expr.val (Val.tensor s1)) (Expr.val (Val.tensor s2)), S⟩
      (.config ⟨E, Expr.val (Val.tensor sOut), S⟩)

  /-- Blame when broadcast shapes are incompatible -/
  | eBlameBroadcast (E : DynEnv) (v1 v2 : Val) (S : Stack)
    (hNotMatch : ¬ (∃ s1 s2 sOut, v1 = Val.tensor s1 ∧ v2 = Val.tensor s2 ∧
                    broadcastShapes (Shape.concrete s1) (Shape.concrete s2) = some (Shape.concrete sOut))) :
    Step methodDefs libImpl ms
      ⟨E, Expr.broadcast (Expr.val v1) (Expr.val v2), S⟩
      .blame

  /-- (E-Matmul): matmul of two tensors with compatible concrete shapes. -/
  | eMatmul (E : DynEnv) (batch1 batch2 batchOut : List Dim) (m k n : ℕ) (S : Stack)
      (hBatch : broadcastShapes (Shape.concrete batch1) (Shape.concrete batch2) = some (Shape.concrete batchOut)) :
      Step methodDefs libImpl ms
        ⟨E, Expr.matmul (Expr.val (Val.tensor (batch1 ++ [m, k]))) (Expr.val (Val.tensor (batch2 ++ [k, n]))), S⟩
        (.config ⟨E, Expr.val (Val.tensor (batchOut ++ [m, n])), S⟩)

  /-- Blame when matmul shapes are incompatible -/
  | eBlameMatmul (E : DynEnv) (v1 v2 : Val) (S : Stack)
      (hNotMatch : ¬ (∃ batch1 batch2 batchOut m k n,
          broadcastShapes (Shape.concrete batch1) (Shape.concrete batch2) = some (Shape.concrete batchOut) ∧
          v1 = Val.tensor (batch1 ++ [m, k]) ∧
          v2 = Val.tensor (batch2 ++ [k, n]))) :
      Step methodDefs libImpl ms
        ⟨E, Expr.matmul (Expr.val v1) (Expr.val v2), S⟩
        .blame

  /-- (E-Reshape): reshape a tensor when the total sizes match -/
  | eReshape (E : DynEnv) (s1 s2 : List Dim) (S : Stack)
    (hSize : s1.prod = s2.prod) :
    Step methodDefs libImpl ms
      ⟨E, Expr.reshape (Expr.val (Val.tensor s1)) s2, S⟩
      (.config ⟨E, Expr.val (Val.tensor s2), S⟩)

  /-- Blame when reshape sizes don't match -/
  | eBlameReshape (E : DynEnv) (v : Val) (s2 : List Dim) (S : Stack)
    (hNotMatch : ¬ (∃ s1, v = Val.tensor s1 ∧ s1.prod = s2.prod)) :
    Step methodDefs libImpl ms
      ⟨E, Expr.reshape (Expr.val v) s2, S⟩
      .blame

  /-- Blame propagation in contexts -/
  | eBlameContext (E : DynEnv) (C : Ctx) (e : Expr) (S : Stack)
    (hStep : Step methodDefs libImpl ms ⟨E, e, S⟩ .blame) :
    Step methodDefs libImpl ms ⟨E, C[[ e ]], S⟩ .blame

/-- Multi-step relation (reflexive transitive closure) -/
inductive MultiStep (methodDefs : MethKey → Option MethDef)
                    (libImpl : MethKey → Val → Val → Option Val)
                    (ms : MethodSets) :
                    Config → StepResult → Prop where
  | refl (c : Config) : MultiStep methodDefs libImpl ms c (.config c)
  | step (c c' : Config) (r : StepResult)
    (hStep : Step methodDefs libImpl ms c (.config c'))
    (hMulti : MultiStep methodDefs libImpl ms c' r) :
    MultiStep methodDefs libImpl ms c r
  | blame (c : Config)
    (hStep : Step methodDefs libImpl ms c .blame) :
    MultiStep methodDefs libImpl ms c .blame

end LambdaC

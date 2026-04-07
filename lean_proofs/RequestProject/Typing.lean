/-
# λC Type Checking Rules

Formalization of the type checking rules from Figure 10 of the paper.
-/

import RequestProject.Semantics

namespace LambdaC

/-- Type checking judgment: Γ ⊢_CT e : A

This formalizes the rules from Figure 10.
CT and ms are fixed parameters (the class table and method sets are global).
-/
inductive HasType (CT : ClassTable) (ms : MethodSets) :
    TypEnv → Expr → ClassId → Prop where
  | tNil (Γ : TypEnv) :
    HasType CT ms Γ (Expr.val Val.nil) ClassId.nil_id
  | tObj (Γ : TypEnv) (A : ClassId) :
    HasType CT ms Γ (Expr.val (Val.obj A)) A
  | tSelf (Γ : TypEnv) (A : ClassId)
    (hSelf : Γ VarId.self_id = some A) :
    HasType CT ms Γ Expr.self A
  | tTrue (Γ : TypEnv) :
    HasType CT ms Γ (Expr.val Val.true_) ClassId.true_id
  | tFalse (Γ : TypEnv) :
    HasType CT ms Γ (Expr.val Val.false_) ClassId.false_id
  | tType (Γ : TypEnv) (A : ClassId) :
    HasType CT ms Γ (Expr.val (Val.cls A)) ClassId.type_id
  | tVar (Γ : TypEnv) (x : VarId) (A : ClassId)
    (hVar : Γ x = some A) :
    HasType CT ms Γ (Expr.var x) A
  | tTSelf (Γ : TypEnv) (A : ClassId)
    (hTSelf : Γ VarId.tself_id = some A) :
    HasType CT ms Γ Expr.tself A
  | tEq (Γ : TypEnv) (e1 e2 : Expr) (A1 A2 : ClassId)
    (h1 : HasType CT ms Γ e1 A1)
    (h2 : HasType CT ms Γ e2 A2) :
    HasType CT ms Γ (Expr.eq e1 e2) ClassId.bool_id
  | tSeq (Γ : TypEnv) (e1 e2 : Expr) (A1 A2 : ClassId)
    (h1 : HasType CT ms Γ e1 A1)
    (h2 : HasType CT ms Γ e2 A2) :
    HasType CT ms Γ (Expr.seq e1 e2) A2
  | tNew (Γ : TypEnv) (A : ClassId) :
    HasType CT ms Γ (Expr.new A) A
  | tIf (Γ : TypEnv) (e1 e2 e3 : Expr) (A1 A2 A3 : ClassId)
    (h1 : HasType CT ms Γ e1 A1)
    (h2 : HasType CT ms Γ e2 A2)
    (h3 : HasType CT ms Γ e3 A3) :
    HasType CT ms Γ (Expr.ite e1 e2 e3) (A2 ⊔ₜ A3)
  /-- T-App -/
  | tApp (Γ : TypEnv) (e0 e1 : Expr) (m : MethId)
    (Arecv Aarg A1 A2 : ClassId)
    (h0 : HasType CT ms Γ e0 Arecv)
    (h1 : HasType CT ms Γ e1 Aarg)
    (hUser : ⟨Arecv, m⟩ ∈ ms.userDefined)
    (hCT : CT Arecv m = some ⟨A1, A2⟩)
    (hSub : Aarg ≤ₜ A1) :
    HasType CT ms Γ (Expr.call e0 m e1) A2
  /-- T-App-Lib -/
  | tAppLib (Γ : TypEnv) (e0 e1 : Expr) (m : MethId)
    (Ares Arec Aarg : ClassId)
    (h0 : HasType CT ms Γ e0 Arec)
    (h1 : HasType CT ms Γ e1 Aarg)
    (hLib : ⟨Arec, m⟩ ∈ ms.library) :
    HasType CT ms Γ (Expr.checkedCall Ares e0 m e1) Ares
  /-- T-Tensor: a tensor value has the corresponding tensor type -/
  | tTensor (Γ : TypEnv) (shape : List ℕ) :
    HasType CT ms Γ (Expr.val (Val.tensor shape)) (ClassId.tensor_id shape)
  /-- T-Broadcast: if both operands have tensor type with the same shape, result has that type -/
  | tBroadcast (Γ : TypEnv) (e1 e2 : Expr) (s : List ℕ)
    (h1 : HasType CT ms Γ e1 (ClassId.tensor_id s))
    (h2 : HasType CT ms Γ e2 (ClassId.tensor_id s)) :
    HasType CT ms Γ (Expr.broadcast e1 e2) (ClassId.tensor_id s)
  /-- T-Matmul: Performs batched matrix multiplication.
      Left tensor must be [d1, d2, d3], right must be [d1, d3, f3].
      Resulting tensor has shape [d1, d2, f3]. -/
  | tMatmul (Γ : TypEnv) (e1 e2 : Expr) (d1 d2 d3 f3 : ℕ)
    (h1 : HasType CT ms Γ e1 (ClassId.tensor_id [d1, d2, d3]))
    (h2 : HasType CT ms Γ e2 (ClassId.tensor_id [d1, d3, f3])) :
    HasType CT ms Γ (Expr.matmul e1 e2) (ClassId.tensor_id [d1, d2, f3])
  /-- Subsumption -/
  | tSub (Γ : TypEnv) (e : Expr) (a a' : ClassId)
    (h : HasType CT ms Γ e a)
    (hSub : Subtype a a') :
    HasType CT ms Γ e a'
  /-- Blame has type Nil -/
  | tBlame (Γ : TypEnv) :
    HasType CT ms Γ (Expr.val Val.nil) ClassId.nil_id

/-- Context typing: Γ[□ → A] ⊢ C : A' -/
inductive CtxHasType (CT : ClassTable) (ms : MethodSets) :
    TypEnv → ClassId → Ctx → ClassId → Prop where
  | hole (Γ : TypEnv) (A : ClassId) :
    CtxHasType CT ms Γ A Ctx.hole A
  | callL (Γ : TypEnv) (Ahole Arecv A1 A2 Aarg : ClassId)
    (C : Ctx) (m : MethId) (e : Expr)
    (hCtx : CtxHasType CT ms Γ Ahole C Arecv)
    (hArg : HasType CT ms Γ e Aarg)
    (hUser : ⟨Arecv, m⟩ ∈ ms.userDefined)
    (hCT : CT Arecv m = some ⟨A1, A2⟩)
    (hSub : Aarg ≤ₜ A1) :
    CtxHasType CT ms Γ Ahole (Ctx.callL C m e) A2
  | callR (Γ : TypEnv) (Ahole Arecv A1 A2 Aarg : ClassId)
    (v : Val) (m : MethId) (C : Ctx)
    (hRecv : HasType CT ms Γ (Expr.val v) Arecv)
    (hCtx : CtxHasType CT ms Γ Ahole C Aarg)
    (hUser : ⟨Arecv, m⟩ ∈ ms.userDefined)
    (hCT : CT Arecv m = some ⟨A1, A2⟩)
    (hSub : Aarg ≤ₜ A1) :
    CtxHasType CT ms Γ Ahole (Ctx.callR v m C) A2
  | seqL (Γ : TypEnv) (Ahole A1 A2 : ClassId) (C : Ctx) (e : Expr)
    (hCtx : CtxHasType CT ms Γ Ahole C A1)
    (hExpr : HasType CT ms Γ e A2) :
    CtxHasType CT ms Γ Ahole (Ctx.seqL C e) A2
  | iteC (Γ : TypEnv) (Ahole A1 A2 A3 : ClassId) (C : Ctx) (e1 e2 : Expr)
    (hCtx : CtxHasType CT ms Γ Ahole C A1)
    (hThen : HasType CT ms Γ e1 A2)
    (hElse : HasType CT ms Γ e2 A3) :
    CtxHasType CT ms Γ Ahole (Ctx.iteC C e1 e2) (A2 ⊔ₜ A3)
  | eqL (Γ : TypEnv) (Ahole A1 A2 : ClassId) (C : Ctx) (e : Expr)
    (hCtx : CtxHasType CT ms Γ Ahole C A1)
    (hExpr : HasType CT ms Γ e A2) :
    CtxHasType CT ms Γ Ahole (Ctx.eqL C e) ClassId.bool_id
  | eqR (Γ : TypEnv) (Ahole A1 A2 : ClassId) (v : Val) (C : Ctx)
    (hVal : HasType CT ms Γ (Expr.val v) A1)
    (hCtx : CtxHasType CT ms Γ Ahole C A2) :
    CtxHasType CT ms Γ Ahole (Ctx.eqR v C) ClassId.bool_id
  | checkedCallL (Γ : TypEnv) (Ahole Arecv Ares Aarg : ClassId)
    (C : Ctx) (m : MethId) (e : Expr)
    (hCtx : CtxHasType CT ms Γ Ahole C Arecv)
    (hArg : HasType CT ms Γ e Aarg)
    (hLib : ⟨Arecv, m⟩ ∈ ms.library) :
    CtxHasType CT ms Γ Ahole (Ctx.checkedCallL Ares C m e) Ares
  | checkedCallR (Γ : TypEnv) (Ahole Arecv Aarg Ares : ClassId)
    (v : Val) (m : MethId) (C : Ctx)
    (hRecv : HasType CT ms Γ (Expr.val v) Arecv)
    (hCtx : CtxHasType CT ms Γ Ahole C Aarg)
    (hLib : ⟨Arecv, m⟩ ∈ ms.library) :
    CtxHasType CT ms Γ Ahole (Ctx.checkedCallR Ares v m C) Ares
  | broadcastL (Γ : TypEnv) (Ahole : ClassId) (C : Ctx) (e : Expr) (s : List ℕ)
    (hCtx : CtxHasType CT ms Γ Ahole C (ClassId.tensor_id s))
    (hExpr : HasType CT ms Γ e (ClassId.tensor_id s)) :
    CtxHasType CT ms Γ Ahole (Ctx.broadcastL C e) (ClassId.tensor_id s)
  | broadcastR (Γ : TypEnv) (Ahole : ClassId) (v : Val) (C : Ctx) (s : List ℕ)
    (hVal : HasType CT ms Γ (Expr.val v) (ClassId.tensor_id s))
    (hCtx : CtxHasType CT ms Γ Ahole C (ClassId.tensor_id s)) :
    CtxHasType CT ms Γ Ahole (Ctx.broadcastR v C) (ClassId.tensor_id s)
  | matmulL (Γ : TypEnv) (Ahole : ClassId) (C : Ctx) (e : Expr) (d1 d2 d3 f3 : ℕ)
    (hCtx : CtxHasType CT ms Γ Ahole C (ClassId.tensor_id [d1, d2, d3]))
    (hExpr : HasType CT ms Γ e (ClassId.tensor_id [d1, d3, f3])) :
    CtxHasType CT ms Γ Ahole (Ctx.matmulL C e) (ClassId.tensor_id [d1, d2, f3])
  | matmulR (Γ : TypEnv) (Ahole : ClassId) (v : Val) (C : Ctx) (d1 d2 d3 f3 : ℕ)
    (hVal : HasType CT ms Γ (Expr.val v) (ClassId.tensor_id [d1, d2, d3]))
    (hCtx : CtxHasType CT ms Γ Ahole C (ClassId.tensor_id [d1, d3, f3])) :
    CtxHasType CT ms Γ Ahole (Ctx.matmulR v C) (ClassId.tensor_id [d1, d2, f3])
  /-- Subsumption for context output type -/
  | ctxSub (Γ : TypEnv) (Ahole : ClassId) (C : Ctx) (tyC tyC' : ClassId)
    (hCtx : CtxHasType CT ms Γ Ahole C tyC)
    (hSub : Subtype tyC tyC') :
    CtxHasType CT ms Γ Ahole C tyC'

/-- Environmental consistency -/
def EnvConsistent (CT : ClassTable) (ms : MethodSets) (Γ : TypEnv) (E : DynEnv) : Prop :=
  (∀ x, (∃ v, E x = some v) ↔ (∃ a, Γ x = some a)) ∧
  (∀ x v, E x = some v →
    ∃ a a', HasType CT ms Γ (Expr.val v) a ∧ Γ x = some a' ∧ a ≤ₜ a')

/-- Stack subtyping -/
def TypeSubStack (a : ClassId) : TypeStack → Prop
  | [] => True
  | ts :: _ => a ≤ₜ ts.retType

/-- Stack consistency -/
inductive StackConsistent (CT : ClassTable) (ms : MethodSets) :
    TypeStack → Stack → Prop where
  | nil : StackConsistent CT ms [] []
  | cons (Γ : TypEnv) (retTy ctxTy : ClassId) (E : DynEnv) (C : Ctx)
    (TS : TypeStack) (S : Stack)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hCtxType : CtxHasType CT ms Γ retTy C ctxTy)
    (hRest : StackConsistent CT ms TS S)
    (hSubStack : TS = [] ∨ TypeSubStack ctxTy TS) :
    StackConsistent CT ms (⟨Γ, retTy, ctxTy⟩ :: TS) ((E, C) :: S)

/-- Class table validity -/
def ValidCT (CT : ClassTable) (ms : MethodSets)
    (methodDefs : MethKey → Option MethDef) : Prop :=
  (∀ key, key ∈ ms.userDefined →
    ∃ a1 a2, CT key.cls key.meth = some ⟨a1, a2⟩ ∧
    ∃ md, methodDefs key = some md ∧
    ∃ a2', HasType CT ms
      ((emptyEnv [VarId.self_id ↦ key.cls]) [md.param ↦ a1])
      md.body a2' ∧ a2' ≤ₜ a2) ∧
  (∀ key, key ∈ ms.library →
    ∃ mt, CT key.cls key.meth = some mt) ∧
  (∀ cls1 cls2 m a1 a2 a1' a2',
    Subtype cls2 cls1 →
    CT cls2 m = some ⟨a1', a2'⟩ →
    CT cls1 m = some ⟨a1, a2⟩ →
    Subtype a1 a1' ∧ Subtype a2' a2) ∧
  -- Method inheritance: subtypes inherit user-defined methods
  (∀ cls1 cls2 m,
    Subtype cls2 cls1 →
    ⟨cls1, m⟩ ∈ ms.userDefined →
    ⟨cls2, m⟩ ∈ ms.userDefined) ∧
  -- Method inheritance: subtypes inherit library methods
  (∀ cls1 cls2 m,
    Subtype cls2 cls1 →
    ⟨cls1, m⟩ ∈ ms.library →
    ⟨cls2, m⟩ ∈ ms.library)

end LambdaC

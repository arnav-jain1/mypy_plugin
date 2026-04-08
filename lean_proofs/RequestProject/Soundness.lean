/-
# λC Soundness

Formalization of the soundness proof from Appendix A of
"Type-Level Computations for Ruby Libraries" (arXiv:1904.03521v1).
-/

import RequestProject.Typing

namespace LambdaC

variable {CT : ClassTable}
         {ms : MethodSets}
         {methodDefs : MethKey → Option MethDef}
         {libImpl : MethKey → Val → Val → Option Val}

/-! ## Basic typing lemmas -/

/-- Value typing lemma -/
theorem val_has_type (Γ : TypEnv) (v : Val) :
    HasType CT ms Γ (Expr.val v) v.typeOf := by
  cases v with
  | nil => exact HasType.tNil Γ
  | obj A => exact HasType.tObj Γ A
  | cls A => exact HasType.tType Γ A
  | true_ => exact HasType.tTrue Γ
  | false_ => exact HasType.tFalse Γ
  | tensor shape => exact HasType.tTensor Γ shape

/-
PROBLEM
Value type subtyping: if val v has type A, then v.typeOf ≤ A

PROVIDED SOLUTION
Generalize to: ∀ {e A}, HasType CT ms Γ e A → e = Expr.val v → v.typeOf ≤ₜ A. By induction on HasType. Only value constructors (tNil, tObj, tTrue, tFalse, tType, tBlame) and tSub apply. For value constructors, cases on hEq gives v.typeOf = the type, so Subtype.refl. For tSub, use IH + trans.
-/
theorem val_type_subtype {Γ : TypEnv} {v : Val} {A : ClassId}
    (h : HasType CT ms Γ (Expr.val v) A) : v.typeOf ≤ₜ A := by
  have h_generalized : ∀ {e : Expr} {A : ClassId}, HasType CT ms Γ e A → e = Expr.val v → v.typeOf ≤ₜ A := by
    intros e A h h_eq; induction h <;> simp_all +decide ;
    all_goals subst h_eq; exact?;
  exact h_generalized h rfl

/-- Weakening -/
def TypEnv.extends_ (Γ Δ : TypEnv) : Prop :=
  ∀ x a, Γ x = some a → Δ x = some a

/-
PROVIDED SOLUTION
By induction on hType. Each case: for value constructors (tNil, tObj, tTrue, tFalse, tType, tBlame), apply same constructor on Δ. For tSelf/tTSelf/tVar, use hExt to get the binding in Δ. For compound expressions (tSeq, tIf, tEq, tApp, tAppLib), use IH on subexpressions. For tSub, use IH then tSub. For tNew, apply tNew.
-/
theorem weakening {Γ Δ : TypEnv} {e : Expr} {ty : ClassId}
    (hType : HasType CT ms Γ e ty)
    (hExt : TypEnv.extends_ Γ Δ) :
    HasType CT ms Δ e ty := by
  -- The proof proceeds by induction on the type derivation.
  induction' hType with Γ e ty hType hExt hType' hExt' hType'' hExt'';
  all_goals exact?

/-- Subtyping is transitive -/
theorem subtype_trans' {a b c : ClassId}
    (h1 : Subtype a b) (h2 : Subtype b c) : Subtype a c :=
  Subtype.trans h1 h2

/-! ## Inversion lemmas -/

/-
PROVIDED SOLUTION
Generalize to: ∀ {e ty}, HasType CT ms Γ e ty → e = Expr.var x → ∃ a, Γ x = some a ∧ Subtype a ty. By induction on HasType. Only tVar and tSub match (all other constructors have different expression forms, so cases hEq closes them). For tVar: cases hEq, exact ⟨_, ‹_›, Subtype.refl _⟩. For tSub: use IH then Subtype.trans.
-/
theorem var_inversion {Γ : TypEnv} {x : VarId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.var x) ty) :
    ∃ a, Γ x = some a ∧ Subtype a ty := by
  have h_ind : ∀ {e ty}, HasType CT ms Γ e ty → e = Expr.var x → ∃ a, Γ x = some a ∧ Subtype a ty := by
    intros e ty hType hEq;
    induction' hType with e ty hType hEq generalizing x;
    all_goals cases hEq;
    · exact ⟨ _, ‹_›, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ h rfl ) fun a ha => ⟨ a, ha.1, Subtype.trans ha.2 h₁ ⟩;
  exact h_ind h rfl

/-
PROVIDED SOLUTION
Same pattern as var_inversion. Generalize to ∀ {e ty}, HasType → e = Expr.self → ∃ a, Γ self_id = some a ∧ a ≤ ty. Only tSelf and tSub match. For tSelf: Subtype.refl. For tSub: IH + trans.
-/
theorem self_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.self ty) :
    ∃ a, Γ VarId.self_id = some a ∧ Subtype a ty := by
  -- By definition of HasType, we know that Γ self_id = some a for some a.
  obtain ⟨a, ha⟩ : ∃ a, Γ VarId.self_id = some a ∧ HasType CT ms Γ Expr.self a := by
    have h_self : HasType CT ms Γ Expr.self ty := h;
    contrapose! h_self;
    intro H;
    have h_self : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.self → ∃ a, Γ VarId.self_id = some a ∧ HasType CT ms Γ Expr.self a := by
      intros e ty h e_eq_self
      induction' h with e ty h ih;
      all_goals cases e_eq_self;
      · exact ⟨ _, h, HasType.tSelf _ _ h ⟩;
      · tauto;
    exact absurd ( h_self H rfl ) ( by tauto );
  -- By definition of HasType, we know that Γ self_id = some a for some a. Use this fact.
  use a;
  convert ha.1;
  have h_subtype : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.self → ∃ a, Γ VarId.self_id = some a ∧ Subtype a ty := by
    intros e ty hType hEq
    induction' hType with e ty hType ih;
    all_goals cases hEq;
    · exact ⟨ _, hType, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ rfl ) fun x hx => ⟨ x, hx.1, Subtype.trans hx.2 h₁ ⟩;
  specialize @h_subtype _ _ h rfl ; aesop

/-
PROVIDED SOLUTION
Same pattern. Generalize to ∀ {e ty}, HasType → e = Expr.tself → ∃ a, Γ tself_id = some a ∧ a ≤ ty. Only tTSelf and tSub match.
-/
theorem tself_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.tself ty) :
    ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
  -- By definition of HasType, we know that tself has type tself_id.
  have h_tself_id : HasType CT ms Γ Expr.tself ty := by
    assumption;
  -- By definition of HasType, we know that tself has type tself_id. We can use the tTSelf constructor to obtain this.
  have h_tself_id : ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
    have := h_tself_id
    have h_tself_id : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.tself → ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
      intros e ty h_type h_eq
      induction' h_type with e ty h_type ih;
      all_goals cases h_eq;
      · exact ⟨ _, ‹_›, Subtype.refl _ ⟩;
      · -- By transitivity of the subtype relation, we can combine the two inequalities.
        have h_trans : ∀ {a b c : ClassId}, Subtype a b → Subtype b c → Subtype a c := by
          exact?;
        grind;
    exact h_tself_id this rfl;
  exact h_tself_id

/-
PROVIDED SOLUTION
Generalize to ∀ {e ty}, HasType → e = Expr.call e0 m e1 → ∃ Arecv Aarg A1 A2, ... . Only tApp and tSub match. For tApp: direct with Subtype.refl for the result type. For tSub: IH + trans on result type.
-/
theorem call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.call e0 m e1) ty) :
    ∃ (Arecv Aarg A1 A2 : ClassId),
      HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧
      CT Arecv m = some ⟨A1, A2⟩ ∧ Subtype Aarg A1 ∧
      Subtype A2 ty ∧ ⟨Arecv, m⟩ ∈ ms.userDefined := by
  by_contra h_contra;
  obtain ⟨Arecv, Aarg, A1, A2, hArecv, hAarg, hCT, hSub, hSub'⟩ : ∃ Arecv Aarg A1 A2, HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧ CT Arecv m = some ⟨A1, A2⟩ ∧ (Aarg ≤ₜ A1) ∧ (A2 ≤ₜ ty) ∧ (⟨Arecv, m⟩ ∈ ms.userDefined) := by
    have h_ind : ∀ {e ty}, HasType CT ms Γ e ty → e = Expr.call e0 m e1 → ∃ Arecv Aarg A1 A2, HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧ CT Arecv m = some ⟨A1, A2⟩ ∧ (Aarg ≤ₜ A1) ∧ (A2 ≤ₜ ty) ∧ (⟨Arecv, m⟩ ∈ ms.userDefined) := by
      intros e ty h_type h_eq
      induction' h_type with e ty h_type ih;
      all_goals cases h_eq;
      · exact ⟨ _, _, _, _, by assumption, by assumption, by assumption, by assumption, by tauto, by assumption ⟩;
      · rename_i h₁ h₂ h₃;
        exact Exists.elim ( h₃ rfl ) fun Arecv hArecv => Exists.elim hArecv fun Aarg hAarg => Exists.elim hAarg fun A1 hA1 => Exists.elim hA1 fun A2 hA2 => ⟨ Arecv, Aarg, A1, A2, hA2.1, hA2.2.1, hA2.2.2.1, hA2.2.2.2.1, hA2.2.2.2.2.1.trans h₁, hA2.2.2.2.2.2 ⟩
    exact h_ind h rfl;
  exact h_contra ⟨ Arecv, Aarg, A1, A2, hArecv, hAarg, hCT, hSub, hSub'.1, hSub'.2 ⟩

theorem checked_call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId}
    {Ares ty : ClassId}
    (h : HasType CT ms Γ (Expr.checkedCall Ares e0 m e1) ty) :
    ∃ (Arec Aarg : ClassId),
      HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧
      Subtype Ares ty ∧ ⟨Arec, m⟩ ∈ ms.library := by
  -- By definition of `HasType`, we know that if `HasType CT ms Γ (Expr.checkedCall Ares e0 m e1) ty`, then there exist `Arec`, `Aarg` such that `HasType CT ms Γ e0 Arec`, `HasType CT ms Γ e1 Aarg`, `Ares ≤ₜ ty`, and `⟨Arec, m⟩ ∈ ms.library`.
  apply Classical.byContradiction
  intro h_no_Arec_Aarg
  generalize_proofs at *; (
  have h_tAppLib : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.checkedCall Ares e0 m e1 → ∃ Arec Aarg, HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧ (Ares ≤ₜ ty) ∧ ⟨Arec, m⟩ ∈ ms.library := by
    intros e ty h h_eq; induction h; aesop;
    all_goals cases h_eq;
    · exact ⟨ _, _, by assumption, by assumption, by exact Subtype.refl _, by assumption ⟩;
    · rename_i h₁ h₂ h₃; specialize h₃ rfl; obtain ⟨ Arec, Aarg, hArec, hAarg, hAres, hLib ⟩ := h₃; exact ⟨ Arec, Aarg, hArec, hAarg, by
        exact?, hLib ⟩ ;
  generalize_proofs at *; (
  exact h_no_Arec_Aarg <| h_tAppLib h rfl))

/-
PROVIDED SOLUTION
Define a helper: ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.ite e1 e2 e3 → ∃ A1 A2 A3, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ HasType CT ms Γ e3 A3 ∧ (A2 ⊔ₜ A3) ≤ₜ ty.  Prove by induction' on HasType. All constructors except tIf and tSub yield contradiction via `cases hEq`. For tIf: use Subtype.refl. For tSub: use IH + Subtype.trans.
-/
theorem ite_inversion {Γ : TypEnv} {e1 e2 e3 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.ite e1 e2 e3) ty) :
    ∃ (A1 A2 A3 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      HasType CT ms Γ e3 A3 ∧ Subtype (A2 ⊔ₜ A3) ty := by
  have h_ind : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = e1.ite e2 e3 → ∃ A1 A2 A3, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ HasType CT ms Γ e3 A3 ∧ (A2⊔ₜA3) ≤ₜ ty := by
    intros e ty h h_eq;
    induction' h with e ty h ih generalizing e1 e2 e3;
    all_goals cases h_eq;
    · exact ⟨ _, _, _, ‹_›, ‹_›, ‹_›, by tauto ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ h rfl ) fun A1 hA1 => Exists.elim hA1 fun A2 hA2 => Exists.elim hA2 fun A3 hA3 => ⟨ A1, A2, A3, hA3.1, hA3.2.1, hA3.2.2.1, Subtype.trans hA3.2.2.2 h₁ ⟩;
  exact h_ind h rfl

/-
PROVIDED SOLUTION
Generalize. Only tSeq and tSub match. For tSeq: Subtype.refl. For tSub: IH + trans.
-/
theorem seq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.seq e1 e2) ty) :
    ∃ (A1 A2 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype A2 ty := by
  revert e1 e2 ty h;
  intro e1 e2 ty h
  obtain ⟨A1, A2, h1, h2, h3⟩ : ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
    have h_seq : HasType CT ms Γ (e1.seq e2) ty := h
    contrapose! h_seq
    generalize_proofs at *;
    intro h_seq';
    obtain ⟨A1, A2, h1, h2, h3⟩ : ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
      have h_seq : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {e1 e2 : Expr}, e = e1.seq e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
        intros e ty h e1 e2 he
        induction' h with e1 e2 ty h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86 h87 h88 h89 h90 h91 h92 h93 h94 h95 h96 h97 h98 h99 h100
        generalize_proofs at *; (
        cases he);
        all_goals cases he; try tauto;
      exact h_seq h_seq' rfl
    generalize_proofs at *; (
    exact h_seq A1 A2 h1 h2 h3)
  exact ⟨A1, A2, h1, h2, h3⟩

/-
PROVIDED SOLUTION
Define a helper: ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.eq e1 e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ ClassId.bool_id ≤ₜ ty.  Prove by induction' on HasType. All constructors except tEq and tSub yield contradiction via `cases hEq`. For tEq: use Subtype.refl for bool_id. For tSub: use IH + Subtype.trans.
-/
theorem eq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.eq e1 e2) ty) :
    ∃ (A1 A2 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      Subtype ClassId.bool_id ty := by
  have h_contra : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.eq e1 e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ ClassId.bool_id ≤ₜ ty := by
    intros e ty h h_eq
    induction' h with e ty h ih;
    all_goals cases h_eq;
    · exact ⟨ _, _, by assumption, by assumption, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ rfl ) fun A1 hA1 => Exists.elim hA1 fun A2 hA2 => ⟨ A1, A2, hA2.1, hA2.2.1, Subtype.trans hA2.2.2 h₁ ⟩;
  exact h_contra h rfl

/-
PROVIDED SOLUTION
Generalize. Only tNew and tSub match. For tNew: Subtype.refl. For tSub: IH + trans.
-/
theorem new_inversion {Γ : TypEnv} {cls : ClassId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.new cls) ty) :
    Subtype cls ty := by
  cases h;
  · constructor;
  · rename_i h1 h2;
    -- By the induction hypothesis, we know that `HasType CT ms Γ (Expr.new cls) a✝`.
    -- Applying the definition of `HasType`, we get that `cls ≤ₜ a✝`.
    have h_ind : cls ≤ₜ ‹ClassId› := by
      have h_ind : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {cls : ClassId}, e = Expr.new cls → cls ≤ₜ ty := by
        intros e ty h cls hcls
        induction' h with e ty h cls hcls ih;
        all_goals cases hcls;
        · constructor;
        · exact?;
      exact h_ind h1 rfl;
    exact?

/-! ## Context lemmas -/

/-- tensor_id values are always ≥ 6 -/
private lemma tensor_id_ge_six (s : List ℕ) : ClassId.tensor_id s ≥ 6 := by
  simp [ClassId.tensor_id]

/-
lub never returns nil_id unless both arguments are nil_id
-/
private lemma lub_eq_zero {a b : ClassId} (h : lub a b = ClassId.nil_id) :
    a = ClassId.nil_id ∧ b = ClassId.nil_id := by
      unfold lub at h;
      split_ifs at h <;> simp_all +decide

/-
If a ≤ₜ nil_id, then a = nil_id
-/
private lemma subtype_nil_eq {a : ClassId} (h : a ≤ₜ ClassId.nil_id) :
    a = ClassId.nil_id := by
      have := h;
      revert ‹a ≤ₜ ClassId.nil_id› a;
      intros a ha ha';
      -- By definition of lub, if lub a b = ClassId.nil_id, then a must be ClassId.nil_id and b must be ClassId.nil_id.
      have h_lub_nil : ∀ a b : ClassId, lub a b = ClassId.nil_id → a = ClassId.nil_id ∧ b = ClassId.nil_id := by
        exact?;
      have h_lub_nil : ∀ a b : ClassId, Subtype a b → b = ClassId.nil_id → a = ClassId.nil_id := by
        intros a b hab hb_nil
        induction' hab with a b hab ih;
        all_goals norm_cast at *;
        · grind;
        · exact h_lub_nil _ _ hb_nil |>.1;
        · exact h_lub_nil _ _ hb_nil |>.2;
      exact h_lub_nil a _ ha rfl

/-
For a ∈ [1,5], lub(a, b) ≤ 5 for any b
-/
private lemma lub_le_five_left {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    lub a b ≤ 5 := by
      unfold lub; split_ifs <;> simp_all +decide ;

/-
For a ∈ [1,5], lub(b, a) ≤ 5 for any b
-/
private lemma lub_le_five_right {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    lub b a ≤ 5 := by
      convert lub_le_five_left ha1 ha5 using 1;
      swap;
      exact b;
      unfold lub;
      grind

/-
If a ∈ [1,5] and a ≤ₜ b, then b ≤ 5
-/
private lemma subtype_small_stays_small {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
    (h : a ≤ₜ b) : b ≤ 5 := by
      induction' h with a b h ih;
      all_goals norm_cast at *;
      · rename_i h₁ h₂ h₃ h₄;
        by_cases h₅ : 1 ≤ ih <;> by_cases h₆ : ih ≤ 5 <;> simp_all +decide;
        exact absurd ( subtype_nil_eq h₁ ) ( by rintro rfl; contradiction );
      · exact?;
      · exact?

/-
If a ≥ 6 and a ≤ₜ b, then b = a or b ≤ 5
-/
private lemma subtype_from_ge_six {a b : ClassId} (ha : a ≥ 6)
    (h : a ≤ₜ b) : b = a ∨ b ≤ 5 := by
      contrapose! h;
      revert h;
      rintro ⟨ hab, hb ⟩ h
      induction' h with a b h ih;
      all_goals norm_cast at *;
      · rename_i k hk₁ hk₂ hk₃ hk₄;
        by_cases hih : ih = h <;> by_cases hih' : ih ≥ 6 <;> simp_all +decide;
        · exact absurd hk₃ ( not_le_of_gt hb );
        · exact absurd ( subtype_small_stays_small ( show 1 ≤ ih from Nat.pos_of_ne_zero ( by
                                                      rintro rfl;
                                                      exact absurd ( subtype_nil_eq hk₁ ) ( by rintro rfl; contradiction ) ) ) hk₃ hk₂ ) ( by
                                                      exact? );
      · rename_i a b;
        cases a <;> cases b <;> simp_all +decide [ lub ];
        split_ifs at * <;> norm_cast at *;
        lia;
      · unfold lub at *;
        split_ifs at hb;
        all_goals simp_all +decide [ ClassId ]

/-- If a ≥ 6 and b ≥ 6 and a ≤ₜ b, then a = b.
    This holds because the Subtype relation only connects tensor-range values
    to themselves (no non-trivial subtypings between distinct tensor types). -/
private lemma subtype_ge_six_eq {a b : ClassId} (ha : a ≥ 6) (hb : b ≥ 6)
    (h : a ≤ₜ b) : a = b := by
  rcases subtype_from_ge_six ha h with rfl | hle
  · rfl
  · exact absurd hle (by simp [ClassId] at *; omega)

/-
If tensor_id s1 ≤ₜ tensor_id s2, then s1 = s2.
-/
theorem tensor_id_subtype_implies_eq {s1 s2 : List ℕ}
    (h : ClassId.tensor_id s1 ≤ₜ ClassId.tensor_id s2) : s1 = s2 := by
      have := @subtype_ge_six_eq;
      specialize @this ( ClassId.tensor_id s1 ) ( ClassId.tensor_id s2 ) ; norm_num at *;
      simp_all +decide [ ClassId.tensor_id ]

/-
Broadcast inversion: if broadcast(e1,e2) has type ty, there exists s such that
    e1 and e2 both have type tensor_id s and tensor_id s ≤ ty
-/
theorem broadcast_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.broadcast e1 e2) ty) :
    ∃ (s1 s2 sOut : List ℕ),
      broadcastShapes s1 s2 = some sOut ∧
      HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧
      HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧
      Subtype (ClassId.tensor_id sOut) ty := by
  have h_inv : ∀ {e ty}, HasType CT ms Γ e ty → e = Expr.broadcast e1 e2 →
      ∃ s1 s2 sOut, broadcastShapes s1 s2 = some sOut ∧
        HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧
        HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧
        (ClassId.tensor_id sOut ≤ₜ ty) := by
    intros e ty h h_eq; induction h; aesop;
    all_goals cases h_eq;
    · exact ⟨ _, _, _, by assumption, by assumption, by assumption, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact h₃ rfl |> fun ⟨ s1, s2, sOut, hb, hs₁, hs₂, hs₃ ⟩ =>
        ⟨ s1, s2, sOut, hb, hs₁, hs₂, Subtype.trans hs₃ h₁ ⟩;
  exact h_inv h rfl

/-
Matmul inversion: if matmul(e1,e2) has type ty, there exist batch1 batch2 batchOut m k n such that
    batch dims are broadcast-compatible, e1 has type tensor_id (batch1 ++ [m, k]),
    e2 has type tensor_id (batch2 ++ [k, n]), and tensor_id (batchOut ++ [m, n]) ≤ ty
-/
theorem matmul_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.matmul e1 e2) ty) :
    ∃ (batch1 batch2 batchOut : List ℕ) (m k n : ℕ),
      broadcastShapes batch1 batch2 = some batchOut ∧
      HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧
      HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧
      Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
  have h_inv : ∀ {e ty}, HasType CT ms Γ e ty → e = Expr.matmul e1 e2 →
      ∃ batch1 batch2 batchOut m k n,
        broadcastShapes batch1 batch2 = some batchOut ∧
        HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧
        HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧
        (ClassId.tensor_id (batchOut ++ [m, n]) ≤ₜ ty) := by
    intros e ty h h_eq; induction h; aesop;
    all_goals cases h_eq;
    · exact ⟨ _, _, _, _, _, _, by assumption, by assumption, by assumption, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact h₃ rfl |> fun ⟨ b1, b2, bo, m, k, n, hb, hs₁, hs₂, hs₃ ⟩ =>
        ⟨ b1, b2, bo, m, k, n, hb, hs₁, hs₂, Subtype.trans hs₃ h₁ ⟩;
  exact h_inv h rfl

/-- Lemma 1 (Contextual Decomposition). -/
theorem ctx_decomposition
    {Γ : TypEnv} {C : Ctx} {e : Expr} {tyC : ClassId}
    (hCtxExpr : HasType CT ms Γ (C[[ e ]]) tyC) :
    ∃ tyE tyC', HasType CT ms Γ e tyE ∧ CtxHasType CT ms Γ tyE C tyC' ∧
      Subtype tyC' tyC := by
  induction C generalizing tyC with
  | hole =>
    exact ⟨tyC, tyC, hCtxExpr, CtxHasType.hole _ _, Subtype.refl _⟩
  | seqL C' e2 ih =>
    obtain ⟨A1, A2, h1, h2, hSub⟩ := seq_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    exact ⟨tyE, A2, hE, CtxHasType.seqL _ _ _ _ _ _ hCtx h2, hSub⟩
  | iteC C' e1 e2 ih =>
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    exact ⟨tyE, A2 ⊔ₜ A3, hE, CtxHasType.iteC _ _ _ _ _ _ _ _ hCtx h2 h3, hSub⟩
  | eqL C' e2 ih =>
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    exact ⟨tyE, ClassId.bool_id, hE, CtxHasType.eqL _ _ _ _ _ _ hCtx h2, hSub⟩
  | eqR v C' ih =>
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h2
    exact ⟨tyE, ClassId.bool_id, hE, CtxHasType.eqR _ _ _ _ _ _ h1 hCtx, hSub⟩
  | callL C' m e2 ih =>
    obtain ⟨Arecv, Aarg, A1, A2, h0, h1, hCT, hArgSub, hResSub, hUser⟩ :=
      call_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h0
    have hCtxRecv := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, A2, hE,
      CtxHasType.callL _ _ Arecv _ _ Aarg _ _ _ hCtxRecv h1 hUser hCT hArgSub,
      hResSub⟩
  | callR v m C' ih =>
    obtain ⟨Arecv, Aarg, A1, A2, h0, h1, hCT, hArgSub, hResSub, hUser⟩ :=
      call_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, A2, hE,
      CtxHasType.callR _ _ Arecv _ _ Aarg _ _ _ h0 hCtxArg hUser hCT hArgSub,
      hResSub⟩
  | checkedCallL Ares C' m e2 ih =>
    obtain ⟨Arec, Aarg, h0, h1, hSub, hLib⟩ := checked_call_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h0
    have hCtxRecv := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, Ares, hE,
      CtxHasType.checkedCallL _ _ Arec _ Aarg _ _ _ hCtxRecv h1 hLib, hSub⟩
  | checkedCallR Ares v m C' ih =>
    obtain ⟨Arec, Aarg, h0, h1, hSub, hLib⟩ := checked_call_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, Ares, hE,
      CtxHasType.checkedCallR _ _ Arec Aarg _ _ _ _ h0 hCtxArg hLib, hSub⟩
  | broadcastL C' e2 ih =>
    obtain ⟨s1, s2, sOut, hb, h1, h2, hSub⟩ := broadcast_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    have hCtxRecv := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id sOut, hE,
      CtxHasType.broadcastL _ _ _ _ _ _ _ hb hCtxRecv h2, hSub⟩
  | broadcastR v C' ih =>
    obtain ⟨s1, s2, sOut, hb, h1, h2, hSub⟩ := broadcast_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h2
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id sOut, hE,
      CtxHasType.broadcastR _ _ _ _ _ _ _ hb h1 hCtxArg, hSub⟩
  | matmulL C' e2 ih =>
    obtain ⟨b1, b2, bo, m, k, n, hb, h1, h2, hSub⟩ := matmul_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h1
    have hCtxRecv := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id (bo ++ [m, n]), hE,
      CtxHasType.matmulL _ _ _ _ _ _ _ _ _ _ hb hCtxRecv h2, hSub⟩
  | matmulR v C' ih =>
    obtain ⟨b1, b2, bo, m, k, n, hb, h1, h2, hSub⟩ := matmul_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h2
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id (bo ++ [m, n]), hE,
      CtxHasType.matmulR _ _ _ _ _ _ _ _ _ _ hb h1 hCtxArg, hSub⟩

/-
Lemma 2 (Substitution).
-/
theorem substitution_lemma
    {Δ : TypEnv} {C : Ctx} {e : Expr} {tyHole tyCtx tyE : ClassId}
    (hCtx : CtxHasType CT ms Δ tyHole C tyCtx)
    (hExpr : HasType CT ms Δ e tyE)
    (hSub : Subtype tyE tyHole) :
    ∃ tyCtx', HasType CT ms Δ (C[[ e ]]) tyCtx' ∧ Subtype tyCtx' tyCtx := by
  have hExprHole : HasType CT ms Δ e tyHole := HasType.tSub _ _ _ _ hExpr hSub
  suffices h : HasType CT ms Δ (C[[e]]) tyCtx from ⟨tyCtx, h, Subtype.refl _⟩
  induction hCtx <;> simp only [Ctx.fill] at * <;>
    first
    | exact hExprHole
    | (apply HasType.tApp <;> assumption)
    | (apply HasType.tSeq <;> assumption)
    | (apply HasType.tIf <;> assumption)
    | (apply HasType.tEq <;> assumption)
    | (apply HasType.tAppLib <;> assumption)
    | (apply HasType.tBroadcast <;> assumption)
    | (apply HasType.tMatmul <;> assumption)
    | (apply HasType.tSub <;> assumption)

/-! ## Main theorems -/

def LibTermination (libImpl : MethKey → Val → Val → Option Val)
    (ms : MethodSets) : Prop :=
  ∀ key v1 v2, key ∈ ms.library → ∃ v', libImpl key v1 v2 = some v'

/-
If a non-value expression can step or blame, wrapping it in a context preserves this.

When a non-value, non-user-call expression steps, either the stack is preserved
    (and we can use eContext), or the step is eAppUD with some context C_inner
    (and we can use eAppUD with composed context).
-/
private theorem progress_in_context_nonCall
    {E : DynEnv} {C : Ctx} {e : Expr} {S : Stack}
    {E' : DynEnv} {e' : Expr} {S' : Stack}
    (h : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩))
    (hNotCall : ¬ isUserMethodCall e ms)
    (hNotVal : e.isVal = false)
    (hValid : ValidCT CT ms methodDefs) :
    (∃ E'' e'' S'', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E'', e'', S''⟩)) := by
  -- In this case, e is a user method call, so we can use the fact that C is a context to construct the required step.
  cases' h with h_case h_case;
  all_goals try cases hNotVal;
  all_goals try { exact ⟨ _, _, _, Step.eContext _ _ _ _ _ _ ( by tauto ) hNotCall ( by tauto ) ⟩ };
  · exact ⟨ _, _, _, Step.eContext _ _ _ _ _ _ ( Step.eIfFalse _ _ _ _ _ ‹_› ) hNotCall ( by tauto ) ⟩;
  · use E, C[[Expr.val Val.false_]], S;
    exact Step.eContext _ _ _ _ _ _ ( by tauto ) hNotCall ( by tauto );
  · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
    rename_i C' vr v m;
    use (emptyEnv [VarId.self_id ↦ vr]) [h₁ ↦ v], h₂.body, (E, C.compose C') :: S;
    convert Step.eAppUD _ _ _ _ _ _ _ _ _ _ _ _ _ using 1;
    rw [ Ctx.compose_fill ];
    exacts [ h₂, h₃, h₄, h₅, rfl ]

theorem progress_in_context
    {E : DynEnv} {C : Ctx} {e : Expr} {S : Stack}
    (hNotVal : e.isVal = false)
    (hProgress : (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩)) ∨
                 (Step methodDefs libImpl ms ⟨E, e, S⟩ .blame))
    (hValid : ValidCT CT ms methodDefs) :
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ .blame) := by
  rcases hProgress with ( ⟨ E', e', S', h ⟩ | h );
  · by_cases hUserCall : isUserMethodCall e ms;
    · obtain ⟨vr, v, m', hEq, hUserMeth⟩ : ∃ vr v m', e = Expr.call (Expr.val vr) m' (Expr.val v) ∧ ⟨vr.typeOf, m'⟩ ∈ ms.userDefined := by
        exact?;
      obtain ⟨a1, a2, hCT, md, hDef, hBody⟩ : ∃ a1 a2, CT vr.typeOf m' = some ⟨a1, a2⟩ ∧ ∃ md, methodDefs ⟨vr.typeOf, m'⟩ = some md ∧ ∃ a2', HasType CT ms ((emptyEnv [VarId.self_id ↦ vr.typeOf]) [md.param ↦ a1]) md.body a2' ∧ a2' ≤ₜ a2 := by
        exact hValid.1 _ hUserMeth |> fun ⟨ a1, a2, hCT, md, hDef, hBody ⟩ => ⟨ a1, a2, hCT, md, hDef, hBody ⟩;
      left; use (emptyEnv [VarId.self_id ↦ vr]) [md.param ↦ v], md.body, (E, C) :: S; rw [hEq]; exact Step.eAppUD E C vr v m' S md.param md.body md hUserMeth hDef rfl rfl;
    · -- ¬isUserMethodCall: need to check if step preserves stack
      -- The step h could be eAppUD(C_inner ≠ hole) which changes the stack
      -- In that case, use eAppUD with composed context C ∘ C_inner
      -- Otherwise, use modified eContext (which requires same stack)
      exact Or.inl (progress_in_context_nonCall h hUserCall hNotVal hValid);
  · exact Or.inr ( Step.eBlameContext E C e S h )

/-- Helper for compound expression cases in progress: if a subexpression
    e1 satisfies progress, and the whole expression is C[[e1]], then the
    whole expression satisfies progress. -/
theorem progress_subexpr
    {E : DynEnv} {C : Ctx} {e1 : Expr} {S : Stack}
    (hProg1 : (∃ v, e1 = Expr.val v) ∨
              (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e1, S⟩ (.config ⟨E', e', S'⟩)) ∨
              (Step methodDefs libImpl ms ⟨E, e1, S⟩ .blame))
    (hValid : ValidCT CT ms methodDefs)
    (hValCase : ∀ v, e1 = Expr.val v →
      (∃ E' e' S', Step methodDefs libImpl ms ⟨E, C[[Expr.val v]], S⟩ (.config ⟨E', e', S'⟩)) ∨
       Step methodDefs libImpl ms ⟨E, C[[Expr.val v]], S⟩ .blame) :
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, C[[e1]], S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, C[[e1]], S⟩ .blame) := by
  rcases hProg1 with ⟨v, rfl⟩ | hStep | hBlame
  · exact hValCase v rfl
  · cases hv : e1.isVal
    · exact progress_in_context hv (Or.inl hStep) hValid
    · -- e1 is a value but also can step
      obtain ⟨v, rfl⟩ : ∃ v, e1 = Expr.val v := by
        cases e1 <;> simp [Expr.isVal] at hv; exact ⟨_, rfl⟩
      exact hValCase v rfl
  · cases hv : e1.isVal
    · exact progress_in_context hv (Or.inr hBlame) hValid
    · obtain ⟨v, rfl⟩ : ∃ v, e1 = Expr.val v := by
        cases e1 <;> simp [Expr.isVal] at hv; exact ⟨_, rfl⟩
      exact hValCase v rfl

/-- Progress (core version without TypeSubStack/StackConsistent). -/
theorem progress_core
    {Γ : TypEnv} {E : DynEnv} {e : Expr}
    {ty : ClassId} {S : Stack}
    (hType : HasType CT ms Γ e ty)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hValid : ValidCT CT ms methodDefs)
    (hLibTerm : LibTermination libImpl ms) :
    (∃ v, e = Expr.val v) ∨
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, e, S⟩ .blame) := by
  induction hType generalizing E S with
  | tNil => left; exact ⟨_, rfl⟩
  | tObj => left; exact ⟨_, rfl⟩
  | tTrue => left; exact ⟨_, rfl⟩
  | tFalse => left; exact ⟨_, rfl⟩
  | tType => left; exact ⟨_, rfl⟩
  | tBlame => left; exact ⟨_, rfl⟩
  | tTensor => left; exact ⟨_, rfl⟩
  | tSelf A hSelf =>
    right; left
    obtain ⟨v, hv⟩ := (hEnvCons.1 VarId.self_id).mpr ⟨_, hSelf⟩
    exact ⟨E, Expr.val v, S, Step.eSelf E S v hv⟩
  | tTSelf A hTSelf =>
    right; left
    obtain ⟨v, hv⟩ := (hEnvCons.1 VarId.tself_id).mpr ⟨_, hTSelf⟩
    exact ⟨E, Expr.val v, S, Step.eTSelf E S v hv⟩
  | tVar x A hVar =>
    right; left
    obtain ⟨v, hv⟩ := (hEnvCons.1 _).mpr ⟨_, hVar⟩
    exact ⟨E, Expr.val v, S, Step.eVar E _ S v hv⟩
  | tNew => right; left; exact ⟨E, Expr.val (Val.obj _), S, Step.eNew E _ S⟩
  | tSub _ _ _ _ _ ih => exact ih hEnvCons
  | tSeq _ _ _ _ _ _ ih1 _ =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.seqL Ctx.hole _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v _ => Or.inl ⟨E, _, S, Step.eSeq E v _ S⟩)
  | tIf _ _ _ _ _ _ _ _ _ ih1 _ _ =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.iteC Ctx.hole _ _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v _ => by
        cases ht : v.isTruthy
        · exact Or.inl ⟨E, _, S, Step.eIfFalse E v _ _ S ht⟩
        · exact Or.inl ⟨E, _, S, Step.eIfTrue E v _ _ S ht⟩)
  | tEq _ _ _ _ _ _ ih1 ih2 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.eqL Ctx.hole _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v1 _ => by
        show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.eqR v1 Ctx.hole)[[_]], S⟩ _) ∨ _
        exact progress_subexpr (ih2 hEnvCons) hValid
          (fun v2 _ => by
            cases he : Val.equiv v1 v2
            · exact Or.inl ⟨E, _, S, Step.eEqFalse E v1 v2 S he⟩
            · exact Or.inl ⟨E, _, S, Step.eEqTrue E v1 v2 S he⟩))
  | tApp _ _ _ _ _ _ _ h0 h1 hUser _ _ ih0 ih1 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.callL Ctx.hole _ _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih0 hEnvCons) hValid
      (fun v0 hv0 => by
        subst hv0
        show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.callR v0 _ Ctx.hole)[[_]], S⟩ _) ∨ _
        exact progress_subexpr (ih1 hEnvCons) hValid
          (fun v1 _ => by
            have hSub0 := val_type_subtype h0
            have hUserRT := hValid.2.2.2.1 _ _ _ hSub0 hUser
            obtain ⟨_, _, _, md, hDef, _⟩ := hValid.1 _ hUserRT
            exact Or.inl ⟨_, _, _, Step.eAppUD E Ctx.hole v0 v1 _ S md.param md.body md hUserRT hDef rfl rfl⟩))
  | tAppLib _ _ _ Ares _ _ h0 h1 hLib ih0 ih1 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.checkedCallL Ares Ctx.hole _ _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih0 hEnvCons) hValid
      (fun v0 hv0 => by
        subst hv0
        show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.checkedCallR Ares v0 _ Ctx.hole)[[_]], S⟩ _) ∨ _
        exact progress_subexpr (ih1 hEnvCons) hValid
          (fun v1 hv1 => by
            subst hv1
            have hSub0 := val_type_subtype h0
            have hLibRT := hValid.2.2.2.2 _ _ _ hSub0 hLib
            obtain ⟨v', hCall⟩ := hLibTerm _ v0 v1 hLibRT
            by_cases hc : v'.typeOf ≤ₜ Ares
            · exact Or.inl ⟨_, _, _, Step.eAppLib E Ares v0 v1 v' _ S hLibRT hCall hc⟩
            · exact Or.inr (Step.eBlameCheckedCall E Ares v0 v1 v' _ S hLibRT hCall hc)))
  | tBroadcast _ _ _ _ _ hBcast h1 h2 ih1 ih2 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.broadcastL Ctx.hole _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v1 hv1 => by
        subst hv1
        show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.broadcastR v1 Ctx.hole)[[_]], S⟩ _) ∨ _
        exact progress_subexpr (ih2 hEnvCons) hValid
          (fun v2 hv2 => by
            subst hv2
            by_cases hm : ∃ s1 s2 sOut, v1 = Val.tensor s1 ∧ v2 = Val.tensor s2 ∧
                broadcastShapes s1 s2 = some sOut
            · obtain ⟨s1', s2', sOut', rfl, rfl, hb'⟩ := hm
              exact Or.inl ⟨_, _, _, Step.eBroadcast E s1' s2' sOut' S hb'⟩
            · exact Or.inr (Step.eBlameBroadcast E v1 v2 S hm)))
  | tMatmul _ _ _ _ _ _ _ _ hBatch h1 h2 ih1 ih2 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.matmulL Ctx.hole _)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v1 hv1 => by
        subst hv1
        show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.matmulR v1 Ctx.hole)[[_]], S⟩ _) ∨ _
        exact progress_subexpr (ih2 hEnvCons) hValid
          (fun v2 hv2 => by
            subst hv2
            by_cases hm : ∃ batch1 batch2 batchOut m k n,
                broadcastShapes batch1 batch2 = some batchOut ∧
                v1 = Val.tensor (batch1 ++ [m, k]) ∧
                v2 = Val.tensor (batch2 ++ [k, n])
            · obtain ⟨b1, b2, bo, m', k', n', hb', rfl, rfl⟩ := hm
              exact Or.inl ⟨_, _, _, Step.eMatmul E b1 b2 bo m' k' n' S hb'⟩
            · exact Or.inr (Step.eBlameMatmul E v1 v2 S hm)))

theorem ctx_weakening
    {Γ Δ : TypEnv} {C : Ctx} {tyHole tyCtx : ClassId}
    (hCtx : CtxHasType CT ms Γ tyHole C tyCtx)
    (hExt : TypEnv.extends_ Γ Δ) :
    CtxHasType CT ms Δ tyHole C tyCtx := by
  -- Apply the induction hypothesis to the recursive context.
  have h_ind : ∀ {Γ Δ : TypEnv} {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → Γ.extends_ Δ → HasType CT ms Δ e ty := by
    exact?;
  induction' hCtx with Γ tyHole C tyCtx hCtx hExt generalizing Δ;
  all_goals constructor <;> tauto;

/-- Type preservation for same-stack steps (no TypeSubStack needed). -/
private theorem preservation_same_stack
    {c : Config} {r : StepResult}
    (hStep : Step methodDefs libImpl ms c r) :
    ∀ {Γ : TypEnv} {E E' : DynEnv} {e e' : Expr}
      {ty : ClassId} {S : Stack},
    c = ⟨E, e, S⟩ → r = .config ⟨E', e', S⟩ →
    HasType CT ms Γ e ty →
    EnvConsistent CT ms Γ E →
    ValidCT CT ms methodDefs →
    ∃ (Δ : TypEnv) (ty' : ClassId),
      HasType CT ms Δ e' ty' ∧
      EnvConsistent CT ms Δ E' ∧
      Subtype ty' ty ∧ TypEnv.extends_ Γ Δ := by
  induction hStep with
  | eVar E_v x S_v v hx =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := var_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 x v hx
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eSelf E_v S_v v hself =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := self_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v hself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eTSelf E_v S_v v htself =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := tself_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v htself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eSeq E_v v_v e_v S_v =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := seq_inversion hType
    exact ⟨Γ, A2, h2, hEnvCons, hSub, fun x a h => h⟩
  | eNew E_v A S_v =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    have hSub := new_inversion hType
    exact ⟨Γ, A, HasType.tObj Γ A, hEnvCons, hSub, fun x a h => h⟩
  | eIfTrue E_v v e2 e3 S_v htruthy =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A2, h2, hEnvCons,
      Subtype.trans (Subtype.lub_left A2 A3) hSub, fun x a h => h⟩
  | eIfFalse E_v v e2 e3 S_v hfalsy =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A3, h3, hEnvCons,
      Subtype.trans (Subtype.lub_right A2 A3) hSub, fun x a h => h⟩
  | eEqTrue E_v v1 v2 S_v heq =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, ClassId.true_id, HasType.tTrue Γ, hEnvCons,
      Subtype.trans Subtype.true_bool hSub, fun x a h => h⟩
  | eEqFalse E_v v1 v2 S_v hneq =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, ClassId.false_id, HasType.tFalse Γ, hEnvCons,
      Subtype.trans Subtype.false_bool hSub, fun x a h => h⟩
  | eAppUD E_v C_v vr v m S_v x body md hUserMethod hDef hParam hBody =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; exact absurd hr (by simp)
  | eAppLib E_v Ares vr v v' m S_v hLibMethod hCall hSubtype_v =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨Arec, Aarg, h0, h1, hSub, hLib⟩ := checked_call_inversion hType
    exact ⟨Γ, v'.typeOf, val_has_type Γ v', hEnvCons,
      Subtype.trans hSubtype_v hSub, fun x a h => h⟩
  | eRet E'_v E_v v C_v S_v =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; exact absurd hr (by simp)
  | eContext E_v E'_v C_v e_v e'_v S_v hStep_inner hNotUserCall hNotVal ih =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨tyE, tyC', hTypeE, hCtxType, hSubCtx⟩ := ctx_decomposition hType
    obtain ⟨Δ, ty'_inner, hType', hEnvCons', hSubTy, hExt⟩ :=
      ih rfl rfl hTypeE hEnvCons hValid
    have hCtxW := ctx_weakening hCtxType hExt
    obtain ⟨tyCtx', hTypeCtx, hSubCtxNew⟩ := substitution_lemma hCtxW hType' hSubTy
    exact ⟨Δ, tyCtx', hTypeCtx, hEnvCons',
      Subtype.trans hSubCtxNew hSubCtx, hExt⟩
  | eBroadcast E_v s1 s2 sOut S_v hBcast =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨s1', s2', sOut', hb', h1, h2, hSub⟩ := broadcast_inversion hType
    have hValSub1 := val_type_subtype h1
    have hValSub2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hValSub1
    have heq2 := tensor_id_subtype_implies_eq hValSub2
    subst heq1; subst heq2
    rw [hBcast] at hb'; cases hb'
    exact ⟨Γ, (Val.tensor sOut).typeOf, val_has_type Γ (Val.tensor sOut), hEnvCons,
      hSub, fun x a h => h⟩
  | eMatmul E_v batch1 batch2 batchOut m k n S_v hBatch =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨b1', b2', bo', m', k', n', hb', h1, h2, hSub⟩ := matmul_inversion hType
    have hVS1 := val_type_subtype h1
    have hVS2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hVS1
    have heq2 := tensor_id_subtype_implies_eq hVS2
    have hl1 : batch1.length = b1'.length := by
      have := congr_arg List.length heq1; simp at this; omega
    have hl2 : batch2.length = b2'.length := by
      have := congr_arg List.length heq2; simp at this; omega
    have hpair1 := List.append_inj heq1 hl1
    have hpair2 := List.append_inj heq2 hl2
    have hb1eq : batch1 = b1' := hpair1.1
    have hb2eq : batch2 = b2' := hpair2.1
    have hmk : [m, k] = [m', k'] := hpair1.2
    have hkn : [k, n] = [k', n'] := hpair2.2
    have hm : m = m' := by have := List.cons.inj hmk; exact this.1
    have hn : n = n' := by have := List.cons.inj hkn; have := List.cons.inj this.2; exact this.1
    subst hb1eq; subst hb2eq; subst hm; subst hn
    rw [hBatch] at hb'; cases hb'
    exact ⟨Γ, (Val.tensor (batchOut ++ [m, n])).typeOf,
      val_has_type Γ (Val.tensor (batchOut ++ [m, n])), hEnvCons,
      hSub, fun x a h => h⟩
  | eBlameNilRecv => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameCheckedCall => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameBroadcast => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameMatmul => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameContext => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)

private theorem preservation_eAppUD
    {Γ : TypEnv} {E : DynEnv} {C : Ctx} {vr v : Val}
    {m : MethId} {S : Stack} {ty : ClassId} {TS : TypeStack}
    {x : VarId} {body : Expr} {md : MethDef}
    (hType : HasType CT ms Γ (C[[ Expr.call (Expr.val vr) m (Expr.val v) ]]) ty)
    (hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hStackCons : StackConsistent CT ms TS S)
    (hValid : ValidCT CT ms methodDefs)
    (hUserMethod : ⟨vr.typeOf, m⟩ ∈ ms.userDefined)
    (hDef : methodDefs ⟨vr.typeOf, m⟩ = some md)
    (hParam : md.param = x)
    (hBody : md.body = body) :
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ body ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ ((emptyEnv [VarId.self_id ↦ vr]) [x ↦ v]) ∧
      StackConsistent CT ms TS' ((E, C) :: S) ∧
      (S = (E, C) :: S → Subtype ty' ty ∧ TypEnv.extends_ Γ Δ) := by
  obtain ⟨tyE, tyC', hCtxE, hCtxC', hSubC⟩ : ∃ tyE tyC', HasType CT ms Γ (Expr.call (Expr.val vr) m (Expr.val v)) tyE ∧ CtxHasType CT ms Γ tyE C tyC' ∧ Subtype tyC' ty := by
    exact?;
  obtain ⟨Arecv, Aarg, A1, A2, hArecv, hAarg, hA1, hA2, hSubA⟩ : ∃ Arecv Aarg A1 A2, HasType CT ms Γ (Expr.val vr) Arecv ∧ HasType CT ms Γ (Expr.val v) Aarg ∧ CT Arecv m = some ⟨A1, A2⟩ ∧ Subtype Aarg A1 ∧ Subtype A2 tyE ∧ ⟨Arecv, m⟩ ∈ ms.userDefined := by
    exact?;
  have hValType : vr.typeOf ≤ₜ Arecv := by
    exact?;
  have := hValid.1 ⟨vr.typeOf, m⟩ hUserMethod; simp_all +decide ;
  obtain ⟨ a1, a2, h1, a2', h2, h3 ⟩ := this; use ( emptyEnv[VarId.self_id ↦ vr.typeOf][x ↦ a1] ), ⟨ Γ, tyE, tyC' ⟩ :: TS, a2'; simp_all +decide ;
  constructor;
  · exact Subtype.trans h3 ( by
      have := hValid.2.2.1 Arecv vr.typeOf m; simp_all +decide ;
      exact Subtype.trans this.2 hSubA.1 );
  · constructor;
    · constructor;
      · intro y; by_cases hy : y = VarId.self_id <;> by_cases hy' : y = x <;> simp +decide [ hy, hy', emptyEnv, envUpdate ] ;
        · aesop;
        · aesop;
      · intro x v hv; by_cases hx : x = VarId.self_id <;> by_cases hx' : x = x <;> simp_all +decide [ emptyEnv, envUpdate ] ;
        · split_ifs at hv <;> simp_all +decide [ VarId.self_id ];
          · have hValType : v.typeOf ≤ₜ Aarg := by
              exact?;
            have hValType : v.typeOf ≤ₜ a1 := by
              have := hValid.2.2.1 Arecv vr.typeOf m; simp_all +decide [ Subtype ] ;
              exact Subtype.trans hValType ( Subtype.trans hA2 this.1 );
            exact ⟨ v.typeOf, val_has_type _ _, hValType ⟩;
          · exact ⟨ v.typeOf, val_has_type _ _, by tauto ⟩;
        · have := hValid.2.2.1 Arecv vr.typeOf m A1 A2 a1 a2; simp_all +decide [ Subtype ] ;
          exact ⟨ v.typeOf, val_has_type _ _, val_type_subtype hAarg |> fun h => by
            exact Subtype.trans h ( Subtype.trans hA2 this.1 ) ⟩;
    · constructor;
      · assumption;
      · assumption;
      · assumption;
      · cases TS <;> tauto

private theorem preservation_eContext
    {Γ : TypEnv} {E E' : DynEnv} {C : Ctx} {e_inner e'_inner : Expr}
    {S : Stack} {ty : ClassId} {TS : TypeStack}
    (hType : HasType CT ms Γ (C[[ e_inner ]]) ty)
    (hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hStackCons : StackConsistent CT ms TS S)
    (hValid : ValidCT CT ms methodDefs)
    (hStep_inner : Step methodDefs libImpl ms ⟨E, e_inner, S⟩ (.config ⟨E', e'_inner, S⟩))
    (hNotVal : e_inner.isVal = false)
    (hNotUserCall : ¬ isUserMethodCall e_inner ms)
    (ih : ∀ {Γ' : TypEnv} {E1 E1' : DynEnv} {e1 e1' : Expr}
      {ty1 : ClassId} {S1 S1' : Stack} {TS1 : TypeStack},
      (Config.mk E e_inner S) = (Config.mk E1 e1 S1) →
      (StepResult.config (Config.mk E' e'_inner S)) = (StepResult.config (Config.mk E1' e1' S1')) →
      HasType CT ms Γ' e1 ty1 →
      TypeSubStack ty1 TS1 →
      EnvConsistent CT ms Γ' E1 →
      StackConsistent CT ms TS1 S1 →
      ValidCT CT ms methodDefs →
      ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
        HasType CT ms Δ e1' ty' ∧
        TypeSubStack ty' TS' ∧
        EnvConsistent CT ms Δ E1' ∧
        StackConsistent CT ms TS' S1' ∧
        (S1 = S1' → Subtype ty' ty1 ∧ TypEnv.extends_ Γ' Δ)) :
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ (C[[ e'_inner ]]) ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ E' ∧
      StackConsistent CT ms TS' S ∧
      (Subtype ty' ty ∧ TypEnv.extends_ Γ Δ) := by
  -- Case split on whether C is the hole context
  by_cases hC : C = Ctx.hole
  · -- C = hole: C[[e_inner]] = e_inner, C[[e'_inner]] = e'_inner
    subst hC; simp [Ctx.fill] at *
    have h := ih rfl rfl rfl rfl rfl rfl hType hSubStack hEnvCons hStackCons hValid
    obtain ⟨Δ, TS', ty', hT, hSS', hEC, hSC, hImp⟩ := h
    exact ⟨Δ, TS', ty', hT, hSS', hEC, hSC, (hImp rfl).1, (hImp rfl).2⟩
  · -- C ≠ hole: use preservation_same_stack for the inner step
    obtain ⟨tyE, tyC', hTypeE, hCtxType, hSubCtx⟩ := ctx_decomposition hType
    obtain ⟨Δ, ty'_inner, hType', hEnvCons', hSubTy, hExt⟩ :=
      preservation_same_stack hStep_inner rfl rfl hTypeE hEnvCons hValid
    -- Weaken context typing from Γ to Δ and reconstruct
    have hCtxW := ctx_weakening hCtxType hExt
    obtain ⟨tyCtx', hTypeCtx, hSubCtxNew⟩ := substitution_lemma hCtxW hType' hSubTy
    refine ⟨Δ, TS, tyCtx', hTypeCtx, ?_, hEnvCons', hStackCons, ?_⟩
    · -- TypeSubStack tyCtx' TS
      cases TS with
      | nil => trivial
      | cons ts rest =>
        exact Subtype.trans (Subtype.trans hSubCtxNew hSubCtx) hSubStack
    · exact ⟨Subtype.trans hSubCtxNew hSubCtx, hExt⟩

/-- Theorem A.1 (Preservation) - generalized for induction. -/
private theorem preservation_gen
    {c : Config} {r : StepResult}
    (hStep : Step methodDefs libImpl ms c r) :
    ∀ {Γ : TypEnv} {E E' : DynEnv} {e e' : Expr}
      {ty : ClassId} {S S' : Stack} {TS : TypeStack},
    c = ⟨E, e, S⟩ → r = .config ⟨E', e', S'⟩ →
    HasType CT ms Γ e ty →
    TypeSubStack ty TS →
    EnvConsistent CT ms Γ E →
    StackConsistent CT ms TS S →
    ValidCT CT ms methodDefs →
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ e' ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ E' ∧
      StackConsistent CT ms TS' S' ∧
      (S = S' → Subtype ty' ty ∧ TypEnv.extends_ Γ Δ) := by
  induction hStep with
  | eVar E_v x S_v v hx =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := var_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 x v hx
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eSelf E_v S_v v hself =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := self_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v hself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eTSelf E_v S_v v htself =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := tself_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v htself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eSeq E_v v_v e_v S_v =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := seq_inversion hType
    exact ⟨Γ, TS, A2, h2,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eNew E_v A S_v =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    have hSub := new_inversion hType
    exact ⟨Γ, TS, A, HasType.tObj Γ A,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eIfTrue E_v v e2 e3 S_v htruthy =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, TS, A2, h2,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans (Subtype.lub_left A2 A3) hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans (Subtype.lub_left A2 A3) hSub, fun x a h => h⟩⟩
  | eIfFalse E_v v e2 e3 S_v hfalsy =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, TS, A3, h3,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans (Subtype.lub_right A2 A3) hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans (Subtype.lub_right A2 A3) hSub, fun x a h => h⟩⟩
  | eEqTrue E_v v1 v2 S_v heq =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, TS, ClassId.true_id, HasType.tTrue Γ,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans Subtype.true_bool hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans Subtype.true_bool hSub, fun x a h => h⟩⟩
  | eEqFalse E_v v1 v2 S_v hneq =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, TS, ClassId.false_id, HasType.tFalse Γ,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans Subtype.false_bool hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans Subtype.false_bool hSub, fun x a h => h⟩⟩
  | eAppUD E_v C_v vr v m S_v x body md hUserMethod hDef hParam hBody =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    exact preservation_eAppUD hType hSubStack hEnvCons hStackCons hValid hUserMethod hDef hParam hBody
  | eAppLib E_v Ares vr v v' m S_v hLibMethod hCall hSubtype_v =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨Arec, Aarg, h0, h1, hSub, hLib⟩ := checked_call_inversion hType
    exact ⟨Γ, TS, v'.typeOf, val_has_type Γ v',
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans hSubtype_v hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans hSubtype_v hSub, fun x a h => h⟩⟩
  | eRet E'_v E_v v C_v S_v =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    cases hStackCons with
    | cons Γ_s retTy ctxTy E_s C_s TS_rest S_rest hEnvCons_s hCtxType_s hRest hSubStack_s =>
      have hValType : HasType CT ms Γ_s (Expr.val v) v.typeOf := val_has_type Γ_s v
      have hValSub : v.typeOf ≤ₜ ty := val_type_subtype hType
      have hValSubRet : v.typeOf ≤ₜ retTy := Subtype.trans hValSub hSubStack
      obtain ⟨tyCtx', hTypeCtx, hSubCtx⟩ := substitution_lemma hCtxType_s hValType hValSubRet
      refine ⟨Γ_s, TS_rest, tyCtx', hTypeCtx, ?_, hEnvCons_s, hRest, ?_⟩
      · cases hSubStack_s with
        | inl h => subst h; trivial
        | inr h =>
          cases TS_rest with
          | nil => trivial
          | cons ts rest => exact Subtype.trans hSubCtx h
      · intro heq; exact absurd heq (by simp)
  | eContext E_v E'_v C_v e_v e'_v S_v hStep_inner hNotUserCall hNotVal ih =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨Δ, TS', ty', h1, h2, h3, h4, h5, h6⟩ := preservation_eContext hType hSubStack hEnvCons hStackCons hValid hStep_inner hNotVal hNotUserCall ih
    exact ⟨Δ, TS', ty', h1, h2, h3, h4, fun _ => ⟨h5, h6⟩⟩
  | eBroadcast E_v s1 s2 sOut S_v hBcast =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨s1', s2', sOut', hb', h1, h2, hSub⟩ := broadcast_inversion hType
    have hValSub1 := val_type_subtype h1
    have hValSub2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hValSub1
    have heq2 := tensor_id_subtype_implies_eq hValSub2
    subst heq1; subst heq2
    rw [hBcast] at hb'; cases hb'
    exact ⟨Γ, TS, (Val.tensor sOut).typeOf, val_has_type Γ (Val.tensor sOut),
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eMatmul E_v batch1 batch2 batchOut m k n S_v hBatch =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨b1', b2', bo', m', k', n', hb', h1, h2, hSub⟩ := matmul_inversion hType
    have hVS1 := val_type_subtype h1
    have hVS2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hVS1
    have heq2 := tensor_id_subtype_implies_eq hVS2
    have hl1 : batch1.length = b1'.length := by
      have := congr_arg List.length heq1; simp at this; omega
    have hl2 : batch2.length = b2'.length := by
      have := congr_arg List.length heq2; simp at this; omega
    have hpair1 := List.append_inj heq1 hl1
    have hpair2 := List.append_inj heq2 hl2
    have hb1eq : batch1 = b1' := hpair1.1
    have hb2eq : batch2 = b2' := hpair2.1
    have hmk : [m, k] = [m', k'] := hpair1.2
    have hkn : [k, n] = [k', n'] := hpair2.2
    have hm : m = m' := by have := List.cons.inj hmk; exact this.1
    have hn : n = n' := by have := List.cons.inj hkn; have := List.cons.inj this.2; exact this.1
    subst hb1eq; subst hb2eq; subst hm; subst hn
    rw [hBatch] at hb'; cases hb'
    exact ⟨Γ, TS, (Val.tensor (batchOut ++ [m, n])).typeOf,
      val_has_type Γ (Val.tensor (batchOut ++ [m, n])),
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eBlameNilRecv E_v C_v m v S_v hNil =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    exact absurd hr (by simp [StepResult.config])
  | eBlameCheckedCall E_v Ares vr v v' m S_v hLibMethod hCall hNotSubtype =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    exact absurd hr (by simp [StepResult.config])
  | eBlameBroadcast E_v v1 v2 S_v hNotMatch =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    exact absurd hr (by simp [StepResult.config])
  | eBlameMatmul E_v v1 v2 S_v hNotMatch =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    exact absurd hr (by simp [StepResult.config])
  | eBlameContext E_v C_v e_v S_v hStep_inner =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    exact absurd hr (by simp [StepResult.config])
theorem preservation
    {Γ : TypEnv} {E E' : DynEnv} {e e' : Expr}
    {ty : ClassId} {S S' : Stack} {TS : TypeStack}
    (hStep : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩))
    (hType : HasType CT ms Γ e ty)
    (hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hStackCons : StackConsistent CT ms TS S)
    (hValid : ValidCT CT ms methodDefs) :
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ e' ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ E' ∧
      StackConsistent CT ms TS' S' ∧
      (S = S' → Subtype ty' ty ∧ TypEnv.extends_ Γ Δ) :=
  preservation_gen hStep rfl rfl hType hSubStack hEnvCons hStackCons hValid

/-- Theorem A.2 (Progress). -/
theorem progress
    {Γ : TypEnv} {E : DynEnv} {e : Expr}
    {ty : ClassId} {S : Stack} {TS : TypeStack}
    (hType : HasType CT ms Γ e ty)
    (_hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (_hStackCons : StackConsistent CT ms TS S)
    (hValid : ValidCT CT ms methodDefs)
    (hLibTerm : LibTermination libImpl ms) :
    (∃ v, e = Expr.val v) ∨
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, e, S⟩ .blame) :=
  progress_core hType hEnvCons hValid hLibTerm

/-- Theorem A.3 (Soundness of Type Checking). -/
theorem soundness_type_checking
    {e : Expr} {ty : ClassId}
    (hType : HasType CT ms emptyEnv e ty)
    (hValid : ValidCT CT ms methodDefs)
    (hLibTerm : LibTermination libImpl ms) :
    (∃ v, e = Expr.val v) ∨
    (∃ E' e' S', Step methodDefs libImpl ms ⟨emptyEnv, e, []⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨emptyEnv, e, []⟩ .blame) := by
  apply progress hType (show TypeSubStack ty [] from trivial)
  · constructor
    · intro x; constructor
      · intro ⟨v, hv⟩; simp [emptyEnv] at hv
      · intro ⟨a, ha⟩; simp [emptyEnv] at ha
    · intro x v hv; simp [emptyEnv] at hv
  · exact StackConsistent.nil
  · exact hValid
  · exact hLibTerm

/-- Theorem A.4 (Soundness of Check Insertion). -/
theorem soundness_check_insertion
    {e : Expr} {ty : ClassId}
    (hType : HasType CT ms emptyEnv e ty)
    (hValid : ValidCT CT ms methodDefs)
    (hLibTerm : LibTermination libImpl ms) :
    (∃ v, e = Expr.val v) ∨
    (∃ E' e' S', Step methodDefs libImpl ms ⟨emptyEnv, e, []⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨emptyEnv, e, []⟩ .blame) := by
  exact soundness_type_checking hType hValid hLibTerm

end LambdaC
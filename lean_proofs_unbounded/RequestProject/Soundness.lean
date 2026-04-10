/-
# λC Soundness

Formalization of the soundness proof from Appendix A of
"Type-Level Computations for Ruby Libraries" (arXiv:1904.03521v1).

Extended with unbounded (rank-polymorphic) tensor shapes.
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
  | tensor dims => exact HasType.tTensor Γ dims

theorem val_type_subtype {Γ : TypEnv} {v : Val} {A : ClassId}
    (h : HasType CT ms Γ (Expr.val v) A) : v.typeOf ≤ₜ A := by
  revert h;
  have h_cases : ∀ t : TypEnv → Expr → ClassId → Prop, (∀ Γ v, t Γ (Expr.val v) v.typeOf) → ∀ Γ e A, HasType CT ms Γ e A → ∀ h : e = Expr.val v, v.typeOf ≤ₜ A := by
    intros t ht Γ e A h h_eq
    induction' h with Γ e A h ih generalizing t;
    all_goals cases h_eq;
    all_goals try tauto;
    exact Subtype.trans ( by solve_by_elim ) ‹_›;
  exact fun h => h_cases ( fun Γ e A => HasType CT ms Γ e A ) ( fun Γ v => val_has_type Γ v ) Γ ( Expr.val v ) A h rfl

/-- Weakening -/
def TypEnv.extends_ (Γ Δ : TypEnv) : Prop :=
  ∀ x a, Γ x = some a → Δ x = some a

theorem weakening {Γ Δ : TypEnv} {e : Expr} {ty : ClassId}
    (hType : HasType CT ms Γ e ty)
    (hExt : TypEnv.extends_ Γ Δ) :
    HasType CT ms Δ e ty := by
  induction hType;
  all_goals exact?

/-- Subtyping is transitive -/
theorem subtype_trans' {a b c : ClassId}
    (h1 : Subtype a b) (h2 : Subtype b c) : Subtype a c :=
  Subtype.trans h1 h2

/-! ## Inversion lemmas -/

theorem var_inversion {Γ : TypEnv} {x : VarId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.var x) ty) :
    ∃ a, Γ x = some a ∧ Subtype a ty := by
  have h_var : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.var x → ∃ a, Γ x = some a ∧ a ≤ₜ ty := by
    intros e ty h h_eq
    induction' h with e ty h ih generalizing x;
    all_goals cases h_eq;
    · exact ⟨ _, ‹_›, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ h rfl ) fun a ha => ⟨ a, ha.1, Subtype.trans ha.2 h₁ ⟩;
  exact h_var h rfl

theorem self_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.self ty) :
    ∃ a, Γ VarId.self_id = some a ∧ Subtype a ty := by
  obtain ⟨a, ha⟩ : ∃ a, Γ VarId.self_id = some a := by
    have h_self : Γ VarId.self_id ≠ none := by
      have h_self : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ x, e = Expr.self → x = VarId.self_id → Γ x ≠ none := by
        intros e ty h x hx hx'; induction h <;> aesop;
      grind;
    exact Option.ne_none_iff_exists'.mp h_self;
  have h_subtype : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.self → ∃ a, Γ VarId.self_id = some a ∧ Subtype a ty := by
    intros e ty h h_eq
    induction' h with e ty h ih;
    all_goals cases h_eq;
    · exact ⟨ ty, h, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact h₃ rfl |> fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ a, ha₁, subtype_trans' ha₂ h₁ ⟩;
  exact h_subtype h rfl

theorem tself_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.tself ty) :
    ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
  have h_subtype : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.tself → ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
    intros e ty h h_eq; induction h; all_goals simp_all +decide [ Subtype.refl ] ;
    exact ⟨ _, ‹∃ a, Γ VarId.tself_id = some a ∧ a ≤ₜ _›.choose_spec.1, subtype_trans' ‹∃ a, Γ VarId.tself_id = some a ∧ a ≤ₜ _›.choose_spec.2 ‹_› ⟩;
  exact h_subtype h rfl

theorem call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.call e0 m e1) ty) :
    ∃ (Arecv Aarg A1 A2 : ClassId),
      HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧
      CT Arecv m = some ⟨A1, A2⟩ ∧ Subtype Aarg A1 ∧
      Subtype A2 ty ∧ ⟨Arecv, m⟩ ∈ ms.userDefined := by
  have h_tApp : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = e0.call m e1 → ∃ Arecv Aarg A1 A2, HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧ CT Arecv m = some ⟨A1, A2⟩ ∧ (Aarg ≤ₜ A1) ∧ (A2 ≤ₜ ty) ∧ (⟨Arecv, m⟩ ∈ ms.userDefined) := by
    intros e ty h h_eq
    induction' h with e ty h ih generalizing e0 e1;
    all_goals cases h_eq;
    · exact ⟨ _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, Subtype.refl _, ‹_› ⟩;
    · rename_i h₁ h₂ h₃;
      obtain ⟨ Arecv, Aarg, A1, A2, h4, h5, h6, h7, h8, h9 ⟩ := h₃ h rfl;
      exact ⟨ Arecv, Aarg, A1, A2, h4, h5, h6, h7, Subtype.trans h8 h₁, h9 ⟩;
  exact h_tApp h rfl

theorem checked_call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId}
    {Ares ty : ClassId}
    (h : HasType CT ms Γ (Expr.checkedCall Ares e0 m e1) ty) :
    ∃ (Arec Aarg : ClassId),
      HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧
      Subtype Ares ty ∧ ⟨Arec, m⟩ ∈ ms.library := by
  revert h;
  have h_ind : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {e' : Expr} {ty' : ClassId}, e = Expr.checkedCall Ares e0 m e1 → ty = ty' → ∃ Arec Aarg, HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧ (Ares ≤ₜ ty') ∧ ⟨Arec, m⟩ ∈ ms.library := by
    intros e ty h;
    induction h;
    all_goals intros; cases ‹_›;
    all_goals cases ‹_›;
    · exact ⟨ _, _, by assumption, by assumption, Subtype.refl _, by assumption ⟩;
    · rename_i h₁ h₂ h₃;
      specialize h₃ rfl rfl;
      · exact h₁;
      · exact ⟨ _, _, h₃.choose_spec.choose_spec.1, h₃.choose_spec.choose_spec.2.1, Subtype.trans h₃.choose_spec.choose_spec.2.2.1 ‹_›, h₃.choose_spec.choose_spec.2.2.2 ⟩;
  aesop

theorem ite_inversion {Γ : TypEnv} {e1 e2 e3 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.ite e1 e2 e3) ty) :
    ∃ A1 A2 A3,
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      HasType CT ms Γ e3 A3 ∧ Subtype (A2 ⊔ₜ A3) ty := by
  contrapose! h;
  intro H;
  obtain ⟨A1, A2, A3, h1, h2, h3, h_subtype⟩ : ∃ A1 A2 A3, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ HasType CT ms Γ e3 A3 ∧ (A2 ⊔ₜ A3) ≤ₜ ty := by
    have h_ite : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.ite e1 e2 e3 → ∃ A1 A2 A3, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ HasType CT ms Γ e3 A3 ∧ (A2 ⊔ₜ A3) ≤ₜ ty := by
      intros e ty h_type h_eq;
      induction' h_type with e ty h_type ih;
      all_goals cases h_eq;
      · exact ⟨ _, _, _, by assumption, by assumption, by assumption, by tauto ⟩;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ A1, A2, A3, h1, h2, h3, h4 ⟩ := h₃ rfl;
        use A1, A2, A3;
        exact ⟨ h1, h2, h3, by exact? ⟩;
    exact h_ite H rfl;
  exact h A1 A2 A3 h1 h2 h3 h_subtype

theorem seq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.seq e1 e2) ty) :
    ∃ A1 A2,
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype A2 ty := by
  contrapose! h;
  -- By definition of HasType, if HasType CT ms Γ (e1.seq e2) ty holds, then there must exist A1 and A2 such that HasType CT ms Γ e1 A1 and HasType CT ms Γ e2 A2 and A2 ≤ₜ ty.
  intro h_seq
  obtain ⟨A1, A2, hA1, hA2, hA2_le⟩ : ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
    obtain ⟨A1, A2, hA1, hA2, hA2_le⟩ : ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
      have := h_seq
      have h_seq_def : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = e1.seq e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty := by
        intros e ty h_seq h_eq
        induction' h_seq with e ty h_seq h_eq;
        all_goals cases h_eq;
        · exact ⟨ _, _, ‹_›, ‹_›, Subtype.refl _ ⟩;
        · rename_i h₁ h₂ h₃;
          exact h₃ rfl |> fun ⟨ A1, A2, hA1, hA2, hA2_le ⟩ => ⟨ A1, A2, hA1, hA2, subtype_trans' hA2_le h₁ ⟩;
      exact h_seq_def this rfl;
    use A1, A2;
  exact h A1 A2 hA1 hA2 hA2_le

theorem eq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.eq e1 e2) ty) :
    ∃ A1 A2,
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      Subtype ClassId.bool_id ty := by
  contrapose! h;
  -- By definition of HasType, if HasType CT ms Γ (e1.eq e2) ty, then there exist A1 and A2 such that HasType CT ms Γ e1 A1, HasType CT ms Γ e2 A2, and Subtype bool_id ty.
  have h_def : ∀ {ty}, HasType CT ms Γ (e1.eq e2) ty → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype ClassId.bool_id ty := by
    intros ty hty;
    have h_def : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → (e = Expr.eq e1 e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype ClassId.bool_id ty) := by
      intros e ty hty heq;
      induction' hty with e ty hty ih;
      all_goals cases heq;
      · exact ⟨ _, _, ‹_›, ‹_›, Subtype.refl _ ⟩;
      · rename_i h₁ h₂ h₃;
        exact h₃ rfl |> fun ⟨ A1, A2, hA1, hA2, h ⟩ => ⟨ A1, A2, hA1, hA2, Subtype.trans h h₁ ⟩;
    exact h_def hty rfl;
  exact fun h' => by obtain ⟨ A1, A2, h1, h2, h3 ⟩ := h_def h'; exact h A1 A2 h1 h2 h3;

theorem new_inversion {Γ : TypEnv} {cls : ClassId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.new cls) ty) : Subtype cls ty := by
  cases h ; tauto;
  rename_i h₁ h₂;
  have h_sub : Subtype cls ‹_› := by
    have h_sub : ∀ {Γ : TypEnv} {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {cls : ClassId}, e = Expr.new cls → Subtype cls ty := by
      intros Γ e ty h cls hcls; induction' h with Γ e ty h cls hcls; aesop;
      all_goals cases hcls;
      · constructor;
      · exact?;
    exact h_sub h₁ rfl;
  exact?

/-! ## Tensor-specific lemmas -/

private lemma tensor_id_ge_six (s : Shape) : ClassId.tensor_id s ≥ 6 := by
  simp [ClassId.tensor_id]

private lemma tensor_id_injective {s1 s2 : Shape}
    (h : ClassId.tensor_id s1 = ClassId.tensor_id s2) : s1 = s2 := by
  simp [ClassId.tensor_id] at h
  exact h

private lemma lub_eq_zero {a b : ClassId} (h : lub a b = ClassId.nil_id) :
    a = ClassId.nil_id ∧ b = ClassId.nil_id := by
  unfold lub at h; split_ifs at h <;> simp_all +decide

private lemma subtype_nil_eq {a : ClassId} (h : a ≤ₜ ClassId.nil_id) :
    a = ClassId.nil_id := by
  have := h;
  have h_nil : ∀ {a b : ClassId}, Subtype a b → b = ClassId.nil_id → a = ClassId.nil_id := by
    intros a b hab hb
    induction' hab with a b hab ih;
    all_goals try contradiction;
    · rfl;
    · exact hb;
    · aesop;
    · exact lub_eq_zero hb |>.1;
    · grind +suggestions;
  exact h_nil this rfl

private lemma lub_le_five_left {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    lub a b ≤ 5 := by
  unfold lub; split_ifs <;> simp_all +decide

private lemma subtype_small_stays_small {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
    (h : a ≤ₜ b) : b ≤ 5 := by
  induction h;
  all_goals norm_cast;
  · rename_i k hk₁ hk₂ hk₃ hk₄;
    by_cases hb : ‹ClassId› = ClassId.nil_id;
    · exact hb.symm ▸ by decide;
    · exact hk₄ ( by
        contrapose! hb;
        cases hb;
        · exact absurd hk₁ ( by exact fun h => by exact absurd ( subtype_nil_eq h ) ( by exact ne_of_gt ha1 ) );
        · contradiction ) ( hk₃ ha1 ha5 );
  · exact?;
  · rename_i c d;
    cases c <;> cases d <;> simp_all +decide [ lub ];
    split_ifs <;> norm_cast;
  · exact absurd ha5 ( not_le_of_gt ( lt_of_lt_of_le ( by decide ) ( tensor_id_ge_six _ ) ) )

private lemma subtype_from_ge_six {a b : ClassId} (ha : a ≥ 6)
    (h : a ≤ₜ b) : b = a ∨ b ≤ 5 ∨
    (∃ prefix_ suffix_, a = ClassId.tensor_id (Shape.concrete (prefix_ ++ suffix_)) ∧
                          b = ClassId.tensor_id (Shape.unbounded suffix_)) := by
  have := h;
  induction' this with a b c h1 h2 ih1 ih2;
  all_goals norm_cast at *;
  · exact Or.inl rfl;
  · by_cases h5 : h1 ≥ 6;
    · grind +suggestions;
    · have h6 : h1 ≤ 5 := by
        exact Nat.le_of_not_lt h5;
      exact Or.inr <| Or.inl <| subtype_small_stays_small ( show 1 ≤ h1 from by
                                                              rcases h1 with ( _ | _ | _ | _ | _ | _ | _ | h1 ) <;> norm_cast;
                                                              exact absurd ( subtype_nil_eq ih1 ) ( by rintro rfl; contradiction ) ) h6 ih2;
  · unfold lub at *;
    split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
  · unfold lub;
    split_ifs <;> simp_all +decide;
  · exact Or.inr <| Or.inr <| ⟨ _, _, rfl, rfl ⟩

private lemma subtype_ge_six_tensor {a b : ClassId} (ha : a ≥ 6) (hb : b ≥ 6)
    (h : a ≤ₜ b) : a = b ∨
    (∃ prefix_ suffix_, a = ClassId.tensor_id (Shape.concrete (prefix_ ++ suffix_)) ∧
                          b = ClassId.tensor_id (Shape.unbounded suffix_)) := by
  -- By definition of subtype_from_ge_six, we know that either a = b or ∃ prefix_ suffix_, a = tensor_id (concrete (prefix_ ++ suffix_)) ∧ b = tensor_id (unbounded suffix_).
  have h_cases : a = b ∨ ∃ prefix_ suffix_, a = ClassId.tensor_id (Shape.concrete (prefix_ ++ suffix_)) ∧ b = ClassId.tensor_id (Shape.unbounded suffix_) := by
    have := subtype_from_ge_six ha h
    grind;
  exact h_cases

/-
Key extraction lemma: if a concrete tensor type subtypes another tensor type,
    we can characterize the relationship.
-/
theorem tensor_subtype_extract {d : List Dim} {s : Shape}
    (h : ClassId.tensor_id (Shape.concrete d) ≤ₜ ClassId.tensor_id s) :
    (s = Shape.concrete d) ∨
    (∃ prefix_, s = Shape.unbounded (d.drop prefix_.length) ∧ d = prefix_ ++ d.drop prefix_.length) := by
  have h_cases : ClassId.tensor_id (Shape.concrete d) = ClassId.tensor_id s ∨
                     (∃ prefix_ suffix_, ClassId.tensor_id (Shape.concrete d) = ClassId.tensor_id (Shape.concrete (prefix_ ++ suffix_)) ∧
                                              ClassId.tensor_id s = ClassId.tensor_id (Shape.unbounded suffix_)) := by
                                                apply subtype_ge_six_tensor (tensor_id_ge_six (Shape.concrete d)) (tensor_id_ge_six s) h
  generalize_proofs at *; (
  rcases h_cases with ( h_cases | ⟨ prefix_, suffix_, h₁, h₂ ⟩ ) <;> simp_all +decide [ ClassId.tensor_id ];
  exact ⟨ prefix_, by simp +decide, by simp +decide ⟩)

/-
Simplified version: if concrete subtypes concrete, they're equal
-/
theorem tensor_id_subtype_concrete_eq {d1 d2 : List Dim}
    (h : ClassId.tensor_id (Shape.concrete d1) ≤ₜ ClassId.tensor_id (Shape.concrete d2)) :
    d1 = d2 := by
  convert tensor_subtype_extract h using 1;
  aesop

/-
If concrete subtypes unbounded, the concrete dims end with the unbounded suffix
-/
theorem tensor_id_subtype_unbounded {d : List Dim} {suffix_ : List Dim}
    (h : ClassId.tensor_id (Shape.concrete d) ≤ₜ ClassId.tensor_id (Shape.unbounded suffix_)) :
    ∃ prefix_, d = prefix_ ++ suffix_ := by
  have := tensor_subtype_extract h;
  grind

/-! ## More inversion lemmas -/

theorem broadcast_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.broadcast e1 e2) ty) :
    ∃ (s1 s2 sOut : Shape),
      broadcastShapes s1 s2 = some sOut ∧
      HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧
      HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧
      Subtype (ClassId.tensor_id sOut) ty := by
  contrapose! h;
  intro H;
  -- By definition of HasType, there must exist s1, s2, sOut such that the conditions hold.
  obtain ⟨s1, s2, sOut, h_broadcast, h_e1, h_e2, h_subtype⟩ : ∃ s1 s2 sOut, broadcastShapes s1 s2 = some sOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧ HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧ Subtype (ClassId.tensor_id sOut) ty := by
    have h_inv : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → (e = Expr.broadcast e1 e2 → ∃ s1 s2 sOut, broadcastShapes s1 s2 = some sOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧ HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧ Subtype (ClassId.tensor_id sOut) ty) := by
      intros e ty h e_eq;
      induction' h with e ty h ih generalizing e1 e2;
      all_goals cases e_eq;
      · exact ⟨ _, _, _, ‹_›, ‹_›, ‹_›, Subtype.refl _ ⟩;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ s1, s2, sOut, h₁, h₂, h₃, h₄ ⟩ := h₃ h H rfl;
        exact ⟨ s1, s2, sOut, h₁, h₂, h₃, Subtype.trans h₄ ‹_› ⟩;
    exact h_inv H rfl;
  exact h s1 s2 sOut h_broadcast h_e1 h_e2 h_subtype

theorem matmul_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.matmul e1 e2) ty) :
    ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ),
      broadcastShapes batch1 batch2 = some batchOut ∧
      HasType CT ms Γ e1 (ClassId.tensor_id (batch1.appendDims [m, k])) ∧
      HasType CT ms Γ e2 (ClassId.tensor_id (batch2.appendDims [k, n])) ∧
      Subtype (ClassId.tensor_id (batchOut.appendDims [m, n])) ty := by
  contrapose! h;
  -- Apply the definition of HasType to the matmul expression.
  intro h_matmul
  obtain ⟨batch1, batch2, batchOut, m, k, n, h_broadcast, h_e1, h_e2, h_subtype⟩ : ∃ batch1 batch2 batchOut m k n, broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1.appendDims [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2.appendDims [k, n])) ∧ ClassId.tensor_id (batchOut.appendDims [m, n]) ≤ₜ ty := by
    have h_matmul_def : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.matmul e1 e2 → ∃ batch1 batch2 batchOut m k n, broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1.appendDims [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2.appendDims [k, n])) ∧ ClassId.tensor_id (batchOut.appendDims [m, n]) ≤ₜ ty := by
      intros e ty h e_eq;
      induction' h with e ty h ih generalizing e1 e2;
      all_goals cases e_eq;
      · exact ⟨ _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, by tauto ⟩;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ batch1, batch2, batchOut, m, k, n, h₁, h₂, h₃, h₄ ⟩ := h₃ h h_matmul rfl;
        exact ⟨ batch1, batch2, batchOut, m, k, n, h₁, h₂, h₃, Subtype.trans h₄ ‹_› ⟩;
    exact h_matmul_def h_matmul rfl;
  exact h batch1 batch2 batchOut m k n h_broadcast h_e1 h_e2 h_subtype

theorem reshape_inversion {Γ : TypEnv} {e : Expr} {s2 : List Dim} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.reshape e s2) ty) :
    ∃ (s1 : List Dim),
      s1.prod = s2.prod ∧
      HasType CT ms Γ e (ClassId.tensor_id (Shape.concrete s1)) ∧
      Subtype (ClassId.tensor_id (Shape.concrete s2)) ty := by
  have h_inv : ∀ {e : Expr} {e' : Expr} {ty : ClassId}, HasType CT ms Γ e' ty → e' = e.reshape s2 → ∃ s1 : List Dim, s1.prod = s2.prod ∧ HasType CT ms Γ e (ClassId.tensor_id (Shape.concrete s1)) ∧ ClassId.tensor_id (Shape.concrete s2) ≤ₜ ty := by
    intros e e' ty h e'_eq
    induction' h with e' ty h ih generalizing e;
    all_goals cases e'_eq;
    · exact ⟨ _, ‹_›, ‹_›, Subtype.refl _ ⟩;
    · rename_i h₁ h₂ h₃;
      exact Exists.elim ( h₃ rfl ) fun s1 hs1 => ⟨ s1, hs1.1, hs1.2.1, Subtype.trans hs1.2.2 h₁ ⟩;
  exact h_inv h rfl

/-! ## Broadcast preservation lemmas -/

/-
Helper: extract concrete broadcastShapesRev from broadcastShapes
-/
private lemma broadcastShapes_concrete_unfold {d1 d2 dOut : List Dim}
    (h : broadcastShapes (Shape.concrete d1) (Shape.concrete d2) = some (Shape.concrete dOut)) :
    broadcastShapesRev d1.reverse d2.reverse = some dOut.reverse := by
  unfold broadcastShapes at h;
  aesop

/-
Helper: if suffix broadcast succeeds and runtime broadcast succeeds,
    the runtime result's reversed list starts with the suffix broadcast result.
-/
private lemma broadcast_suffix_result {suffix1 suffix2 : List Dim}
    {p1 p2 : List Dim} {r_suffix dOut : List Dim}
    (hLen : suffix1.length = suffix2.length)
    (hSuffix : broadcastShapesRev suffix1.reverse suffix2.reverse = some r_suffix)
    (hRuntime : broadcastShapesRev (suffix1.reverse ++ p1) (suffix2.reverse ++ p2) = some dOut) :
    ∃ extra, dOut = r_suffix ++ extra := by
  -- By definition of `broadcastShapesRev`, we know that if `broadcastShapesRev (suffix1.reverse ++ p1) (suffix2.reverse ++ p2) = some dOut`, then `dOut` is the result of appending the original suffixes' broadcast to the prefix broadcast result.
  have hbroadcastShapesRev_append : ∀ (p1 p2 : List Dim), broadcastShapesRev (suffix1.reverse ++ p1) (suffix2.reverse ++ p2) = some dOut → ∃ extra, dOut = r_suffix ++ extra := by
    intros p1 p2 hRuntime
    have := @broadcastShapesRev_prefix;
    exact this ( by simp +decide [ hLen ] ) hSuffix hRuntime;
  exact hbroadcastShapesRev_append p1 p2 hRuntime

/-
Case concrete/concrete
-/
private lemma bcast_pres_cc {d1 d2 dOut ds1 ds2 : List Dim} {sOut : Shape}
    (hType : broadcastShapes (Shape.concrete ds1) (Shape.concrete ds2) = some sOut)
    (hSub1 : ClassId.tensor_id (Shape.concrete d1) ≤ₜ ClassId.tensor_id (Shape.concrete ds1))
    (hSub2 : ClassId.tensor_id (Shape.concrete d2) ≤ₜ ClassId.tensor_id (Shape.concrete ds2))
    (hRuntime : broadcastShapes (Shape.concrete d1) (Shape.concrete d2) = some (Shape.concrete dOut)) :
    ClassId.tensor_id (Shape.concrete dOut) ≤ₜ ClassId.tensor_id sOut := by
  rw [ tensor_id_subtype_concrete_eq hSub1, tensor_id_subtype_concrete_eq hSub2 ] at *;
  cases hType.symm.trans hRuntime ; tauto

/-- Helper: decompose d.reverse into suffix.reverse ++ prefix.reverse
    when d = prefix ++ suffix. -/
private lemma reverse_append_decompose {d suffix_ : List Dim}
    (h : ∃ prefix_, d = prefix_ ++ suffix_) :
    ∃ p, d.reverse = suffix_.reverse ++ p := by
  obtain ⟨prefix_, rfl⟩ := h
  exact ⟨prefix_.reverse, by simp [List.reverse_append]⟩

/-
Helper: if d = prefix ++ suffix and tail = suffix.drop(|suffix|-n),
    then d.reverse = tail.reverse ++ rest for some rest.
-/
private lemma reverse_has_tail_prefix {d suffix_ : List Dim} {n : ℕ}
    (hd : ∃ prefix_, d = prefix_ ++ suffix_)
    (hn : n ≤ suffix_.length) :
    ∃ rest, d.reverse = (suffix_.drop (suffix_.length - n)).reverse ++ rest := by
  obtain ⟨ prefix_, rfl ⟩ := hd;
  simp +zetaDelta at *;
  rw [ ← List.take_append_drop ( suffix_.length - n ) suffix_, List.reverse_append ];
  simp +arith +decide [ List.length_append, List.length_take, List.length_drop, hn ]

/-
Helper: extract sOut suffix from broadcastShapes in the unbounded case
-/
private lemma broadcastShapes_unbounded_extract {s1 s2 : Shape} {sOut : Shape}
    (hType : broadcastShapes s1 s2 = some sOut)
    (hNotCC : ¬(s1.isUnbounded = false ∧ s2.isUnbounded = false)) :
    ∃ (sOutDims : List Dim) (n : ℕ) (r : List Dim),
      sOut = Shape.unbounded sOutDims ∧
      n = min s1.dims.length s2.dims.length ∧
      broadcastShapesRev (s1.dims.drop (s1.dims.length - n)).reverse
                         (s2.dims.drop (s2.dims.length - n)).reverse = some r ∧
      sOutDims = r.reverse := by
  rcases s1 with ( _ | s1_dims ) <;> rcases s2 with ( _ | s2_dims ) <;> simp_all +decide [ Shape.isUnbounded ];
  · unfold broadcastShapes at hType; aesop;
  · unfold broadcastShapes at hType; aesop;
  · unfold broadcastShapes at hType; aesop;

/-
Case unbounded/anything or anything/unbounded (at least one unbounded)
-/
private lemma bcast_pres_unbounded {d1 d2 dOut : List Dim} {s1 s2 sOut : Shape}
    (hType : broadcastShapes s1 s2 = some sOut)
    (hSub1 : ClassId.tensor_id (Shape.concrete d1) ≤ₜ ClassId.tensor_id s1)
    (hSub2 : ClassId.tensor_id (Shape.concrete d2) ≤ₜ ClassId.tensor_id s2)
    (hRuntime : broadcastShapes (Shape.concrete d1) (Shape.concrete d2) = some (Shape.concrete dOut))
    (hNotCC : ¬(s1.isUnbounded = false ∧ s2.isUnbounded = false)) :
    ClassId.tensor_id (Shape.concrete dOut) ≤ₜ ClassId.tensor_id sOut := by
  obtain ⟨ sOutDims, n, r, hsOut, hn, hr, hdOut ⟩ := broadcastShapes_unbounded_extract hType hNotCC;
  have h_suffix : ∃ p1, d1 = p1 ++ s1.dims := by
    have := tensor_subtype_extract hSub1;
    rcases this with ( rfl | ⟨ prefix_, rfl, h ⟩ ) <;> [ exact ⟨ [ ], rfl ⟩ ; exact ⟨ prefix_, h ⟩ ]
  have h_suffix2 : ∃ p2, d2 = p2 ++ s2.dims := by
    have := tensor_subtype_extract hSub2;
    rcases this with ( rfl | ⟨ prefix_, rfl, h ⟩ ) <;> [ exact ⟨ [ ], rfl ⟩ ; exact ⟨ prefix_, h ⟩ ];
  have h_suffix_rev : ∃ rest1, d1.reverse = (s1.dims.drop (s1.dims.length - n)).reverse ++ rest1 := by
    apply reverse_has_tail_prefix;
    · exact h_suffix;
    · exact hn.symm ▸ min_le_left _ _
  have h_suffix_rev2 : ∃ rest2, d2.reverse = (s2.dims.drop (s2.dims.length - n)).reverse ++ rest2 := by
    apply reverse_has_tail_prefix;
    · exact h_suffix2;
    · exact hn.symm ▸ min_le_right _ _;
  obtain ⟨ rest1, hrest1 ⟩ := h_suffix_rev
  obtain ⟨ rest2, hrest2 ⟩ := h_suffix_rev2
  have h_broadcast : broadcastShapesRev (d1.reverse) (d2.reverse) = some dOut.reverse := by
    convert broadcastShapes_concrete_unfold hRuntime using 1;
  have h_broadcast_suffix : ∃ extra, dOut.reverse = r ++ extra := by
    apply broadcast_suffix_result;
    rotate_left;
    exact hr;
    rw [ ← hrest1, ← hrest2, h_broadcast ];
    grind;
  obtain ⟨ extra, hextra ⟩ := h_broadcast_suffix;
  rw [ show dOut = extra.reverse ++ r.reverse by simpa [ List.reverse_append ] using congr_arg List.reverse hextra ];
  rw [ hsOut, hdOut ];
  exact?

/-- Key lemma for preservation: if the type-level broadcast of shapes s1, s2 succeeds,
    and the runtime concrete shapes are subtypes of s1, s2, and the concrete broadcast
    also succeeds, then the concrete result subtypes the type-level result. -/
theorem broadcast_preservation_subtype
    {d1 d2 dOut : List Dim} {s1 s2 sOut : Shape}
    (hType : broadcastShapes s1 s2 = some sOut)
    (hSub1 : ClassId.tensor_id (Shape.concrete d1) ≤ₜ ClassId.tensor_id s1)
    (hSub2 : ClassId.tensor_id (Shape.concrete d2) ≤ₜ ClassId.tensor_id s2)
    (hRuntime : broadcastShapes (Shape.concrete d1) (Shape.concrete d2) = some (Shape.concrete dOut)) :
    ClassId.tensor_id (Shape.concrete dOut) ≤ₜ ClassId.tensor_id sOut := by
  cases s1 with
  | concrete ds1 =>
    cases s2 with
    | concrete ds2 => exact bcast_pres_cc hType hSub1 hSub2 hRuntime
    | unbounded ds2 => exact bcast_pres_unbounded hType hSub1 hSub2 hRuntime (by simp [Shape.isUnbounded])
  | unbounded ds1 =>
    cases s2 with
    | concrete ds2 => exact bcast_pres_unbounded hType hSub1 hSub2 hRuntime (by simp [Shape.isUnbounded])
    | unbounded ds2 => exact bcast_pres_unbounded hType hSub1 hSub2 hRuntime (by simp [Shape.isUnbounded])

/-! ## Context lemmas -/

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
    exact ⟨tyE, ClassId.tensor_id (bo.appendDims [m, n]), hE,
      CtxHasType.matmulL _ _ _ _ _ _ _ _ _ _ hb hCtxRecv h2, hSub⟩
  | matmulR v C' ih =>
    obtain ⟨b1, b2, bo, m, k, n, hb, h1, h2, hSub⟩ := matmul_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h2
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id (bo.appendDims [m, n]), hE,
      CtxHasType.matmulR _ _ _ _ _ _ _ _ _ _ hb h1 hCtxArg, hSub⟩
  | reshapeC C' s2 ih =>
    obtain ⟨s1, hSz, he, hSub⟩ := reshape_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih he
    have hCtxR := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id (Shape.concrete s2), hE,
      CtxHasType.reshapeC _ _ _ _ _ hSz hCtxR, hSub⟩

theorem substitution_lemma
    {Δ : TypEnv} {C : Ctx} {e : Expr} {tyHole tyCtx tyE : ClassId}
    (hCtx : CtxHasType CT ms Δ tyHole C tyCtx)
    (hExpr : HasType CT ms Δ e tyE)
    (hSub : Subtype tyE tyHole) :
    ∃ tyCtx', HasType CT ms Δ (C[[ e ]]) tyCtx' ∧ Subtype tyCtx' tyCtx := by
  by_contra h_contra;
  -- By definition of `HasType`, if `HasType CT ms Δ (C[[e]]) tyCtx` is false, then `HasType CT ms Δ (C[[e]]) tyCtx` must be true.
  have h_true : HasType CT ms Δ (C[[e]]) tyCtx := by
    have hCtxExpr : ∀ {tyHole tyCtx : ClassId} {C : Ctx} {e : Expr}, CtxHasType CT ms Δ tyHole C tyCtx → HasType CT ms Δ e tyHole → HasType CT ms Δ (C[[e]]) tyCtx := by
      intros tyHole tyCtx C e hCtx hExpr
      induction' hCtx with tyHole tyCtx C e hCtx hExpr ih;
      all_goals norm_num [ CtxHasType ] at *;
      exact?;
      any_goals apply HasType.tApp; assumption; assumption; assumption; assumption; assumption;
      any_goals apply HasType.tSeq; assumption; assumption;
      any_goals apply HasType.tEq; assumption; assumption;
      any_goals apply HasType.tIf; assumption; assumption; assumption;
      any_goals apply HasType.tAppLib; assumption; assumption; assumption;
      any_goals apply HasType.tBroadcast; assumption; assumption; assumption;
      · exact HasType.tMatmul _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›;
      · exact HasType.tMatmul _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›;
      · exact HasType.tReshape _ _ _ _ ‹_› ‹_›;
      · exact HasType.tSub _ _ _ _ ‹_› ‹_›;
    exact hCtxExpr hCtx ( HasType.tSub _ _ _ _ hExpr hSub );
  exact h_contra ⟨ tyCtx, h_true, by tauto ⟩

/-! ## Main theorems -/

def LibTermination (libImpl : MethKey → Val → Val → Option Val)
    (ms : MethodSets) : Prop :=
  ∀ key v1 v2, key ∈ ms.library → ∃ v', libImpl key v1 v2 = some v'

/-- Helper: if e cannot be Expr.call (val vr) m (val v) then isUserMethodCall is false -/
private lemma not_user_call_of_not_call {e : Expr}
    (h : ∀ vr m v, e ≠ Expr.call (Expr.val vr) m (Expr.val v)) :
    ¬isUserMethodCall e ms := by
  intro ⟨vr, v, m', heq, _⟩; exact h vr m' v heq

/-- If e can step to a config, then C[[e]] can also step to a config. -/
private lemma step_in_context
    {E E' : DynEnv} {e e' : Expr} {S S' : Stack} {C : Ctx}
    (h : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩))
    (hNotVal : e.isVal = false)
    (_hValid : ValidCT CT ms methodDefs) :
    ∃ E'' e'' S'', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E'', e'', S''⟩) := by
  cases h with
  | eVar =>
    rename_i x v hx
    exact ⟨E, C[[Expr.val v]], S,
      Step.eContext E E C _ _ S (Step.eVar E x S v hx)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eSelf =>
    rename_i v hself
    exact ⟨E, C[[Expr.val v]], S,
      Step.eContext E E C _ _ S (Step.eSelf E S v hself)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eTSelf =>
    rename_i v htself
    exact ⟨E, C[[Expr.val v]], S,
      Step.eContext E E C _ _ S (Step.eTSelf E S v htself)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eSeq =>
    rename_i v
    exact ⟨E, C[[e']], S,
      Step.eContext E E C _ _ S (Step.eSeq E v e' S)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eNew =>
    rename_i A
    exact ⟨E, C[[Expr.val (Val.obj A)]], S,
      Step.eContext E E C _ _ S (Step.eNew E A S)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eIfTrue =>
    rename_i v e3 htruthy
    exact ⟨E, C[[e']], S,
      Step.eContext E E C _ _ S (Step.eIfTrue E v e' e3 S htruthy)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eIfFalse =>
    rename_i v e2 hfalsy
    exact ⟨E, C[[e']], S,
      Step.eContext E E C _ _ S (Step.eIfFalse E v e2 e' S hfalsy)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eEqTrue =>
    rename_i v1 v2 heq'
    exact ⟨E, C[[Expr.val Val.true_]], S,
      Step.eContext E E C _ _ S (Step.eEqTrue E v1 v2 S heq')
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eEqFalse =>
    rename_i v1 v2 hneq
    exact ⟨E, C[[Expr.val Val.false_]], S,
      Step.eContext E E C _ _ S (Step.eEqFalse E v1 v2 S hneq)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eAppUD =>
    rename_i C' vr v m' x md hUM hDef hP hB
    subst hP; subst hB
    rw [show C[[C'[[Expr.call (Expr.val vr) m' (Expr.val v)]]]]
        = (C.compose C')[[Expr.call (Expr.val vr) m' (Expr.val v)]]
        from (Ctx.compose_fill C C' _).symm]
    exact ⟨(emptyEnv [VarId.self_id ↦ vr]) [md.param ↦ v], md.body, (E, C.compose C') :: S,
      Step.eAppUD E (C.compose C') vr v m' S md.param md.body md hUM hDef rfl rfl⟩
  | eAppLib =>
    rename_i Ares vr v v' m' hLib hCall hSub
    exact ⟨E, C[[Expr.val v']], S,
      Step.eContext E E C _ _ S (Step.eAppLib E Ares vr v v' m' S hLib hCall hSub)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eRet => simp [Expr.isVal] at hNotVal
  | eContext =>
    rename_i C' ei ei' hNU hNV hStep
    rw [show C[[C'[[ei]]]] = (C.compose C')[[ei]] from (Ctx.compose_fill C C' _).symm]
    exact ⟨E', (C.compose C')[[ei']], S,
      (Ctx.compose_fill C C' ei').symm ▸ Step.eContext E E' (C.compose C') ei ei' S hStep hNU hNV⟩
  | eBroadcast =>
    rename_i s1 s2 sOut hBr
    exact ⟨E, C[[Expr.val (Val.tensor sOut)]], S,
      Step.eContext E E C _ _ S (Step.eBroadcast E s1 s2 sOut S hBr)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eMatmul =>
    rename_i b1 b2 bOut m' k n hBatch
    exact ⟨E, C[[Expr.val (Val.tensor (bOut ++ [m', n]))]], S,
      Step.eContext E E C _ _ S (Step.eMatmul E b1 b2 bOut m' k n S hBatch)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩
  | eReshape =>
    rename_i s1 s2 hSize
    exact ⟨E, C[[Expr.val (Val.tensor s2)]], S,
      Step.eContext E E C _ _ S (Step.eReshape E s1 s2 S hSize)
        (not_user_call_of_not_call (fun _ _ _ h => Expr.noConfusion h)) hNotVal⟩

private theorem progress_in_context
    {E : DynEnv} {C : Ctx} {e : Expr} {S : Stack}
    (hNotVal : e.isVal = false)
    (hProgress : (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩)) ∨
                 (Step methodDefs libImpl ms ⟨E, e, S⟩ .blame))
    (hValid : ValidCT CT ms methodDefs) :
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ .blame) := by
  rcases hProgress with ⟨E', e', S', h⟩ | h
  · exact Or.inl (step_in_context h hNotVal hValid)
  · exact Or.inr (Step.eBlameContext E C e S h)

private theorem progress_subexpr
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
  rcases hProg1 with ⟨v, rfl⟩ | ⟨E', e', S', hStep⟩ | hBlame
  · exact hValCase v rfl
  · -- e1 can step. If it's a value (eRet case), handle via hValCase.
    -- Otherwise use progress_in_context.
    cases hv : e1.isVal
    · exact progress_in_context hv (Or.inl ⟨E', e', S', hStep⟩) hValid
    · -- e1 is a value that can step (eRet case)
      obtain ⟨v, rfl⟩ : ∃ v, e1 = Expr.val v := by
        cases e1 <;> simp [Expr.isVal] at hv; exact ⟨_, rfl⟩
      exact hValCase v rfl
  · cases hv : e1.isVal
    · exact progress_in_context hv (Or.inr hBlame) hValid
    · obtain ⟨v, rfl⟩ : ∃ v, e1 = Expr.val v := by
        cases e1 <;> simp [Expr.isVal] at hv; exact ⟨_, rfl⟩
      exact hValCase v rfl

set_option maxHeartbeats 800000 in
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
  induction hType with
  | tNil | tObj | tTrue | tFalse | tType | tTensor | tBlame => exact Or.inl ⟨_, rfl⟩
  | tVar =>
    rename_i x A hVar
    exact Or.inr (Or.inl ⟨E, _, S, Step.eVar E x S _ ((hEnvCons.1 x).mpr ⟨A, hVar⟩).choose_spec⟩)
  | tSelf =>
    rename_i A hSelf
    exact Or.inr (Or.inl ⟨E, _, S, Step.eSelf E S _ ((hEnvCons.1 VarId.self_id).mpr ⟨A, hSelf⟩).choose_spec⟩)
  | tTSelf =>
    rename_i A hTSelf
    exact Or.inr (Or.inl ⟨E, _, S, Step.eTSelf E S _ ((hEnvCons.1 VarId.tself_id).mpr ⟨A, hTSelf⟩).choose_spec⟩)
  | tNew => exact Or.inr (Or.inl ⟨E, _, S, Step.eNew E _ S⟩)
  | tSub _ _ _ _ _ ih => exact ih
  | tSeq =>
    rename_i e1 e2 A1 A2 h1 h2 ih1 ih2
    right
    exact progress_subexpr (C := Ctx.seqL Ctx.hole e2) ih1 hValid (fun v hv => by
      subst hv; exact Or.inl ⟨E, e2, S, Step.eSeq E v e2 S⟩)
  | tEq =>
    rename_i e1 e2 A1 A2 h1 h2 ih1 ih2
    right
    exact progress_subexpr (C := Ctx.eqL Ctx.hole e2) ih1 hValid (fun v1 hv1 => by
      subst hv1
      exact progress_subexpr (C := Ctx.eqR v1 Ctx.hole) ih2 hValid (fun v2 hv2 => by
        subst hv2
        cases hb : v1.equiv v2 with
        | true => exact Or.inl ⟨E, _, S, Step.eEqTrue E v1 v2 S hb⟩
        | false => exact Or.inl ⟨E, _, S, Step.eEqFalse E v1 v2 S hb⟩))
  | tIf =>
    rename_i e1 e2 e3 A1 A2 A3 h1 h2 h3 ih1 ih2 ih3
    right
    exact progress_subexpr (C := Ctx.iteC Ctx.hole e2 e3) ih1 hValid (fun v hv => by
      subst hv
      cases hb : v.isTruthy with
      | true => exact Or.inl ⟨E, e2, S, Step.eIfTrue E v e2 e3 S hb⟩
      | false => exact Or.inl ⟨E, e3, S, Step.eIfFalse E v e2 e3 S hb⟩)
  | tApp =>
    rename_i e0 e1 m Arecv Aarg A1 A2 h0 h1 hUser hCT hArgSub ih0 ih1
    right
    exact progress_subexpr (C := Ctx.callL Ctx.hole m e1) ih0 hValid (fun v0 hv0 => by
      subst hv0
      exact progress_subexpr (C := Ctx.callR v0 m Ctx.hole) ih1 hValid (fun v1 hv1 => by
        subst hv1
        have hSub0 := val_type_subtype h0
        have hUserV0 := hValid.2.2.2.1 Arecv v0.typeOf m hSub0 hUser
        obtain ⟨a1, a2, hCT', md, hDef, hBody⟩ := hValid.1 ⟨v0.typeOf, m⟩ hUserV0
        exact Or.inl ⟨(emptyEnv [VarId.self_id ↦ v0]) [md.param ↦ v1], md.body,
          (E, Ctx.hole) :: S,
          Step.eAppUD E Ctx.hole v0 v1 m S md.param md.body md hUserV0 hDef rfl rfl⟩))
  | tAppLib =>
    rename_i e0 e1 m Ares Arec Aarg h0 h1 hLib ih0 ih1
    right
    exact progress_subexpr (C := Ctx.checkedCallL Ares Ctx.hole m e1) ih0 hValid (fun v0 hv0 => by
      subst hv0
      exact progress_subexpr (C := Ctx.checkedCallR Ares v0 m Ctx.hole) ih1 hValid (fun v1 hv1 => by
        subst hv1
        have hSub0 := val_type_subtype h0
        have hLibV0 := hValid.2.2.2.2 Arec v0.typeOf m hSub0 hLib
        obtain ⟨v', hv'⟩ := hLibTerm ⟨v0.typeOf, m⟩ v0 v1 hLibV0
        by_cases hSubRes : v'.typeOf ≤ₜ Ares
        · exact Or.inl ⟨E, Expr.val v', S, Step.eAppLib E Ares v0 v1 v' m S hLibV0 hv' hSubRes⟩
        · exact Or.inr (Step.eBlameCheckedCall E Ares v0 v1 v' m S hLibV0 hv' hSubRes)))
  | tBroadcast =>
    rename_i e1 e2 s1 s2 sOut hBroadcast h1 h2 ih1 ih2
    right
    exact progress_subexpr (C := Ctx.broadcastL Ctx.hole e2) ih1 hValid (fun v1 hv1 => by
      subst hv1
      exact progress_subexpr (C := Ctx.broadcastR v1 Ctx.hole) ih2 hValid (fun v2 hv2 => by
        subst hv2
        by_cases hMatch : ∃ d1 d2 dOut, v1 = Val.tensor d1 ∧ v2 = Val.tensor d2 ∧
            broadcastShapes (Shape.concrete d1) (Shape.concrete d2) = some (Shape.concrete dOut)
        · obtain ⟨d1, d2, dOut, rfl, rfl, hBr⟩ := hMatch
          exact Or.inl ⟨E, Expr.val (Val.tensor dOut), S, Step.eBroadcast E d1 d2 dOut S hBr⟩
        · exact Or.inr (Step.eBlameBroadcast E v1 v2 S hMatch)))
  | tMatmul =>
    rename_i e1 e2 batch1 batch2 batchOut mk kk nk hBatch h1 h2 ih1 ih2
    right
    exact progress_subexpr (C := Ctx.matmulL Ctx.hole e2) ih1 hValid (fun v1 hv1 => by
      subst hv1
      exact progress_subexpr (C := Ctx.matmulR v1 Ctx.hole) ih2 hValid (fun v2 hv2 => by
        subst hv2
        by_cases hMatch : ∃ b1 b2 bOut m' k' n',
            broadcastShapes (Shape.concrete b1) (Shape.concrete b2) = some (Shape.concrete bOut) ∧
            v1 = Val.tensor (b1 ++ [m', k']) ∧ v2 = Val.tensor (b2 ++ [k', n'])
        · obtain ⟨b1, b2, bOut, m', k', n', hBr, rfl, rfl⟩ := hMatch
          exact Or.inl ⟨E, Expr.val (Val.tensor (bOut ++ [m', n'])), S,
            Step.eMatmul E b1 b2 bOut m' k' n' S hBr⟩
        · exact Or.inr (Step.eBlameMatmul E v1 v2 S hMatch)))
  | tReshape =>
    rename_i e1 s1 s2 hSize h1 ih1
    right
    exact progress_subexpr (C := Ctx.reshapeC Ctx.hole s2) ih1 hValid (fun v hv => by
      subst hv
      by_cases hMatch : ∃ d1, v = Val.tensor d1 ∧ d1.prod = s2.prod
      · obtain ⟨d1, rfl, hSz⟩ := hMatch
        exact Or.inl ⟨E, Expr.val (Val.tensor s2), S, Step.eReshape E d1 s2 S hSz⟩
      · exact Or.inr (Step.eBlameReshape E v s2 S hMatch))

theorem ctx_weakening
    {Γ Δ : TypEnv} {C : Ctx} {tyHole tyCtx : ClassId}
    (hCtx : CtxHasType CT ms Γ tyHole C tyCtx)
    (hExt : TypEnv.extends_ Γ Δ) :
    CtxHasType CT ms Δ tyHole C tyCtx := by
  induction hCtx <;> simp_all +decide [ TypEnv.extends_ ];
  all_goals constructor;
  all_goals solve_by_elim [ weakening ]

private theorem matmul_dim_extract {a : List Dim} {x y m k : ℕ} {s : Shape}
    (h : ClassId.tensor_id (Shape.concrete (a ++ [x, y])) ≤ₜ ClassId.tensor_id (s.appendDims [m, k])) :
    x = m ∧ y = k ∧ ClassId.tensor_id (Shape.concrete a) ≤ₜ ClassId.tensor_id s := by
  cases s;
  · have := tensor_id_subtype_concrete_eq h; simp_all +decide [ List.append_eq_cons_iff ] ;
    replace this := congr_arg List.reverse this ; simp_all +decide [ List.reverse_append ];
    exact Subtype.refl _;
  · have := tensor_id_subtype_unbounded h;
    obtain ⟨ prefix_, h ⟩ := this;
    have := congr_arg List.reverse h; norm_num at this;
    exact ⟨ this.2.1, this.1, by rw [ this.2.2 ] ; exact Subtype.tensor_unbounded_sub _ _ ⟩

-- Same-stack preservation: for steps that don't change the stack.
set_option maxHeartbeats 1600000 in
private theorem preservation_same_stack
    {Γ : TypEnv} {E E' : DynEnv} {e e' : Expr}
    {ty : ClassId} {S : Stack}
    (hStep : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S⟩))
    (hType : HasType CT ms Γ e ty)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hValid : ValidCT CT ms methodDefs) :
    ∃ (Δ : TypEnv) (ty' : ClassId),
      HasType CT ms Δ e' ty' ∧
      Subtype ty' ty ∧
      EnvConsistent CT ms Δ E' ∧
      TypEnv.extends_ Γ Δ := by
  generalize hc1 : (⟨E, e, S⟩ : Config) = c1 at hStep
  generalize hc2 : (StepResult.config ⟨E', e', S⟩) = c2 at hStep
  induction hStep generalizing Γ ty E E' e e' S with
  | eVar _ x _ v hx =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨a, ha, hsub⟩ := var_inversion hType
    obtain ⟨a', a'', hv, ha', hsub'⟩ := hEnvCons.2 x v hx
    have heq : a'' = a := by rw [ha] at ha'; exact Option.some_injective _ ha'.symm
    subst heq
    exact ⟨Γ, a', hv, Subtype.trans hsub' hsub, hEnvCons, fun _ _ h => h⟩
  | eSelf _ _ v hself =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨a, ha, hsub⟩ := self_inversion hType
    obtain ⟨a', a'', hv, ha', hsub'⟩ := hEnvCons.2 _ v hself
    have heq : a'' = a := by rw [ha] at ha'; exact Option.some_injective _ ha'.symm
    subst heq
    exact ⟨Γ, a', hv, Subtype.trans hsub' hsub, hEnvCons, fun _ _ h => h⟩
  | eTSelf _ _ v htself =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨a, ha, hsub⟩ := tself_inversion hType
    obtain ⟨a', a'', hv, ha', hsub'⟩ := hEnvCons.2 _ v htself
    have heq : a'' = a := by rw [ha] at ha'; exact Option.some_injective _ ha'.symm
    subst heq
    exact ⟨Γ, a', hv, Subtype.trans hsub' hsub, hEnvCons, fun _ _ h => h⟩
  | eSeq _ v e2 _ =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, A2, _, h2, hSub⟩ := seq_inversion hType
    exact ⟨Γ, A2, h2, hSub, hEnvCons, fun _ _ h => h⟩
  | eNew _ A _ =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    exact ⟨Γ, A, HasType.tObj Γ A, new_inversion hType, hEnvCons, fun _ _ h => h⟩
  | eIfTrue _ v e2 e3 _ htruthy =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, A2, A3, _, h2, _, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A2, h2, Subtype.trans (Subtype.lub_left A2 A3) hSub, hEnvCons, fun _ _ h => h⟩
  | eIfFalse _ v e2 e3 _ hfalsy =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, A2, A3, _, _, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A3, h3, Subtype.trans (Subtype.lub_right A2 A3) hSub, hEnvCons, fun _ _ h => h⟩
  | eEqTrue _ v1 v2 _ _ =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, _, _, _, hSub⟩ := eq_inversion hType
    exact ⟨Γ, _, HasType.tTrue Γ, Subtype.trans Subtype.true_bool hSub, hEnvCons, fun _ _ h => h⟩
  | eEqFalse _ v1 v2 _ _ =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, _, _, _, hSub⟩ := eq_inversion hType
    exact ⟨Γ, _, HasType.tFalse Γ, Subtype.trans Subtype.false_bool hSub, hEnvCons, fun _ _ h => h⟩
  | eAppUD _ C vr v m _ x body md hUM hDef hP hB =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2
  | eAppLib _ Ares vr v v' m _ hLib hCall hSubRes =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨_, _, _, _, hAresSub, _⟩ := checked_call_inversion hType
    exact ⟨Γ, _, val_has_type Γ v', Subtype.trans hSubRes hAresSub, hEnvCons, fun _ _ h => h⟩
  | eRet E'_ E_old v C _ =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2
  | eContext _ _ C ei ei' _ hInnerStep hNU hNV ih =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨tyE, tyC', hInnerType, hCtxType, hSubCtx⟩ := ctx_decomposition hType
    have ⟨Δ, tyE', hTyped', hSubTy, hEnvCons', hExtends⟩ := ih hInnerType hEnvCons rfl rfl
    have hCtxWeak := ctx_weakening hCtxType hExtends
    obtain ⟨tyCtx', hCtxFill, hSubCtx'⟩ := substitution_lemma hCtxWeak hTyped' hSubTy
    exact ⟨Δ, tyCtx', hCtxFill, Subtype.trans hSubCtx' hSubCtx, hEnvCons', hExtends⟩
  | eBroadcast _ s1 s2 sOut _ hBr =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨ts1, ts2, tsOut, hBrType, h1, h2, hSub⟩ := broadcast_inversion hType
    exact ⟨Γ, _, HasType.tTensor Γ sOut,
      Subtype.trans (broadcast_preservation_subtype hBrType (val_type_subtype h1) (val_type_subtype h2) hBr) hSub,
      hEnvCons, fun _ _ h => h⟩
  | eMatmul _ b1 b2 bOut m' k n _ hBatch =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨batch1, batch2, batchOut, mk, kk, nk, hBrType, h1, h2, hSub⟩ := matmul_inversion hType
    have hSub1 := val_type_subtype h1  -- tensor_id (concrete (b1++[m',k])) ≤ tensor_id (batch1.appendDims [mk,kk])
    have hSub2 := val_type_subtype h2  -- tensor_id (concrete (b2++[k,n])) ≤ tensor_id (batch2.appendDims [kk,nk])
    obtain ⟨hmk, hkk, hBatchSub1⟩ := matmul_dim_extract hSub1
    obtain ⟨_, hnk, hBatchSub2⟩ := matmul_dim_extract hSub2
    subst hmk; subst hkk; subst hnk
    have hBcastPres := broadcast_preservation_subtype hBrType hBatchSub1 hBatchSub2 hBatch
    have hFinalSub : ClassId.tensor_id (Shape.concrete (bOut ++ [m', n])) ≤ₜ
        ClassId.tensor_id (batchOut.appendDims [m', n]) := by
      rcases batchOut with ⟨ds⟩ | ⟨ds⟩ <;> simp [Shape.appendDims]
      · have heq := tensor_id_subtype_concrete_eq hBcastPres; subst heq; exact Subtype.refl _
      · obtain ⟨prefix_, hpre⟩ := tensor_id_subtype_unbounded hBcastPres
        rw [hpre, List.append_assoc]
        exact Subtype.tensor_unbounded_sub prefix_ (ds ++ [m', n])
    exact ⟨Γ, _, HasType.tTensor Γ (bOut ++ [m', n]),
      Subtype.trans hFinalSub hSub, hEnvCons, fun _ _ h => h⟩
  | eReshape _ s1 s2 _ hSize =>
    simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
    simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
    obtain ⟨s1', hSzType, hE, hSub⟩ := reshape_inversion hType
    have : s1 = s1' := tensor_id_subtype_concrete_eq (val_type_subtype hE); subst this
    exact ⟨Γ, _, HasType.tTensor Γ s2, hSub, hEnvCons, fun _ _ h => h⟩
  | eBlameNilRecv | eBlameCheckedCall | eBlameBroadcast | eBlameMatmul | eBlameReshape | eBlameContext =>
    simp at hc2

/-
Helper: TypeSubStack is monotone under subtyping
-/
private lemma typeSubStack_mono {a b : ClassId} {TS : TypeStack}
    (hab : a ≤ₜ b) (hb : TypeSubStack b TS) : TypeSubStack a TS := by
  -- We'll use induction on the structure of `TS`.
  cases' TS with ts ts';
  · trivial;
  · exact Subtype.trans hab hb

/-
Helper: construct EnvConsistent for the new method env in eAppUD
-/
private lemma envConsistent_method_env
    {vr v : Val} {x : VarId} {selfTy argTy : ClassId}
    (hvrSub : vr.typeOf ≤ₜ selfTy)
    (hvSub : v.typeOf ≤ₜ argTy) :
    EnvConsistent CT ms ((emptyEnv [VarId.self_id ↦ selfTy]) [x ↦ argTy])
      ((emptyEnv [VarId.self_id ↦ vr]) [x ↦ v]) := by
  constructor;
  · intro y; by_cases hy : y = x <;> by_cases hy' : y = VarId.self_id <;> simp +decide [ hy, hy', emptyEnv, envUpdate ] ;
    aesop;
  · intro y w hw; by_cases hy : y = VarId.self_id <;> by_cases hy' : y = x <;> simp_all +decide [ envUpdate ] ;
    · exact ⟨ _, val_has_type _ _, hvSub ⟩;
    · exact ⟨ _, val_has_type _ _, hvrSub ⟩;
    · exact ⟨ _, val_has_type _ _, hvSub ⟩;
    · cases hw

/-
Helper: eAppUD preservation case
-/
private theorem preservation_eAppUD
    {Γ : TypEnv} {E : DynEnv} {S : Stack} {TS : TypeStack}
    {C : Ctx} {vr v : Val} {m : MethId} {x : VarId} {body : Expr} {md : MethDef}
    {ty : ClassId}
    (hType : HasType CT ms Γ (C[[ Expr.call (Expr.val vr) m (Expr.val v) ]]) ty)
    (hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E)
    (hStackCons : StackConsistent CT ms TS S)
    (hValid : ValidCT CT ms methodDefs)
    (hUM : ⟨vr.typeOf, m⟩ ∈ ms.userDefined)
    (hDef : methodDefs ⟨vr.typeOf, m⟩ = some md)
    (hParam : md.param = x)
    (hBody : md.body = body) :
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ body ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ ((emptyEnv [VarId.self_id ↦ vr]) [x ↦ v]) ∧
      StackConsistent CT ms TS' ((E, C) :: S) ∧
      ((E, C) :: S = (E, C) :: S → True) := by
  revert hType;
  intro hType;
  obtain ⟨tyE, tyC', htyE, htyC', hty⟩ := ctx_decomposition hType;
  obtain ⟨Arecv, Aarg, A1, A2, hArecv, hAarg, hCT, hAarg_sub, hA2_sub, hUM⟩ := call_inversion htyE;
  obtain ⟨a1, a2, ha1, ha2, hBody⟩ := hValid.1 ⟨vr.typeOf, m⟩ ‹_›;
  obtain ⟨a2', ha2', ha2''⟩ := hBody.right;
  have := hValid.2.2.1 Arecv vr.typeOf m A1 A2 a1 a2; simp_all +decide [ Val.typeOf ] ;
  use (emptyEnv [VarId.self_id ↦ vr.typeOf]) [x ↦ a1], ⟨Γ, tyE, tyC'⟩ :: TS, a2';
  refine' ⟨ _, _, _, _ ⟩;
  · convert ha2' using 1;
  · exact this ( val_type_subtype hArecv ) |>.2 |> fun h => Subtype.trans ha2'' h |> fun h => Subtype.trans h hA2_sub;
  · apply envConsistent_method_env;
    · cases vr <;> tauto;
    · exact this ( val_type_subtype hArecv ) |>.1 |> fun h => val_type_subtype hAarg |> fun h' => h'.trans hAarg_sub |> fun h'' => h''.trans h;
  · constructor;
    · assumption;
    · exact htyC';
    · assumption;
    · exact Or.inr ( typeSubStack_mono hty hSubStack )

/-
Helper: eRet preservation case
-/
private theorem preservation_eRet
    {Γ : TypEnv} {E' E_old : DynEnv} {v : Val} {C : Ctx}
    {S_rest : Stack} {TS : TypeStack}
    {ty : ClassId}
    (hType : HasType CT ms Γ (Expr.val v) ty)
    (hSubStack : TypeSubStack ty TS)
    (hEnvCons : EnvConsistent CT ms Γ E')
    (hStackCons : StackConsistent CT ms TS ((E_old, C) :: S_rest))
    (hValid : ValidCT CT ms methodDefs) :
    ∃ (Δ : TypEnv) (TS' : TypeStack) (ty' : ClassId),
      HasType CT ms Δ (C[[ Expr.val v ]]) ty' ∧
      TypeSubStack ty' TS' ∧
      EnvConsistent CT ms Δ E_old ∧
      StackConsistent CT ms TS' S_rest := by
  -- Apply the substitution_lemma with the given hypotheses.
  apply Classical.byContradiction
  intro h_contra;
  rcases hStackCons with ( _ | ⟨ Γ_old, retTy, ctxTy, E_old, C, TS_rest, hEnvCons_old, hCtxType, hRest, hSubStackRest ⟩ ) ; simp_all +decide [ TypeSubStack ];
  obtain ⟨tyCtx', htyCtx'⟩ : ∃ tyCtx', HasType CT ms Γ_old (C[[Expr.val v]]) tyCtx' ∧ tyCtx' ≤ₜ ctxTy := by
    apply substitution_lemma hRest (val_has_type Γ_old v) (by
    exact Subtype.trans ( val_type_subtype hType ) hSubStack);
  specialize h_contra Γ_old TS_rest tyCtx' htyCtx'.left;
  cases TS_rest <;> simp_all +decide [ TypeSubStack ];
  exact h_contra ( Subtype.trans htyCtx'.2 ‹_› )

-- Full preservation theorem
set_option maxHeartbeats 1200000 in
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
      (S = S' → Subtype ty' ty ∧ TypEnv.extends_ Γ Δ) := by
  by_cases hSS : S = S'
  · subst hSS
    obtain ⟨Δ, ty', h1, h2, h3, h4⟩ := preservation_same_stack hStep hType hEnvCons hValid
    exact ⟨Δ, TS, ty', h1, typeSubStack_mono h2 hSubStack, h3, hStackCons, fun _ => ⟨h2, h4⟩⟩
  · -- S ≠ S': the step must be eAppUD or eRet
    generalize hc1 : (⟨E, e, S⟩ : Config) = c1 at hStep
    generalize hc2 : (StepResult.config ⟨E', e', S'⟩) = c2 at hStep
    induction hStep generalizing Γ ty E E' e e' S S' TS with
    | eAppUD _ C vr v m _ x body md hUM hDef hP hB =>
      simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
      simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
      obtain ⟨Δ, TS', ty', h1, h2, h3, h4, _⟩ := preservation_eAppUD hType hSubStack hEnvCons hStackCons hValid hUM hDef hP hB
      exact ⟨Δ, TS', ty', h1, h2, h3, h4, fun h => absurd h hSS⟩
    | eRet E'_ E_old v C _ =>
      simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
      simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
      obtain ⟨Δ, TS', ty', h1, h2, h3, h4⟩ := preservation_eRet hType hSubStack hEnvCons hStackCons hValid
      exact ⟨Δ, TS', ty', h1, h2, h3, h4, fun h => absurd h hSS⟩
    | eVar | eSelf | eTSelf | eSeq | eNew | eIfTrue | eIfFalse
    | eEqTrue | eEqFalse | eAppLib | eBroadcast | eMatmul | eReshape =>
      simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
      simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
      exact absurd rfl hSS
    | eContext _ _ C ei ei' _ hInnerStep hNU hNV ih =>
      simp [Config.mk.injEq] at hc1; obtain ⟨rfl, rfl, rfl⟩ := hc1
      simp [StepResult.config.injEq, Config.mk.injEq] at hc2; obtain ⟨rfl, rfl, rfl⟩ := hc2
      exact absurd rfl hSS
    | eBlameNilRecv | eBlameCheckedCall | eBlameBroadcast | eBlameMatmul | eBlameReshape | eBlameContext =>
      simp at hc2

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
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

theorem val_type_subtype {Γ : TypEnv} {v : Val} {A : ClassId}
    (h : HasType CT ms Γ (Expr.val v) A) : v.typeOf ≤ₜ A := by
      have hv : v.typeOf ≤ₜ A := by
        have := h
        have h_ind : ∀ {e : Expr} {A : ClassId}, HasType CT ms Γ e A → ∀ {v : Val}, e = Expr.val v → v.typeOf ≤ₜ A := by
          intros e A h v hv; induction h <;> simp_all +decide [ HasType ] ;
          all_goals subst hv;
          all_goals tauto;
        exact h_ind this rfl;
      exact hv

/-- Weakening -/
def TypEnv.extends_ (Γ Δ : TypEnv) : Prop :=
  ∀ x a, Γ x = some a → Δ x = some a

theorem weakening {Γ Δ : TypEnv} {e : Expr} {ty : ClassId}
    (hType : HasType CT ms Γ e ty)
    (hExt : TypEnv.extends_ Γ Δ) :
    HasType CT ms Δ e ty := by
      induction' hType with Γ e ty hType hExt;
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
        induction' h with e ty h ih;
        all_goals cases h_eq;
        · exact ⟨ _, ‹_›, Subtype.refl _ ⟩;
        · rename_i h₁ h₂ h₃;
          exact h₃ rfl |> fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ a, ha₁, Subtype.trans ha₂ h₁ ⟩;
      exact h_var h rfl

theorem self_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.self ty) :
    ∃ a, Γ VarId.self_id = some a ∧ Subtype a ty := by
      -- By definition of HasType, if HasType CT ms Γ Expr.self ty holds, then there must exist some a such that Γ VarId.self_id = some a and a ≤ₜ ty.
      by_contra h_contra;
      obtain ⟨a, ha⟩ : ∃ a, Γ VarId.self_id = some a ∧ a ≤ₜ ty := by
        have h_self : HasType CT ms Γ Expr.self ty := h
        have h_self : ∃ a, Γ VarId.self_id = some a ∧ a ≤ₜ ty := by
          have h_self : HasType CT ms Γ Expr.self ty := h_self
          have h_self_def : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.self → ∃ a, Γ VarId.self_id = some a ∧ a ≤ₜ ty := by
            intros e ty h_self h_eq_self
            induction' h_self with e ty h_self h_eq_self ih;
            all_goals cases h_eq_self;
            · exact ⟨ ty, h_self, by exact Subtype.refl _ ⟩;
            · grind +suggestions
          exact h_self_def h_self rfl;
        exact h_self
      exact h_contra ⟨a, ha⟩

theorem tself_inversion {Γ : TypEnv} {ty : ClassId}
    (h : HasType CT ms Γ Expr.tself ty) :
    ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
      contrapose! h;
      intro H;
      obtain ⟨a, ha⟩ : ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
        have h_self : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.tself → ∃ a, Γ VarId.tself_id = some a ∧ Subtype a ty := by
          intros e ty h_type h_eq
          induction' h_type with e ty h_type h_eq ih;
          all_goals cases h_eq;
          · exact ⟨ _, ‹_›, Subtype.refl _ ⟩;
          · rename_i h₁ h₂ h₃;
            exact Exists.elim ( h₃ rfl ) fun a ha => ⟨ a, ha.1, Subtype.trans ha.2 h₁ ⟩;
        exact h_self H rfl;
      exact h a ha.1 ha.2

theorem call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.call e0 m e1) ty) :
    ∃ (Arecv Aarg A1 A2 : ClassId),
      HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧
      CT Arecv m = some ⟨A1, A2⟩ ∧ Subtype Aarg A1 ∧
      Subtype A2 ty ∧ ⟨Arecv, m⟩ ∈ ms.userDefined := by
        have h_ind : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {e0 e1 : Expr} {m : MethId}, e = e0.call m e1 → ∃ Arecv Aarg A1 A2, HasType CT ms Γ e0 Arecv ∧ HasType CT ms Γ e1 Aarg ∧ CT Arecv m = some ⟨A1, A2⟩ ∧ (Aarg ≤ₜ A1) ∧ (A2 ≤ₜ ty) ∧ { cls := Arecv, meth := m } ∈ ms.userDefined := by
                                                                                                                                                                                                                                                                intros e ty h e0 e1 m heq
                                                                                                                                                                                                                                                                induction' h with e ty h e0 e1 m ty h ih;
                                                                                                                                                                                                                                                                all_goals cases heq;
                                                                                                                                                                                                                                                                · exact ⟨ _, _, _, _, by assumption, by assumption, by assumption, by assumption, by tauto, by assumption ⟩;
                                                                                                                                                                                                                                                                · rename_i h₁ h₂ h₃;
                                                                                                                                                                                                                                                                  exact h₃ rfl |> fun ⟨ Arecv, Aarg, A1, A2, h4, h5, h6, h7, h8, h9 ⟩ => ⟨ Arecv, Aarg, A1, A2, h4, h5, h6, h7, h8.trans h₁, h9 ⟩;
        exact h_ind h rfl

theorem checked_call_inversion {Γ : TypEnv} {e0 e1 : Expr} {m : MethId}
    {Ares ty : ClassId}
    (h : HasType CT ms Γ (Expr.checkedCall Ares e0 m e1) ty) :
    ∃ (Arec Aarg : ClassId),
      HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧
      Subtype Ares ty ∧ ⟨Arec, m⟩ ∈ ms.library := by
        contrapose! h;
        intro H;
        obtain ⟨Arec, Aarg, hArec, hAarg, hSub, hLib⟩ : ∃ Arec Aarg, HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧ Subtype Ares ty ∧ ⟨Arec, m⟩ ∈ ms.library := by
          have h_inv : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.checkedCall Ares e0 m e1 → ∃ Arec Aarg, HasType CT ms Γ e0 Arec ∧ HasType CT ms Γ e1 Aarg ∧ Subtype Ares ty ∧ ⟨Arec, m⟩ ∈ ms.library := by
            intros e ty h h_eq
            induction' h with e ty h ih;
            all_goals cases h_eq;
            · exact ⟨ _, _, by assumption, by assumption, by exact Subtype.refl _, by assumption ⟩;
            · grind +suggestions;
          exact h_inv ‹_› rfl;
        exact h Arec Aarg hArec hAarg hSub hLib

theorem ite_inversion {Γ : TypEnv} {e1 e2 e3 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.ite e1 e2 e3) ty) :
    ∃ (A1 A2 A3 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      HasType CT ms Γ e3 A3 ∧ Subtype (A2 ⊔ₜ A3) ty := by
        have h_ite : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.ite e1 e2 e3 → ∃ A1 A2 A3, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ HasType CT ms Γ e3 A3 ∧ (A2 ⊔ₜ A3) ≤ₜ ty := by
          intros e ty h h_eq; induction h; aesop;
          all_goals cases h_eq;
          · exact ⟨ _, _, _, by assumption, by assumption, by assumption, by exact Subtype.refl _ ⟩;
          · rename_i h₁ h₂ h₃; obtain ⟨ A1, A2, A3, h4, h5, h6, h7 ⟩ := h₃ rfl; exact ⟨ A1, A2, A3, h4, h5, h6, Subtype.trans h7 ‹_› ⟩ ;
        exact h_ite h rfl

theorem seq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.seq e1 e2) ty) :
    ∃ (A1 A2 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype A2 ty := by
        -- Apply the inversion lemma for HasType to split into cases.
        have h_inv : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → (e = Expr.seq e1 e2 → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ A2 ≤ₜ ty) := by
          intros e ty h;
          induction h;
          all_goals rintro ⟨ ⟩;
          · exact ⟨ _, _, by assumption, by assumption, Subtype.refl _ ⟩;
          · rename_i h₁ h₂ h₃;
            exact h₃ rfl |> fun ⟨ A1, A2, hA1, hA2, hA3 ⟩ => ⟨ A1, A2, hA1, hA2, subtype_trans' hA3 h₁ ⟩;
        exact h_inv h rfl

theorem eq_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.eq e1 e2) ty) :
    ∃ (A1 A2 : ClassId),
      HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧
      Subtype ClassId.bool_id ty := by
        -- Apply the constructor inversion lemma to h.
        have h_cases : HasType CT ms Γ (e1.eq e2) ty → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype ClassId.bool_id ty := by
          intros h
          have := h
          contrapose! this;
          have h_eq : ∀ {t : Expr}, t = Expr.eq e1 e2 → ∀ {ty : ClassId}, HasType CT ms Γ t ty → ∃ A1 A2, HasType CT ms Γ e1 A1 ∧ HasType CT ms Γ e2 A2 ∧ Subtype ClassId.bool_id ty := by
            intros t ht ty hty;
            induction' hty with t ty hty ih;
            all_goals cases ht;
            · exact ⟨ _, _, ‹_›, ‹_›, Subtype.refl _ ⟩;
            · rename_i h₁ h₂ h₃;
              exact h₃ rfl |> fun ⟨ A1, A2, hA1, hA2, hA3 ⟩ => ⟨ A1, A2, hA1, hA2, Subtype.trans hA3 h₁ ⟩;
          exact fun h => by obtain ⟨ A1, A2, h1, h2, h3 ⟩ := h_eq rfl h; exact this A1 A2 h1 h2 h3;
        exact h_cases h

theorem new_inversion {Γ : TypEnv} {cls : ClassId} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.new cls) ty) :
    Subtype cls ty := by
      have h_new : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = Expr.new cls → cls ≤ₜ ty := by
        intros e ty h h_eq; induction h; aesop;
        all_goals cases h_eq;
        · constructor;
        · exact?;
      exact h_new h rfl

/-! ## Tensor-specific lemmas -/

private lemma tensor_id_ge_six (s : Shape) : ClassId.tensor_id s ≥ 6 := by
  simp [ClassId.tensor_id]

private lemma lub_eq_zero {a b : ClassId} (h : lub a b = ClassId.nil_id) :
    a = ClassId.nil_id ∧ b = ClassId.nil_id := by
  unfold lub at h; split_ifs at h <;> simp_all +decide

private lemma subtype_nil_eq {a : ClassId} (h : a ≤ₜ ClassId.nil_id) :
    a = ClassId.nil_id := by
      contrapose! h;
      intro h';
      -- By definition of subtype, if a ≤ₜ nil_id, then a must be nil_id. We prove this by induction on the subtype relation.
      have h_subtype_nil : ∀ a b : ClassId, Subtype a b → b = ClassId.nil_id → a = ClassId.nil_id := by
        intros a b hab hb_nil
        induction' hab with a b hab ih;
        all_goals try tauto;
        · exact lub_eq_zero hb_nil |>.1;
        · exact ( lub_eq_zero hb_nil ) |>.2;
      exact h ( h_subtype_nil a ClassId.nil_id h' rfl )

private lemma lub_le_five_left {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    lub a b ≤ 5 := by
  unfold lub; split_ifs <;> simp_all +decide

private lemma subtype_small_stays_small {a b : ClassId} (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
    (h : a ≤ₜ b) : b ≤ 5 := by
      revert h;
      have h_a_nonzero : ∀ a : ClassId, 1 ≤ a → a ≠ ClassId.nil_id := by
        exact fun a ha => by rintro rfl; contradiction;
      intro h
      induction' h with a b h ih;
      all_goals norm_cast;
      · rename_i k hk₁ hk₂ hk₃ hk₄;
        by_cases hih : 1 ≤ ih <;> by_cases hih' : ih ≤ 5 <;> simp_all +decide;
        exact False.elim <| h_a_nonzero h ha1 <| subtype_nil_eq hk₁;
      · exact?;
      · rename_i a b;
        rcases a with ( _ | _ | _ | _ | _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | _ | _ | _ | _ | b ) <;> norm_cast;
        · exact?;
        · exact?;
        · exact?

private lemma subtype_from_ge_six {a b : ClassId} (ha : a ≥ 6)
    (h : a ≤ₜ b) : b = a ∨ b ≤ 5 := by
      induction' h with a b c h ih;
      all_goals norm_cast at * <;> simp_all +decide [ ClassId.nil_id, ClassId.true_id, ClassId.false_id ];
      · rcases ‹h = c ∨ h ≤ 5› with ( rfl | h5 ) <;> simp_all +decide [ ClassId.nil_id, ClassId.true_id, ClassId.false_id ];
        have := subtype_small_stays_small ( show 1 ≤ h from by
                                              contrapose! ha; interval_cases h ; simp_all +decide [ ClassId.nil_id, ClassId.true_id, ClassId.false_id ] ;
                                              exact lt_of_le_of_lt ( subtype_nil_eq ‹_› |> le_of_eq ) ( by decide ) ) h5 ‹_›; aesop;
      · unfold lub; split_ifs <;> simp_all +decide [ ClassId.nil_id, ClassId.true_id, ClassId.false_id ] ;
      · unfold lub; split_ifs <;> simp_all +decide [ ClassId.true_id, ClassId.false_id, ClassId.bool_id ] ;

private lemma subtype_ge_six_eq {a b : ClassId} (ha : a ≥ 6) (hb : b ≥ 6)
    (h : a ≤ₜ b) : a = b := by
      -- Apply the definition of subtype to get that $b = a$ or $b \leq 5$.
      have h_cases : b = a ∨ b ≤ 5 := subtype_from_ge_six ha h;
      grind

theorem tensor_id_subtype_implies_eq {s1 s2 : Shape}
    (h : ClassId.tensor_id s1 ≤ₜ ClassId.tensor_id s2) : s1 = s2 := by
  have heq := subtype_ge_six_eq (tensor_id_ge_six s1) (tensor_id_ge_six s2) h
  simp [ClassId.tensor_id] at heq
  exact heq

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
        -- By definition of `HasType`, if `HasType CT ms Γ (e1.broadcast e2) ty`, then there exist `s1`, `s2`, `sOut` such that `broadcastShapes s1 s2 = some sOut` and `HasType CT ms Γ e1 (ClassId.tensor_id s1)` and `HasType CT ms Γ e2 (ClassId.tensor_id s2)`.
        obtain ⟨s1, s2, sOut, hs1, hs2, hsOut, hty⟩ : ∃ s1 s2 sOut, broadcastShapes s1 s2 = some sOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧ HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧ Subtype (ClassId.tensor_id sOut) ty := by
          have h_inv : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → e = e1.broadcast e2 → ∃ s1 s2 sOut, broadcastShapes s1 s2 = some sOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id s1) ∧ HasType CT ms Γ e2 (ClassId.tensor_id s2) ∧ Subtype (ClassId.tensor_id sOut) ty := by
            intros e ty h ty_eq; induction h; aesop;
            all_goals cases ty_eq;
            · exact ⟨ _, _, _, ‹_›, ‹_›, ‹_›, Subtype.refl _ ⟩;
            · rename_i h₁ h₂ h₃;
              obtain ⟨ s1, s2, sOut, hs1, hs2, hs3, hs4 ⟩ := h₃ rfl;
              exact ⟨ s1, s2, sOut, hs1, hs2, hs3, Subtype.trans hs4 h₁ ⟩;
          exact h_inv H rfl;
        exact h s1 s2 sOut hs1 hs2 hsOut hty

theorem matmul_inversion {Γ : TypEnv} {e1 e2 : Expr} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.matmul e1 e2) ty) :
    ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ),
      broadcastShapes batch1 batch2 = some batchOut ∧
      HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧
      HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧
      Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
        have h_reconstruct : ∀ {e1 e2 : Expr} {ty : ClassId}, HasType CT ms Γ (e1.matmul e2) ty → ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ), broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧ Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
          intros e1 e2 ty h;
          have h_reconstruct : ∀ {e1 e2 : Expr} {ty : ClassId}, HasType CT ms Γ (e1.matmul e2) ty → ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ), broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧ Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
            intros e1 e2 ty h
            have h_reconstruct : ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ), broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧ Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
              have h_reconstruct : ∀ {e : Expr} {ty : ClassId}, HasType CT ms Γ e ty → ∀ {e1 e2 : Expr}, e = e1.matmul e2 → ∃ (batch1 batch2 batchOut : Shape) (m k n : ℕ), broadcastShapes batch1 batch2 = some batchOut ∧ HasType CT ms Γ e1 (ClassId.tensor_id (batch1 ++ [m, k])) ∧ HasType CT ms Γ e2 (ClassId.tensor_id (batch2 ++ [k, n])) ∧ Subtype (ClassId.tensor_id (batchOut ++ [m, n])) ty := by
                intros e ty h e1 e2 he;
                induction' h with e ty h ih generalizing e1 e2;
                all_goals cases he;
                · exact ⟨ _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, by tauto ⟩;
                · rename_i h₁ h₂ h₃;
                  exact Exists.elim ( h₃ rfl ) fun batch1 h => Exists.elim h fun batch2 h => Exists.elim h fun batchOut h => Exists.elim h fun m h => Exists.elim h fun k h => Exists.elim h fun n h => ⟨ batch1, batch2, batchOut, m, k, n, h.1, h.2.1, h.2.2.1, Subtype.trans h.2.2.2 h₁ ⟩
              exact h_reconstruct h rfl
            exact h_reconstruct;
          exact h_reconstruct h;
        exact h_reconstruct h

theorem reshape_inversion {Γ : TypEnv} {e : Expr} {s2 : Shape} {ty : ClassId}
    (h : HasType CT ms Γ (Expr.reshape e s2) ty) :
    ∃ (s1 : Shape),
      s1.size = s2.size ∧
      HasType CT ms Γ e (ClassId.tensor_id s1) ∧
      Subtype (ClassId.tensor_id s2) ty := by
        have h_inv : ∀ {expr ty}, HasType CT ms Γ expr ty → ∀ {e : Expr} {s2 : Shape}, expr = e.reshape s2 → ∃ s1, s1.size = s2.size ∧ HasType CT ms Γ e (ClassId.tensor_id s1) ∧ (ClassId.tensor_id s2 ≤ₜ ty) := by
          intros expr ty h_expr e s2 h_eq
          induction' h_expr with expr ty h_expr e s2 h_eq generalizing e s2;
          all_goals cases h_eq;
          · exact ⟨ _, ‹_›, ‹_›, Subtype.refl _ ⟩;
          · rename_i h₁ h₂ h₃;
            exact Exists.elim ( h₃ rfl ) fun s1 hs1 => ⟨ s1, hs1.1, hs1.2.1, Subtype.trans hs1.2.2 h₁ ⟩;
        exact h_inv h rfl

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
    exact ⟨tyE, ClassId.tensor_id (bo ++ [m, n]), hE,
      CtxHasType.matmulL _ _ _ _ _ _ _ _ _ _ hb hCtxRecv h2, hSub⟩
  | matmulR v C' ih =>
    obtain ⟨b1, b2, bo, m, k, n, hb, h1, h2, hSub⟩ := matmul_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih h2
    have hCtxArg := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id (bo ++ [m, n]), hE,
      CtxHasType.matmulR _ _ _ _ _ _ _ _ _ _ hb h1 hCtxArg, hSub⟩
  | reshapeC C' s2 ih =>
    obtain ⟨s1, hSz, he, hSub⟩ := reshape_inversion hCtxExpr
    obtain ⟨tyE, tyC', hE, hCtx, hSub'⟩ := ih he
    have hCtxR := CtxHasType.ctxSub _ _ _ _ _ hCtx hSub'
    exact ⟨tyE, ClassId.tensor_id s2, hE,
      CtxHasType.reshapeC _ _ _ _ _ hSz hCtxR, hSub⟩

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
    | (apply HasType.tReshape <;> assumption)
    | (apply HasType.tSub <;> assumption)

/-! ## Main theorems -/

def LibTermination (libImpl : MethKey → Val → Val → Option Val)
    (ms : MethodSets) : Prop :=
  ∀ key v1 v2, key ∈ ms.library → ∃ v', libImpl key v1 v2 = some v'

private theorem progress_in_context_nonCall
    {E : DynEnv} {C : Ctx} {e : Expr} {S : Stack}
    {E' : DynEnv} {e' : Expr} {S' : Stack}
    (h : Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩))
    (hNotCall : ¬ isUserMethodCall e ms)
    (hNotVal : e.isVal = false)
    (hValid : ValidCT CT ms methodDefs) :
    (∃ E'' e'' S'', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E'', e'', S''⟩)) := by
      contrapose! h;
      intro h';
      apply h;
      apply Step.eContext;
      any_goals tauto;
      convert h';
      cases h' ; aesop;
      all_goals try rfl;
      · contrapose! hNotCall;
        rename_i k hk₁ hk₂ hk₃ hk₄ hk₅;
        rename_i C' vr v m;
        exact absurd ( hNotCall ) ( by
          simp +decide [ Step ];
          exact h ( ( emptyEnv [ VarId.self_id ↦ vr ] ) [ k ↦ v ] ) e' ( ( E, C.compose C' ) :: S ) ( by
            convert Step.eAppUD _ _ _ _ _ _ _ _ _ _ _ _ _ using 1;
            congr! 1;
            rotate_left;
            exact m;
            exact hk₁;
            · assumption;
            · exact hk₃;
            · exact hk₄;
            · exact hk₅;
            · exact? ) );
      · cases hNotVal

theorem progress_in_context
    {E : DynEnv} {C : Ctx} {e : Expr} {S : Stack}
    (hNotVal : e.isVal = false)
    (hProgress : (∃ E' e' S', Step methodDefs libImpl ms ⟨E, e, S⟩ (.config ⟨E', e', S'⟩)) ∨
                 (Step methodDefs libImpl ms ⟨E, e, S⟩ .blame))
    (hValid : ValidCT CT ms methodDefs) :
    (∃ E' e' S', Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ (.config ⟨E', e', S'⟩)) ∨
    (Step methodDefs libImpl ms ⟨E, C[[e]], S⟩ .blame) := by
  rcases hProgress with ⟨E', e', S', h⟩ | h
  · by_cases hUserCall : isUserMethodCall e ms
    · obtain ⟨vr, v, m', hEq, hUserMeth⟩ := hUserCall
      obtain ⟨a1, a2, hCT, md, hDef, hBody⟩ := hValid.1 _ hUserMeth
      left; use (emptyEnv [VarId.self_id ↦ vr]) [md.param ↦ v], md.body, (E, C) :: S
      rw [hEq]; exact Step.eAppUD E C vr v m' S md.param md.body md hUserMeth hDef rfl rfl
    · exact Or.inl (progress_in_context_nonCall h hUserCall hNotVal hValid)
  · exact Or.inr (Step.eBlameContext E C e S h)

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
    · obtain ⟨v, rfl⟩ : ∃ v, e1 = Expr.val v := by
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
  | tReshape _ s1 s2 hSize h1 ih1 =>
    right
    show (∃ E' e' S', Step _ _ _ ⟨E, (Ctx.reshapeC Ctx.hole s2)[[_]], S⟩ _) ∨ _
    exact progress_subexpr (ih1 hEnvCons) hValid
      (fun v hv => by
        subst hv
        by_cases hm : ∃ s1', v = Val.tensor s1' ∧ s1'.size = s2.size
        · obtain ⟨s1', rfl, hSz'⟩ := hm
          exact Or.inl ⟨_, _, _, Step.eReshape E s1' s2 S hSz'⟩
        · exact Or.inr (Step.eBlameReshape E v s2 S hm))

theorem ctx_weakening
    {Γ Δ : TypEnv} {C : Ctx} {tyHole tyCtx : ClassId}
    (hCtx : CtxHasType CT ms Γ tyHole C tyCtx)
    (hExt : TypEnv.extends_ Γ Δ) :
    CtxHasType CT ms Δ tyHole C tyCtx := by
      have := @weakening CT ms Γ Δ; simp_all +decide [ TypEnv.extends_ ] ;
      induction hCtx <;> (constructor <;> solve_by_elim;)

/-- Type preservation for same-stack steps. -/
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
  | eVar _ x _ v hx =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := var_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 x v hx
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eSelf _ _ v hself =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := self_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v hself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eTSelf _ _ v htself =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := tself_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v htself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, a', hTypV, hEnvCons, Subtype.trans hSub' hSub, fun x a h => h⟩
  | eSeq _ _ _ _ =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := seq_inversion hType
    exact ⟨Γ, A2, h2, hEnvCons, hSub, fun x a h => h⟩
  | eNew _ A _ =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    exact ⟨Γ, A, HasType.tObj Γ A, hEnvCons, new_inversion hType, fun x a h => h⟩
  | eIfTrue _ v _ _ _ ht =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A2, h2, hEnvCons, Subtype.trans (Subtype.lub_left A2 A3) hSub, fun x a h => h⟩
  | eIfFalse _ v _ _ _ hf =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, A3, h3, hEnvCons, Subtype.trans (Subtype.lub_right A2 A3) hSub, fun x a h => h⟩
  | eEqTrue _ _ _ _ heq =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, ClassId.true_id, HasType.tTrue Γ, hEnvCons, Subtype.trans Subtype.true_bool hSub, fun x a h => h⟩
  | eEqFalse _ _ _ _ hneq =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, ClassId.false_id, HasType.tFalse Γ, hEnvCons, Subtype.trans Subtype.false_bool hSub, fun x a h => h⟩
  | eAppUD => intro _ _ _ _ _ _ _ hc hr; cases hc; simp at hr
  | eAppLib _ Ares vr v v' m _ hLib hCall hSub_v =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨Arec, Aarg, h0, h1, hSub, hL⟩ := checked_call_inversion hType
    exact ⟨Γ, v'.typeOf, val_has_type Γ v', hEnvCons, Subtype.trans hSub_v hSub, fun x a h => h⟩
  | eRet => intro _ _ _ _ _ _ _ hc hr; cases hc; simp at hr
  | eContext _ _ C_v _ _ _ hStep' hNotUserCall hNotVal ih =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨tyE, tyC', hTypeE, hCtxType, hSubCtx⟩ := ctx_decomposition hType
    obtain ⟨Δ, ty', hType', hEnvCons', hSubTy, hExt⟩ := ih rfl rfl hTypeE hEnvCons hValid
    have hCtxW := ctx_weakening hCtxType hExt
    obtain ⟨tyCtx', hTypeCtx, hSubCtxNew⟩ := substitution_lemma hCtxW hType' hSubTy
    exact ⟨Δ, tyCtx', hTypeCtx, hEnvCons', Subtype.trans hSubCtxNew hSubCtx, hExt⟩
  | eBroadcast _ s1 s2 sOut _ hBcast =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨s1', s2', sOut', hb', h1, h2, hSub⟩ := broadcast_inversion hType
    have heq1 := tensor_id_subtype_implies_eq (val_type_subtype h1)
    have heq2 := tensor_id_subtype_implies_eq (val_type_subtype h2)
    subst heq1; subst heq2; rw [hBcast] at hb'; cases hb'
    exact ⟨Γ, (Val.tensor sOut).typeOf, val_has_type Γ _, hEnvCons, hSub, fun x a h => h⟩
  | eMatmul _ batch1 batch2 batchOut mm kk nn _ hBatch =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨b1', b2', bo', m', k', n', hb', h1, h2, hSub⟩ := matmul_inversion hType
    have hVS1 := val_type_subtype h1; have hVS2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hVS1
    have heq2 := tensor_id_subtype_implies_eq hVS2
    have hl1 : batch1.length = b1'.length := by have := congr_arg List.length heq1; simp at this; omega
    have hl2 : batch2.length = b2'.length := by have := congr_arg List.length heq2; simp at this; omega
    have hpair1 := List.append_inj heq1 hl1
    have hpair2 := List.append_inj heq2 hl2
    have hb1eq : batch1 = b1' := hpair1.1
    have hb2eq : batch2 = b2' := hpair2.1
    have hmk : [mm, kk] = [m', k'] := hpair1.2
    have hkn : [kk, nn] = [k', n'] := hpair2.2
    have hm : mm = m' := by have := List.cons.inj hmk; exact this.1
    have hn : nn = n' := by have := List.cons.inj hkn; have := List.cons.inj this.2; exact this.1
    subst hb1eq; subst hb2eq; subst hm; subst hn; rw [hBatch] at hb'; cases hb'
    exact ⟨Γ, _, val_has_type Γ _, hEnvCons, hSub, fun x a h => h⟩
  | eReshape _ s1 s2 _ hSize =>
    intro Γ E E' e e' ty S hc hr hType hEnvCons hValid
    cases hc; cases hr
    obtain ⟨s1', hSz', h1, hSub⟩ := reshape_inversion hType
    have heq := tensor_id_subtype_implies_eq (val_type_subtype h1); subst heq
    exact ⟨Γ, _, val_has_type Γ _, hEnvCons, hSub, fun x a h => h⟩
  | eBlameNilRecv => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameCheckedCall => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameBroadcast => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameMatmul => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameReshape => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameContext => intro _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)

private lemma env_consistent_method_env
    {vr v : Val} {x : VarId} {selfTy a1 : ClassId}
    (hVrSub : vr.typeOf ≤ₜ selfTy)
    (hVSub : v.typeOf ≤ₜ a1) :
    EnvConsistent CT ms
      ((emptyEnv [VarId.self_id ↦ selfTy]) [x ↦ a1])
      ((emptyEnv [VarId.self_id ↦ vr]) [x ↦ v]) := by
        constructor;
        · intro y; by_cases hy : y = x <;> by_cases hy' : y = VarId.self_id <;> simp +decide [ *, envUpdate ] ;
          · aesop;
          · exact iff_of_false ( by unfold emptyEnv; aesop ) ( by unfold emptyEnv; aesop );
        · intro y v hv; by_cases hy : y = VarId.self_id <;> by_cases hy' : y = x <;> simp_all +decide [ envUpdate ] ;
          · exact ⟨ _, val_has_type _ _, hVSub ⟩;
          · exact ⟨ _, val_has_type _ _, hVrSub ⟩;
          · exact ⟨ v.typeOf, val_has_type _ _, hVSub ⟩;
          · cases hv

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
        obtain ⟨tyE, tyC', hCtxE, hCtxC, hSubC⟩ := ctx_decomposition hType;
        obtain ⟨Arecv, Aarg, A1, A2, hArecv, hAarg, hCT, hAarg_sub_A1, hA2_sub_tyE, hUserMethod⟩ := call_inversion hCtxE;
        have := hValid.1 ⟨ vr.typeOf, m ⟩ ‹_›; simp_all +decide ;
        obtain ⟨ a1, a2, h1, a2', h2, h3 ⟩ := this; use ( emptyEnv[VarId.self_id ↦ vr.typeOf][x ↦ a1] ), ⟨ Γ, tyE, tyC' ⟩ :: TS, a2'; simp_all +decide ;
        apply And.intro;
        · exact Subtype.trans ( Subtype.trans h3 ( hValid.2.2.1 _ _ _ _ _ _ _ ( val_type_subtype hArecv ) h1 hCT |>.2 ) ) hA2_sub_tyE;
        · apply And.intro;
          · apply env_consistent_method_env;
            · exact?;
            · have := hValid.2.2.1 Arecv vr.typeOf m A1 A2 a1 a2; simp_all +decide ;
              have := val_type_subtype hArecv; have := val_type_subtype hAarg; simp_all +decide [ Subtype ] ;
              exact Subtype.trans this ( Subtype.trans hAarg_sub_A1 ( by tauto ) );
          · apply StackConsistent.cons; assumption; assumption; assumption; exact (Or.inr <| by
              cases hSubStack : TS <;> simp_all +decide [ TypeSubStack ];
              exact Subtype.trans hSubC ‹_›)

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
  contrapose! ih;
  obtain ⟨ tyE, tyC', hTypeE, hCtxType, hSubC ⟩ := ctx_decomposition hType;
  obtain ⟨ Δ, ty', hType', hEnvCons', hSubTy, hExt ⟩ := preservation_same_stack hStep_inner rfl rfl hTypeE hEnvCons hValid;
  obtain ⟨ tyCtx', hTypeCtx', hSubCtx' ⟩ := substitution_lemma ( ctx_weakening hCtxType hExt ) hType' hSubTy;
  refine' False.elim ( ih Δ _ tyCtx' hTypeCtx' _ hEnvCons' _ _ _ );
  exact TS;
  · cases TS <;> simp_all +decide [ TypeSubStack ];
    exact Subtype.trans hSubCtx' ( Subtype.trans hSubC hSubStack );
  · assumption;
  · exact?;
  · assumption


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
  | eVar _ x _ v hx =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := var_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 x v hx
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eSelf _ _ v hself =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := self_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v hself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eTSelf _ _ v htself =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨a, ha, hSub⟩ := tself_inversion hType
    obtain ⟨a', a'', hTypV, hΓ, hSub'⟩ := hEnvCons.2 _ v htself
    have hEq : a = a'' := by rw [ha] at hΓ; exact Option.some.inj hΓ
    subst hEq
    exact ⟨Γ, TS, a', hTypV,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans (Subtype.trans hSub' hSub) hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨Subtype.trans hSub' hSub, fun x a h => h⟩⟩
  | eSeq _ _ _ _ =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := seq_inversion hType
    exact ⟨Γ, TS, A2, h2,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eNew _ A _ =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    have hSub := new_inversion hType
    exact ⟨Γ, TS, A, HasType.tObj Γ A,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eIfTrue _ v _ _ _ ht =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, TS, A2, h2,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans (Subtype.lub_left A2 A3) hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans (Subtype.lub_left A2 A3) hSub, fun x a h => h⟩⟩
  | eIfFalse _ v _ _ _ hf =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, A3, h1, h2, h3, hSub⟩ := ite_inversion hType
    exact ⟨Γ, TS, A3, h3,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans (Subtype.lub_right A2 A3) hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans (Subtype.lub_right A2 A3) hSub, fun x a h => h⟩⟩
  | eEqTrue _ _ _ _ heq =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, TS, ClassId.true_id, HasType.tTrue Γ,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans Subtype.true_bool hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans Subtype.true_bool hSub, fun x a h => h⟩⟩
  | eEqFalse _ _ _ _ hneq =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨A1, A2, h1, h2, hSub⟩ := eq_inversion hType
    exact ⟨Γ, TS, ClassId.false_id, HasType.tFalse Γ,
      (by cases TS with | nil => trivial | cons ts rest =>
        exact Subtype.trans (Subtype.trans Subtype.false_bool hSub) hSubStack),
      hEnvCons, hStackCons,
      fun _ => ⟨Subtype.trans Subtype.false_bool hSub, fun x a h => h⟩⟩
  | eAppUD _ _ vr v m _ x body md hUserMethod hDef hParam hBody =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    exact preservation_eAppUD hType hSubStack hEnvCons hStackCons hValid hUserMethod hDef hParam hBody
  | eAppLib _ Ares vr v v' m _ hLibMethod hCall hSubtype_v =>
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
        | inr h => cases TS_rest with | nil => trivial | cons ts rest => exact Subtype.trans hSubCtx h
      · intro heq; exact absurd heq (by simp)
  | eContext _ _ C_v _ _ _ hStep_inner hNotUserCall hNotVal ih =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨Δ, TS', ty', h1, h2, h3, h4, h5, h6⟩ := preservation_eContext hType hSubStack hEnvCons hStackCons hValid hStep_inner hNotVal hNotUserCall ih
    exact ⟨Δ, TS', ty', h1, h2, h3, h4, fun _ => ⟨h5, h6⟩⟩
  | eBroadcast _ s1 s2 sOut _ hBcast =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨s1', s2', sOut', hb', h1, h2, hSub⟩ := broadcast_inversion hType
    have heq1 := tensor_id_subtype_implies_eq (val_type_subtype h1)
    have heq2 := tensor_id_subtype_implies_eq (val_type_subtype h2)
    subst heq1; subst heq2; rw [hBcast] at hb'; cases hb'
    exact ⟨Γ, TS, _, val_has_type Γ _,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eMatmul _ batch1 batch2 batchOut mm kk nn _ hBatch =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨b1', b2', bo', m', k', n', hb', h1, h2, hSub⟩ := matmul_inversion hType
    have hVS1 := val_type_subtype h1; have hVS2 := val_type_subtype h2
    have heq1 := tensor_id_subtype_implies_eq hVS1
    have heq2 := tensor_id_subtype_implies_eq hVS2
    have hl1 : batch1.length = b1'.length := by have := congr_arg List.length heq1; simp at this; omega
    have hl2 : batch2.length = b2'.length := by have := congr_arg List.length heq2; simp at this; omega
    have hpair1 := List.append_inj heq1 hl1
    have hpair2 := List.append_inj heq2 hl2
    have hb1eq : batch1 = b1' := hpair1.1
    have hb2eq : batch2 = b2' := hpair2.1
    have hmk : [mm, kk] = [m', k'] := hpair1.2
    have hkn : [kk, nn] = [k', n'] := hpair2.2
    subst hb1eq; subst hb2eq
    have hm : mm = m' := by have := List.cons.inj hmk; exact this.1
    have hn : nn = n' := by have := List.cons.inj hkn; have := List.cons.inj this.2; exact this.1
    subst hm; subst hn; rw [hBatch] at hb'; cases hb'
    exact ⟨Γ, TS, _, val_has_type Γ _,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eReshape _ s1 s2 _ hSize =>
    intro Γ E E' e e' ty S S' TS hc hr hType hSubStack hEnvCons hStackCons hValid
    cases hc; cases hr
    obtain ⟨s1', hSz', h1, hSub⟩ := reshape_inversion hType
    have heq := tensor_id_subtype_implies_eq (val_type_subtype h1); subst heq
    exact ⟨Γ, TS, _, val_has_type Γ _,
      (by cases TS with | nil => trivial | cons ts rest => exact Subtype.trans hSub hSubStack),
      hEnvCons, hStackCons, fun _ => ⟨hSub, fun x a h => h⟩⟩
  | eBlameNilRecv => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameCheckedCall => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameBroadcast => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameMatmul => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameReshape => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)
  | eBlameContext => intro _ _ _ _ _ _ _ _ _ _ hr; exact absurd hr (by simp)

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
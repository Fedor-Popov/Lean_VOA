import VOA.Classification.COne.PlusSplitTransport

/-! Equal-bottom splitting on arbitrary two-step intervals. -/
set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.PlusSplitting
open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

set_option maxHeartbeats 1200000 in
-- Nested mode algebras and the c/a quotient require additional elaboration.
/-- Transfer a whole-extension splitting theorem to arbitrary intervals. -/
theorem relativeComplement_of_whole_factorBottoms
    (hC2 : C2Cofinite W)
    (A : WeakModule W M) {a b c : Submodule (modeAlg A) M}
    (hab : a ⋖ b) (hbc : b ⋖ c) (h k : ℂ)
    (hb : FactorBottom A a b h) (ht : FactorBottom A b c k)
    (split : ∀ {X : Type u} [AddCommGroup X] [Module ℂ X]
      (B : WeakModule W X) (P : Submodule (modeAlg B) X),
      IsAtom P → P ⋖ ⊤ → FactorBottom B ⊥ P h → FactorBottom B P ⊤ k →
      ∃ Q : Submodule (modeAlg B) X, IsCompl P Q) :
    ∃ d : Submodule (modeAlg A) M,
      a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  let C : WeakModule W c := WeakModule.submodule A (ofR A c)
  let ι : C.Hom A := { toLinearMap := (c.restrictScalars ℂ).subtype
                       map_act := fun _ _ _ => rfl }
  have hi : Function.Injective ι.toLinearMap := Subtype.val_injective
  have hr : modeMap ι ⊤ = c := by
    ext x
    change (∃ y : c, y ∈ (⊤ : Submodule ℂ c) ∧ (y : M) = x) ↔ x ∈ c
    simp
  have hk : modeComap ι ⊥ = ⊥ := by
    ext x
    change ι.toLinearMap x = 0 ↔ x = 0
    exact map_eq_zero_iff ι.toLinearMap hi
  let a' := modeComap ι a
  let b' := modeComap ι b
  have ha : modeMap ι a' = a := by
    rw [modeMap_comap, hr, inf_eq_left.mpr (hab.le.trans hbc.le)]
  have hb' : modeMap ι b' = b := by
    rw [modeMap_comap, hr, inf_eq_left.mpr hbc.le]
  have hc : modeComap ι c = ⊤ := by ext x; exact iff_true_intro x.property
  have hab' : a' ⋖ b' := modeComap_covBy ι hab (by rw [hr]; exact hbc.le)
  have hbc' : b' ⋖ ⊤ := by
    have := modeComap_covBy ι hbc (by rw [hr])
    rwa [hc] at this
  have hlo : FactorBottom C a' b' h := by
    apply (factorBottom_modeMap_iff hC2 ι a' b' (by rw [hk]; exact bot_le) h).mp
    rwa [ha, hb']
  have hup : FactorBottom C b' ⊤ k := by
    apply (factorBottom_modeMap_iff hC2 ι b' ⊤ (by rw [hk]; exact bot_le) k).mp
    rwa [hb', hr]
  let Q : WeakModule W (↥c ⧸ (ofR C a').carrier) := WeakModule.quotient C (ofR C a')
  let π : C.Hom Q := WeakModule.quotientMk C (ofR C a')
  have hker : modeComap π ⊥ = a' := by
    ext x
    exact Submodule.Quotient.mk_eq_zero ((ofR C a').carrier)
  have hzero : modeMap π a' = ⊥ := by
    ext y
    change (∃ x, x ∈ a' ∧ π.toLinearMap x = y) ↔ y = 0
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (Submodule.Quotient.mk_eq_zero ((ofR C a').carrier)).mpr hx
    · rintro rfl; exact ⟨0, a'.zero_mem, map_zero _⟩
  have htop : modeMap π ⊤ = ⊤ := by
    ext y
    change (∃ x, x ∈ (⊤ : Submodule ℂ c) ∧ π.toLinearMap x = y) ↔ True
    simp only [Submodule.mem_top, true_and, iff_true]
    exact ((ofR C a').carrier).mkQ_surjective y
  have hatom : IsAtom (modeMap π b') := by
    have := modeMap_covBy π hab' (by rw [hker])
    rw [hzero] at this
    exact bot_covBy_iff.mp this
  have hcoat : modeMap π b' ⋖ ⊤ := by
    have := modeMap_covBy π hbc' (by rw [hker]; exact hab'.le)
    rwa [htop] at this
  have hloQ : FactorBottom Q ⊥ (modeMap π b') h := by
    have := (factorBottom_modeMap_iff hC2 π a' b' (by rw [hker]) h).mpr hlo
    rwa [hzero] at this
  have hupQ : FactorBottom Q (modeMap π b') ⊤ k := by
    have := (factorBottom_modeMap_iff hC2 π b' ⊤ (by rw [hker]; exact hab'.le) k).mpr hup
    rwa [htop] at this
  obtain ⟨S, hS⟩ := split Q (modeMap π b') hatom hcoat hloQ hupQ
  obtain ⟨d', had, hdc, hbi, hbu⟩ := relativeComplement_of_modeMap π hab'.le
    (show b' ≤ ⊤ from le_top) (by rw [hker])
    ⟨S, by rw [hzero]; exact bot_le, by rw [htop]; exact le_top,
      by rw [hzero]; exact hS.inf_eq_bot, by rw [htop]; exact hS.sup_eq_top⟩
  refine ⟨modeMap ι d', ?_, ?_, ?_, ?_⟩
  · rw [← ha]; exact modeMap_mono ι had
  · exact (modeMap_mono ι hdc).trans_eq hr
  · rw [← hb', ← ha, ← hbi]
    apply Submodule.restrictScalars_injective ℂ
    exact (Submodule.map_inf _ hi).symm
  · calc
      b ⊔ modeMap ι d' = modeMap ι (b' ⊔ d') := by rw [modeMap_sup, hb']
      _ = c := by rw [hbu]; exact hr

/-- Equal intrinsic bottoms split arbitrary simple two-step intervals. -/
theorem relativeComplement_of_semisimpleZhu_equalBottom
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (A : WeakModule W M) {a b c : Submodule (modeAlg A) M}
    (hab : a ⋖ b) (hbc : b ⋖ c) (h : ℂ)
    (hb : FactorBottom A a b h) (ht : FactorBottom A b c h) :
    ∃ d : Submodule (modeAlg A) M,
      a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c :=
  relativeComplement_of_whole_factorBottoms hC2 A hab hbc h h hb ht
    (fun B P hP hQ hb ht =>
      exists_isCompl_of_semisimpleZhu_equalBottom hC2 hss B P hP hQ h hb ht)

end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting

/-- The arbitrary-interval lifting premise, discharged. -/
theorem V2mPlus_equalBottomZhuLifting : V2mPlusEqualBottomZhuLifting := by
  intro hzhu m hm hm2 M _ _ N a b c h hab hbc hb ht
  exact relativeComplement_of_semisimpleZhu_equalBottom (V2mPlus_c2Cofinite m hm)
    (hzhu m hm hm2) N.toWeakModule hab hbc h hb ht

/-- Conditional rationality without the equal-bottom lifting premise. -/
theorem rationality_of_twistedTopModels_normalForms_resonant
    (ht : V2mPlusTwistedTopModels) (hr : V2mPlusZhuNormalFormReductions)
    (hgen : V2mPlusResonantGeneratorComplements) : V2mPlusRationalFactGe2 :=
  rationality_of_twistedTopModels_reductions ht hr V2mPlus_equalBottomZhuLifting hgen

end VOA.Classification.COne

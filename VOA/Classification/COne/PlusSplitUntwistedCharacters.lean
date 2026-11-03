import VOA.Classification.COne.PlusSplitSignCharacter
import VOA.Classification.COne.PlusSplitExplicitInputs

/-! # All untwisted characters and a smaller rationality input list

Every untwisted row of the character table is realized on the
actual Zhu algebra. This does not assert the stronger `TopModel` predicate.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable

theorem untwisted_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (i : Label m) (hi : IsUntwisted i) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ := by
  rcases i with r | i
  · exact charged_character_exists m hm hm2 r
  · fin_cases i
    · exact vacuum_character_exists m hm hm2
    · exact sign_character_exists m hm hm2
    · exact half_plus_character_exists m hm hm2
    · exact half_minus_character_exists m hm hm2
    all_goals simp [IsUntwisted] at hi

theorem label_eq_of_hasValues (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∀ (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ) (i j : Label m),
      HasValues m hm i χ → HasValues m hm j χ → i = j := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  intro χ i j hi hj
  apply values_injective m hm2 _ (twistedScale_ne_zero m)
  exact Prod.ext (Complex.ofReal_injective (hi.1.symm.trans hj.1))
    (Prod.ext (Complex.ofReal_injective (hi.2.1.symm.trans hj.2.1))
      (Complex.ofReal_injective (hi.2.2.symm.trans hj.2.2)))

/-- The m+3 untwisted characters alone give an unconditional lower bound. -/
theorem untwisted_finrank_lower_bound (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    m + 3 ≤ Module.finrank ℂ (VOA.A (V2mPlus m hm)) := by
  classical
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  let f : Fin (m-1) ⊕ Fin 4 → Label m := Sum.map id (Fin.castLE (by omega))
  have hf : Function.Injective f := by
    intro i j he
    dsimp [f] at he
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Sum.inl.inj he)
    · cases he
    · cases he
    · have hv : i.val = j.val := congrArg (fun x : Fin 8 => x.val) (Sum.inr.inj he)
      exact congrArg Sum.inr (Fin.ext hv)
  have hex : ∀ i, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (f i) χ := by
    intro i
    apply untwisted_character_exists m hm hm2
    rcases i with i | i
    · trivial
    · exact i.isLt
  choose χ hχ using hex
  have hχi : Function.Injective χ := by
    intro i j he
    apply hf
    exact label_eq_of_hasValues m hm hm2 (χ i) (f i) (f j) (hχ i) (he.symm ▸ hχ j)
  have h := ((linearIndependent_algHom_toLinearMap ℂ (VOA.A (V2mPlus m hm)) ℂ).comp
    χ hχi).fintype_card_le_finrank
  simpa [Fintype.card_sum, Fintype.card_fin,
    show m-1+4 = m+3 by omega] using h

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable

/-- A proved character-level statement, weaker than untwisted top models. -/
def V2mPlusUntwistedCharacters : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Label m, IsUntwisted i →
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ

theorem V2mPlus_untwistedCharacters : V2mPlusUntwistedCharacters :=
  untwisted_character_exists

theorem zhuDistinctCharacters_of_twistedTopModels (ht : V2mPlusTwistedTopModels) :
    V2mPlusZhuDistinctCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have hex : ∀ i : Label m, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ := by
    intro i
    by_cases hi : IsUntwisted i
    · exact untwisted_character_exists m hm hm2 i hi
    · exact character_exists_of_topModel m hm i (ht m hm hm2 i hi)
  choose χ hχ using hex
  let e : Label m ≃ Fin (m+7) := Fintype.equivFinOfCardEq (card_label m hm)
  exact ⟨χ ∘ e.symm, (characters_injective m hm hm2 χ hχ).comp e.symm.injective⟩

/-- The sign/half top-model premise is not required for rationality.
The twisted, normal-form, equal-bottom, and resonant inputs remain explicit. -/
theorem rationality_of_twistedTopModels_reductions
    (ht : V2mPlusTwistedTopModels) (hr : V2mPlusZhuNormalFormReductions)
    (hlift : V2mPlusEqualBottomZhuLifting) (hgen : V2mPlusResonantGeneratorComplements) :
    V2mPlusRationalFactGe2 :=
  rationality_of_character_bottom_generator_inputs
    (zhuDimensionBound_of_normalFormReductions hr)
    (zhuDistinctCharacters_of_twistedTopModels ht) hlift hgen

end VOA.Classification.COne

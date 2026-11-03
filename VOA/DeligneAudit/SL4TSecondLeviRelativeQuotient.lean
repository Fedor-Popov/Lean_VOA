import VOA.DeligneAudit.SL4TSecondLeviPresentation

/-! Surjective and Cartan-equivariant evaluation from the relative symmetric-function quotient. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B : Type} [CommRing B] [Algebra ℂ B]

theorem secondLeviModePowerSum_symmetric (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    secondLeviModePowerSum (B := B) e₁ e₂ j s ∈ secondLeviSymmetricModes e₁ e₂ := by
  intro e
  by_cases hj : j = 0
  · simp only [secondLeviModePowerSum, if_pos hj, map_sum, map_pow, rename_X,
      secondLeviSlotPermutation, Equiv.sumCongr_apply, Sum.map_inl]
    exact Equiv.sum_comp e.1
      (fun i => (X (.inl i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) ^ s)
  · simp only [secondLeviModePowerSum, if_neg hj, map_sum, map_pow, rename_X,
      secondLeviSlotPermutation, Equiv.sumCongr_apply, Sum.map_inr]
    exact Equiv.sum_comp e.2
      (fun i => (X (.inr i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B) ^ s)

/-- The source symbol of either retained Cartan mode. -/
def secondLeviSourceCartanSymbol (e₁ e₂ : ℕ) (i : Fin 2) (U : B) (s : ℕ) :
    secondLeviSymmetricModes (B := B) e₁ e₂ :=
  ⟨MvPolynomial.C U +
    (if i = 0 then (-2 : ℂ) else 1) • secondLeviModePowerSum e₁ e₂ 0 s -
      secondLeviModePowerSum e₁ e₂ 1 s,
    (secondLeviSymmetricModes e₁ e₂).sub_mem
      ((secondLeviSymmetricModes e₁ e₂).add_mem (fun _ => rename_C _ _)
        ((secondLeviSymmetricModes e₁ e₂).smul_mem
          (secondLeviModePowerSum_symmetric e₁ e₂ 0 s) _))
      (secondLeviModePowerSum_symmetric e₁ e₂ 1 s)⟩

/-- The two relative relation windows over the actual three-Grassmannian coefficient algebra. -/
abbrev RadicalSecondLeviRelativeRing (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) :=
  secondLeviSymmetricModes (B := RadicalGrassmannianRing a b c d) e₁ e₂ ⧸
    secondLeviRelativeIdeal e₁ e₂
      (fun j => (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat)
      (radicalLeviPowerSum a b c d)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
variable (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
variable (hm : ∀ j, 0 ≤ a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩)

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- Evaluation descends through both finite relative relation windows. -/
def radicalSecondLeviRelativeEvaluation :
    RadicalSecondLeviRelativeRing a b c d e₁ e₂ →ₗ[ℂ]
      secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ :=
  (secondLeviRelativeIdeal e₁ e₂
    (fun j => (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat)
    (radicalLeviPowerSum a b c d)).restrictScalars ℂ |>.liftQ
      (secondLeviSymmetricMultiplicityEvaluation (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂) (by
          intro P hP
          apply Subtype.ext
          have hz := radicalSecondLeviRelativeIdeal_le_relations ρ w a b c h d e₁ e₂ hm
            hP (1 : RadicalGrassmannianRing a b c d)
          simpa only [map_one, one_mul] using hz)

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
theorem radicalSecondLeviRelativeEvaluation_mk
    (P : secondLeviSymmetricModes (B := RadicalGrassmannianRing a b c d) e₁ e₂) :
    radicalSecondLeviRelativeEvaluation ρ w a b c h d e₁ e₂ hm (Ideal.Quotient.mk _ P) =
      secondLeviSymmetricMultiplicityEvaluation (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The relative symmetric-function quotient surjects onto the second multiplicity. -/
theorem radicalSecondLeviRelativeEvaluation_surjective :
    Function.Surjective (radicalSecondLeviRelativeEvaluation ρ w a b c h d e₁ e₂ hm) := by
  intro x
  obtain ⟨P, rfl⟩ := radicalSecondLeviEvaluation_surjective ρ w a b c h d e₁ e₂ x
  exact ⟨Ideal.Quotient.mk _ P, rfl⟩

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The descended surjection intertwines both positive Cartans with their source symbols. -/
theorem radicalSecondLeviRelativeEvaluation_cartan (i : Fin 2) (s : ℕ) (hs : 0 < s)
    (P : RadicalSecondLeviRelativeRing a b c d e₁ e₂) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b c h d
    let π := radicalSecondLeviRelativeEvaluation ρ w a b c h d e₁ e₂ hm
    secondLeviQuotientCartan Q β e₁ e₂ i s (π P).val =
      (π (Ideal.Quotient.mk _
        (secondLeviSourceCartanSymbol e₁ e₂ i (radicalLeviPowerSum a b c d i s) s) * P)).val := by
  obtain ⟨R, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ P
  change secondLeviQuotientCartan _ _ e₁ e₂ i s
    (secondLeviQuotientEvaluation _ _ e₁ e₂ R.val) =
      secondLeviQuotientEvaluation _ _ e₁ e₂
        ((secondLeviSourceCartanSymbol e₁ e₂ i
          (radicalLeviPowerSum a b c d i s) s).val * R.val)
  exact radicalSecondLeviEvaluation_cartan ρ w a b c h d e₁ e₂ i s hs R.val

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviModePowerSum_symmetric
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_mk
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviRelativeEvaluation_cartan

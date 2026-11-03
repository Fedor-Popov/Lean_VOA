import VOA.DeligneAudit.SL4TSecondLeviPowerSums

/-! Two-Cartan propagation of the relative relations on the actual second Levi evaluator. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- Coefficients embed as constant mode polynomials. -/
def secondLeviBaseEmbedding (e₁ e₂ : ℕ) :
    B →ₐ[ℂ] MvPolynomial (SecondLeviModeSlot e₁ e₂) B where
  toRingHom := MvPolynomial.C
  commutes' := fun _ => rfl

/-- Both actual Cartan formulas isolate the two power sums on base-saturated relations. -/
theorem secondLeviQuotientEvaluation_saturated_generators (e₁ e₂ s : ℕ)
    (u v : B)
    (hu : ∀ φ, Q.op 6 (s + 1) (β φ) = β (u * φ))
    (hv : ∀ φ, Q.op 7 (s + 1) (β φ) = β (v * φ))
    {R : MvPolynomial (SecondLeviModeSlot e₁ e₂) B}
    (hR : R ∈ baseSaturatedEvaluationKernel (secondLeviBaseEmbedding e₁ e₂)
      (secondLeviQuotientEvaluation Q β e₁ e₂)) :
    secondLeviModePowerSum e₁ e₂ 0 (s + 1) * R ∈
        baseSaturatedEvaluationKernel (secondLeviBaseEmbedding e₁ e₂)
          (secondLeviQuotientEvaluation Q β e₁ e₂) ∧
      secondLeviModePowerSum e₁ e₂ 1 (s + 1) * R ∈
        baseSaturatedEvaluationKernel (secondLeviBaseEmbedding e₁ e₂)
          (secondLeviQuotientEvaluation Q β e₁ e₂) := by
  apply twoCartan_saturatedKernel_generators (secondLeviBaseEmbedding e₁ e₂)
    (secondLeviQuotientEvaluation Q β e₁ e₂) u v _ _
    (secondLeviQuotientCartan Q β e₁ e₂ 0 (s + 1))
    (secondLeviQuotientCartan Q β e₁ e₂ 1 (s + 1)) _ _ hR
  · intro P
    simpa only [secondLeviBaseEmbedding, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, if_true, neg_smul, sub_eq_add_neg] using
      secondLeviQuotientEvaluation_cartan Q β e₁ e₂ 0 (s + 1) u hu P
  · intro P
    simpa only [secondLeviBaseEmbedding, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, show (1 : Fin 2) ≠ 0 by decide,
      if_false, one_smul] using
      secondLeviQuotientEvaluation_cartan Q β e₁ e₂ 1 (s + 1) v hv P

/-- Degree induction propagates every saturated relation through all symmetric multipliers. -/
theorem secondLeviQuotientEvaluation_symmetric_mul (e₁ e₂ : ℕ) (u v : ℕ → B)
    (hu : ∀ s, 1 ≤ s → ∀ φ, Q.op 6 s (β φ) = β (u s * φ))
    (hv : ∀ s, 1 ≤ s → ∀ φ, Q.op 7 s (β φ) = β (v s * φ))
    (R P : MvPolynomial (SecondLeviModeSlot e₁ e₂) B)
    (hR : ∀ φ, secondLeviQuotientEvaluation Q β e₁ e₂ (MvPolynomial.C φ * R) = 0)
    (hP : P ∈ secondLeviSymmetricModes e₁ e₂) :
    secondLeviQuotientEvaluation Q β e₁ e₂ (P * R) = 0 := by
  let S := baseSaturatedEvaluationKernel (secondLeviBaseEmbedding e₁ e₂)
    (secondLeviQuotientEvaluation Q β e₁ e₂)
  have hle : secondLeviPowerSumAlgebra e₁ e₂ ≤ multiplicationPreservingSubalgebra S := by
    apply Algebra.adjoin_le
    rintro p ((⟨b, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) x hx
    · exact baseSaturatedEvaluationKernel_base_mul _ _ hx b
    · exact (secondLeviQuotientEvaluation_saturated_generators Q β e₁ e₂ s
        (u (s + 1)) (v (s + 1)) (hu _ (by omega)) (hv _ (by omega)) hx).1
    · exact (secondLeviQuotientEvaluation_saturated_generators Q β e₁ e₂ s
        (u (s + 1)) (v (s + 1)) (hu _ (by omega)) (hv _ (by omega)) hx).2
  have hm := hle (secondLeviSymmetricModes_le_powerSumAlgebra e₁ e₂ hP) R hR
  have hz := hm (1 : B)
  simpa only [map_one, one_mul] using hz

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- The source coefficient algebra is a tensor product of three quotient rings.
/-- Every symmetric multiple of either positive-count relative tail vanishes. -/
theorem radicalSecondLeviEvaluation_relative_mul (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (j : Fin 2) (hm : 0 ≤ a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩)
    (s : ℕ) (hk : 1 ≤ if j = 0 then e₁ else e₂)
    (hs : (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat + 1 ≤
      (if j = 0 then e₁ else e₂) + s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d))
    (hP : P ∈ secondLeviSymmetricModes e₁ e₂) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b c h d
    secondLeviQuotientEvaluation Q β e₁ e₂
      (P * secondLeviRelativeComplete e₁ e₂ j (radicalLeviPowerSum a b c d j) s) = 0 := by
  apply secondLeviQuotientEvaluation_symmetric_mul _ _ e₁ e₂
    (radicalLeviPowerSum a b c d 0) (radicalLeviPowerSum a b c d 1)
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0)
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1) _ P _ hP
  intro φ
  rw [mul_comm]
  fin_cases j
  · exact radicalSecondLeviEvaluation_firstRelativeTail ρ w a b c h d hm e₁ e₂ s hk hs φ
  · exact radicalSecondLeviEvaluation_secondRelativeTail ρ w a b c h d hm e₁ e₂ s hk hs φ

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_saturated_generators
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_symmetric_mul
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_relative_mul

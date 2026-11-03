import VOA.DeligneAudit.SL4TMixedSecondLeviEvaluation

/-! Vanishing of unsupported second Levi counts, from the degree-zero relative relations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
attribute [local instance 2000] Fin.fintype Fin.instOfNat

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- A relative complete function has constant coefficient one for either alphabet. -/
theorem secondLeviRelativeComplete_zero {B : Type} [CommRing B] [Algebra ℂ B]
    (e₁ e₂ : ℕ) (j : Fin 2) (p : ℕ → B) :
    secondLeviRelativeComplete e₁ e₂ j p 0 = 1 := by
  simp [secondLeviRelativeComplete, newtonCoeff]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Exceeding either ambient alphabet length kills every symmetric mode evaluation. -/
theorem radicalSecondLeviEvaluation_zero_of_count_excess (d : Fin 3 → ℕ)
    (e₁ e₂ : ℕ) (j : Fin 2)
    (hm : 0 ≤ a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩)
    (he : (a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩).toNat <
      if j = 0 then e₁ else e₂)
    (P : secondLeviSymmetricModes (B := RadicalGrassmannianRing a b c d) e₁ e₂) :
    secondLeviQuotientEvaluation (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P.val = 0 := by
  have hz := radicalSecondLeviEvaluation_relative_mul ρ w a b c h d e₁ e₂ j hm 0
    (by omega) (by omega) P.val P.property
  simpa only [secondLeviRelativeComplete_zero, mul_one] using hz

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The actual second multiplicity vanishes when either lowering count is unsupported. -/
theorem secondLeviMultiplicity_eq_bot_of_unsupported (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hm : ∀ j, 0 ≤ a3KeyLabelInt b c j ⟨d 0, d 1, d 2, 0⟩)
    (he : (a3KeyLabelInt b c 0 ⟨d 0, d 1, d 2, 0⟩).toNat < e₁ ∨
      (a3KeyLabelInt b c 1 ⟨d 0, d 1, d 2, 0⟩).toNat < e₂) :
    secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  obtain ⟨P, hP⟩ := radicalSecondLeviEvaluation_surjective ρ w a b c h d e₁ e₂ ⟨x, hx⟩
  have hv : secondLeviQuotientEvaluation (radicalCountQuotCurrent ρ w d)
      (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P.val = x :=
    congrArg Subtype.val hP
  rw [← hv]
  rcases he with he | he
  · exact radicalSecondLeviEvaluation_zero_of_count_excess ρ w a b c h d e₁ e₂ 0
      (hm 0) (by simpa using he) P
  · exact radicalSecondLeviEvaluation_zero_of_count_excess ρ w a b c h d e₁ e₂ 1
      (hm 1) (by simpa using he) P

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviRelativeComplete_zero
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_zero_of_count_excess
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_eq_bot_of_unsupported

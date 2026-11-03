import VOA.DeligneAudit.SL4TMixedRelativeEquivariance

/-! The mixed-ring surjection onto the actual second Levi multiplicity space. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
attribute [local instance 2000] Fin.fintype Fin.instOfNat

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Valid mixed tuples have nonnegative first Levi labels. -/
theorem mixedLabelBlockParams_dominant (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) :
    ∀ j, 0 ≤ a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩ := by
  simp only [MixedValid, mixedLabelBlockParams, mixedP, mixedQ] at hv
  intro j
  fin_cases j <;> simp [a3KeyLabelInt] <;> omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b : ℕ) (h : LocalWeylRel ρ w (weightABC a b a))
variable (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
variable (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂))

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The mixed ring evaluates on the actual second multiplicity in the two Levi quotients. -/
def mixedSecondLeviEvaluation :
    MixedRing (mixedLabelBlockParams a b d e₁ e₂) →ₗ[ℂ]
      secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b a h d) e₁ e₂ :=
  (radicalSecondLeviRelativeEvaluation ρ w a b a h d e₁ e₂
    (mixedLabelBlockParams_dominant a b d e₁ e₂ hv)).comp
      (mixedToRadicalRelative a b d e₁ e₂ hv).toLinearMap

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Every second multiplicity vector comes from the mixed ring for its valid tuple. -/
theorem mixedSecondLeviEvaluation_surjective :
    Function.Surjective (mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv) :=
  (radicalSecondLeviRelativeEvaluation_surjective ρ w a b a h d e₁ e₂
    (mixedLabelBlockParams_dominant a b d e₁ e₂ hv)).comp
      (mixedToRadicalRelative_surjective a b d e₁ e₂ hv)

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The last positive Cartan acts through the mixed characteristic power sums. -/
theorem mixedSecondLeviEvaluation_cartan (s : ℕ) (hs : 0 < s)
    (P : MixedRing (mixedLabelBlockParams a b d e₁ e₂)) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
    let π := mixedSecondLeviEvaluation ρ w a b h d e₁ e₂ hv
    secondLeviQuotientCartan Q β e₁ e₂ 1 s (π P).val =
      (π (mixedPowerSum (mixedLabelBlockParams a b d e₁ e₂) s * P)).val := by
  have he := radicalSecondLeviRelativeEvaluation_cartan ρ w a b a h d e₁ e₂
    (mixedLabelBlockParams_dominant a b d e₁ e₂ hv) 1 s hs
    (mixedToRadicalRelative a b d e₁ e₂ hv P)
  simpa only [mixedSecondLeviEvaluation, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, mixedToRadicalRelative_powerSum a b d e₁ e₂ hv s hs] using he

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedLabelBlockParams_dominant
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviEvaluation_cartan

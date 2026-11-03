import VOA.DeligneAudit.SL4TRadicalPowerSumGeneration
import VOA.DeligneAudit.SL4TRadicalCompleteRelations

/-! Vanishing of unsupported merged radical multiplicities at every dominant weight. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

-- Retain the standard finite-index instances under the symmetric-polynomial imports.
attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The constant mode polynomial evaluates to the all-zero radical word. -/
theorem radicalModeEvaluation_one (d : Fin 3 → ℕ) :
    radicalModeEvaluation ρ w d 1 = radicalZeroModeVector ρ w d := by
  have he := radicalModeEvaluation_monomial ρ w d 0 1
  simpa [radicalModeWord, radicalZeroModeVector, aWord,
    List.ofFn_const, List.prod_replicate] using he

/-- Any invariant relation space containing the zero-mode vector contains the multiplicity. -/
theorem radicalMultiplicityEvaluation_eq_zero_of_one (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ)
    (hone : radicalMultiplicityEvaluation ρ w d 1 = 0)
    (P : RadicalModePolynomial d) : radicalMultiplicityEvaluation ρ w d P = 0 := by
  obtain ⟨Q, hQ⟩ := radicalModeEvaluation_symmetric_representative ρ w d P
  have hk := radicalPowerSumAlgebra_preserves_relations ρ w a b c h d Q
    (radicalSymmetricModes_le_powerSumAlgebra d Q.property) 1 hone
  simp only [mul_one] at hk
  have he : radicalMultiplicityEvaluation ρ w d Q =
      radicalMultiplicityEvaluation ρ w d P :=
    Subtype.ext (congrArg (higherRadicalCountClosure ρ w d).mkQ hQ)
  rw [← he]
  exact hk

/-- Every unsupported count multiplicity vanishes, with all mode degrees retained. -/
theorem radicalCountMultiplicity_eq_bot_of_unsupported (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (hd : a < d 0 ∨ b < d 1 ∨ c < d 2) :
    radicalCountMultiplicity ρ w d = ⊥ := by
  have hone : radicalMultiplicityEvaluation ρ w d 1 = 0 := by
    apply Subtype.ext
    change (higherRadicalCountClosure ρ w d).mkQ
      (radicalModeEvaluation ρ w d 1) = 0
    rw [radicalModeEvaluation_one]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (radicalZeroModeVector_mem_higher_of_unsupported ρ w a b c h d hd)
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨P, hP⟩ := radicalMultiplicityEvaluation_surjective ρ w d ⟨v, hv⟩
  have he := radicalMultiplicityEvaluation_eq_zero_of_one ρ w a b c h d hone P
  rw [hP] at he
  exact congrArg Subtype.val he

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalModeEvaluation_one
#print axioms VOA.DeligneAudit.SL4T.radicalMultiplicityEvaluation_eq_zero_of_one
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_eq_bot_of_unsupported

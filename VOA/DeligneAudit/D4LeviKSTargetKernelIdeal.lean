import VOA.DeligneAudit.D4LeviKSTargetKernel
import VOA.DeligneAudit.D4LeviKSSymmetricColour

/-! Symmetric source shifts preserve PAIR target-kernel relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

theorem pairSourcePower_eq_colourPsum (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    pairSourcePower a b c j r =
      colourPsum (pairSourceShape a b c)
        (if j = 0 then 1 else if j = 1 then 4 else 5) r := by
  classical
  fin_cases j
  · simp [pairSourcePower, pairSourceXPsum, colourPsum,
      pairSourceShape, Fintype.sum_sum_type]
  · simp [pairSourcePower, sourceYPsum, colourPsum,
      pairSourceShape, Fintype.sum_sum_type]
  · simp [pairSourcePower, pairSourceZPsum, colourPsum,
      pairSourceShape, Fintype.sum_sum_type]

theorem pairSourceSymmetric_le_xyzPowerSumAlgebra (a b c : ℕ) :
    pairSourceSymmetric a b c ≤
      xyzPowerSumAlgebra (pairSourceShape a b c) := by
  apply Algebra.adjoin_le
  rintro P ⟨⟨j, r⟩, rfl⟩
  change pairSourcePower a b c j r ∈ _
  rw [pairSourcePower_eq_colourPsum, colourPsum_rename_psum]
  apply colourSymmetric_mem_xyzPowerSumAlgebra
  · fin_cases j <;> simp
  · exact psum_isSymmetric _ ℂ r

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairSourceSymmetric_mul_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (P Q : pairSourceSymmetric a b c)
    (hP : xyzEvaluation ρ w (pairSourceShape a b c) P ∈
      keyPrefix ρ w m i) :
    xyzEvaluation ρ w (pairSourceShape a b c) (Q * P :
      pairSourceSymmetric a b c) ∈ keyPrefix ρ w m i := by
  have hQ : (Q : MvPolynomial (PairSource a b c) ℂ) ∈
      xyzPowerSumAlgebra (pairSourceShape a b c) :=
    pairSourceSymmetric_le_xyzPowerSumAlgebra a b c Q.property
  simpa only [Subalgebra.coe_mul, symmetricShiftAction_apply] using
    xyzPowerSumAlgebra_prefix ρ w m i h hi
      (pairSourceShape a b c) (pairSourceShape_xyz a b c)
      Q hQ P hP

/-- The kernel of the PAIR target evaluator is closed under multiplication
    by every separately symmetric target polynomial at a fixed key. -/
theorem pairTargetQuotientEvaluation_mul_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hPair : PairKernelPrefix ρ w m i a b c)
    (T U : pairTargetSymmetric a b c)
    (hT : T ∈ (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker) :
    U * T ∈ (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker := by
  obtain ⟨P, hPT, hP⟩ :=
    (pairTargetQuotientEvaluation_mem_ker_iff ρ w m i a b c hPair T).1 hT
  obtain ⟨Q, hQU⟩ := pairSymmetricRestriction_surjective a b c U
  apply (pairTargetQuotientEvaluation_mem_ker_iff ρ w m i a b c
    hPair (U * T)).2
  refine ⟨Q * P, ?_, pairSourceSymmetric_mul_prefix ρ w m i a b c
    h hi P Q hP⟩
  rw [map_mul, hQU, hPT]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSourcePower_eq_colourPsum
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_le_xyzPowerSumAlgebra
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_mul_prefix
#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_mul_mem_ker

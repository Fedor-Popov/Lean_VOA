/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningMoment

/-!
# A nonzero individual coefficient for the finite screening construction

The residue functional is linear. Expanding the homogeneous Newton witness
therefore yields a single positive-power-sum monomial with nonzero residue.
Its weighted degree is exactly rs, as required by the proposed Fock state.
This proves a nonzero coefficient uniformly, without a product formula;
the actual Fock Ward identities are not part of this result.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators

/-- The exact finite screening residue, viewed as a rational linear map.
This permits expansion into ordinary monomial coefficients. -/
noncomputable def screeningMomentLinear (r s t : ℕ) :
    MvPolynomial (Fin r) ℚ →ₗ[ℚ] ℚ where
  toFun := screeningMoment r s t
  map_add' P Q := by
    simp only [screeningMoment,map_add,mul_add]
    rfl
  map_smul' a P := by
    simp only [screeningMoment,map_smul,mul_smul_comm,AddMonoidAlgebra.smul_apply]
    rfl

/-- Some single monomial in positive power sums of total weight rs has
nonzero residue for every integer screening parameter. The test is an
actual computed coefficient functional, not a hypothesized pairing. -/
theorem screening_nonzero_monomial (r s t : ℕ) :
    ∃ d : ℕ →₀ ℕ, Finsupp.weight (fun i => i+1) d = r*s ∧
      screeningMoment r s t (powerSumSubstitution (Fin r)
        (MvPolynomial.monomial d 1)) ≠ 0 := by
  classical
  obtain ⟨P,hP,hne⟩ := screeningMoment_powerSum_witness r s t
  let L := (screeningMomentLinear r s t).comp (powerSumSubstitution (Fin r)).toLinearMap
  by_contra hz
  push_neg at hz
  apply hne
  change L P = 0
  rw [MvPolynomial.as_sum P,map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hw : Finsupp.weight (fun i => i+1) d = r*s :=
    hP (MvPolynomial.mem_support_iff.mp hd)
  have he : L (MvPolynomial.monomial d 1) = 0 := hz d hw
  have hm : MvPolynomial.monomial d (MvPolynomial.coeff d P) =
      MvPolynomial.coeff d P • (MvPolynomial.monomial d 1 : MvPolynomial ℕ ℚ) := by
    simp [MvPolynomial.smul_monomial,smul_eq_mul]
  rw [hm,map_smul,he,smul_zero]

end VOA.VirasoroScreening

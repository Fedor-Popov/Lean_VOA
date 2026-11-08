import VOA.Moonshine.MoonshineCNHyperbolicMixedModes

/-! # Exact finite central-scalar evaluation

The finite contraction sum is evaluated by induction, without certificates.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypSugawara_central_triangular_sum (j : ℕ) :
    (∑ k ∈ Finset.range j, (k + 1 : ℂ)) = (j : ℂ) * (j + 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem hypSugawara_central_sum (j : ℕ) :
    (∑ k ∈ Finset.range j, (k + 1 : ℂ) * (j - k : ℂ)) =
      (j : ℂ) * (j + 1) * (j + 2) / 6 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ k ∈ Finset.range j, (k + 1 : ℂ) * ((j + 1 : ℕ) - k : ℂ)) =
        (∑ k ∈ Finset.range j, (k + 1 : ℂ) * (j - k : ℂ)) +
        ∑ k ∈ Finset.range j, (k + 1 : ℂ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [he, ih, hypSugawara_central_triangular_sum]
    push_cast
    ring

theorem hypLoweringDerivation_potential_constant (κ ell : ℂ) (i j : ℕ) :
    constantCoeff (hypLoweringDerivation κ ell (i + 1) (hypNegativePotential κ ell j)) =
      if i = j then 2 * (i + 1 : ℂ) * κ * ell else 0 := by
  have hx (a : Fin 2) :
      constantCoeff (hypLoweringDerivation κ ell (i + 1) (X (j, a))) =
        if j + 1 = i + 1 then (j + 1 : ℂ) * (if a = 0 then κ else ell) else 0 := by
    rw [hypLoweringDerivation_X]
    split_ifs <;> simp_all
  have hq (s t : ℕ) : constantCoeff (hypLoweringDerivation κ ell (i + 1)
      (X (s, 0) * X (t, 1))) = 0 := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, constantCoeff_X, zero_mul, add_zero]
  simp only [hypNegativePotential, map_add, Derivation.map_smul, map_sum,
    constantCoeff_smul, hx, hq, Finset.sum_const_zero, add_zero, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp
    ring
  · simp [h, Ne.symm h]

theorem hypPositiveSecondOrder_negativePotential (κ ell : ℂ) (i j : ℕ) :
    hypPositiveSecondOrder i (hypNegativePotential κ ell j) =
      if i = j then ((i : ℂ) * (i + 1) * (i + 2) / 6) • (1 : hypFock) else 0 := by
  have ht (k : ℕ) (hk : k ∈ Finset.range i) :
      pderiv (k, 0) (pderiv (i - 1 - k, 1) (hypNegativePotential κ ell j)) =
        if i = j then (1 : hypFock) else 0 := by
    have hk' := Finset.mem_range.mp hk
    rw [hypNegativePotential_pderiv_b]
    simp only [map_add, apply_ite, pderiv_C, map_zero, pderiv_X, Pi.single_apply,
      Prod.mk.injEq, and_true, ite_self, zero_add]
    by_cases h : i = j
    · subst j
      simp [show i - 1 - k < i by omega, show i - 1 - (i - 1 - k) = k by omega]
    · by_cases hlt : i - 1 - k < j
      · simp [h, hlt, show j - 1 - (i - 1 - k) ≠ k by omega]
      · simp [h, hlt]
  simp only [hypPositiveSecondOrder, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Derivation.coeFn_coe]
  rw [Finset.sum_congr rfl (fun (k : ℕ) hk => congrArg (fun p : hypFock =>
    ((k + 1 : ℂ) * (i - k : ℂ)) • p) (ht k hk))]
  by_cases h : i = j
  · simp only [h, if_true, ← Finset.sum_smul, hypSugawara_central_sum]
  · simp [h]

/-- The vacuum matrix coefficient determining the central extension. -/
theorem hypSugawara_positive_negative_constant (κ ell : ℂ) (i j : ℕ) :
    constantCoeff (hypSugawara κ ell (i + 1 : ℤ)
      (hypSugawara κ ell (-(j + 1 : ℤ)) 1)) =
      if i = j then 2 * (i + 1 : ℂ) * κ * ell +
        (i : ℂ) * (i + 1) * (i + 2) / 6 else 0 := by
  rw [hypSugawara_negative_vacuum, hypSugawara_positive, map_add,
    hypLoweringDerivation_potential_constant, hypPositiveSecondOrder_negativePotential]
  by_cases h : i = j <;> simp [h]

end VOA.Moonshine.ConwayNorton

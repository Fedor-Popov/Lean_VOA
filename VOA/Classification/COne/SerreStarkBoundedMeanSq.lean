/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkBoundedFarey

/-!
# Serre–Stark S5-2c: the mean-square bound ("Ramanujan on average")

`sum_sq_coeff_le`: for a θ-type form `f = Σ a(n) qⁿ` of level `N` (`4 ∣ N`) there is `C` with

`Σ_{n < M} |a(n)|² e^{−4πny} ≤ C y^{−1/2}`  for all `M` and `0 < y ≤ 1/4`

(no logarithm). Proof: Parseval on `[0, 1]` (Mathlib `tsum_sq_fourierCoeffOn`; the Fourier
coefficients of `x ↦ f(x+iy)` are `a(n) e^{−2πny}` by `qExpansion_coeff_eq_intervalIntegral`), and
`∫₀¹ |f(x+iy)|² dx = y^{−1/2} ∫₀¹ nf f (x+iy) dx ≤ y^{−1/2} K √y ∫₀¹ fareySum y` with the
Farey-arc estimates of `SerreStarkBoundedFarey.lean`.

Corollary `norm_coeff_sq_le`: `|a(n)|² ≤ C' n^{1/2}`.
-/

open Complex MeasureTheory Set
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## The horizontal-line integral of `nf` -/

theorem continuous_horizontal {N : ℕ} {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I) := by
  have hc : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I :=
    Complex.continuous_ofReal.add continuous_const
  exact hf.holo.continuousOn.comp_continuous hc fun x => by simp [hy]

theorem continuous_nf_horizontal {N : ℕ} {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ => nf f ((x : ℂ) + (y : ℂ) * I) := by
  unfold nf
  have : (fun x : ℝ => ‖f ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 *
      Real.sqrt ((x : ℂ) + (y : ℂ) * I).im) =
      fun x : ℝ => ‖f ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 * Real.sqrt y := by
    funext x; simp
  rw [this]
  exact ((continuous_horizontal hf hy).norm.pow 2).mul continuous_const

/-- `∫₀¹ nf f (x + iy) dx ≤ 4 (2 + log 4) K` for `0 < y ≤ 1/4`. -/
theorem integral_nf_le {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 4 →
      ∫ x in (0 : ℝ)..1, nf f ((x : ℂ) + (y : ℂ) * I) ≤ 4 * (2 + Real.log 4) * K := by
  obtain ⟨K, hK0, hK⟩ := exists_nf_bound h4 hN hf
  refine ⟨K, hK0, fun y hy0 hy => ?_⟩
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hfi : IntervalIntegrable (fun x : ℝ => fareySum y x) volume 0 1 := by
    unfold fareySum
    exact (integrable_finsetSum _ fun c hc => integrable_finsetSum _ fun a _ =>
      integrable_fareyPiece _ hy0 (Finset.mem_Icc.1 hc).1 a).intervalIntegrable
  calc ∫ x in (0 : ℝ)..1, nf f ((x : ℂ) + (y : ℂ) * I)
      ≤ ∫ x in (0 : ℝ)..1, K * Real.sqrt y * fareySum y x := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((continuous_nf_horizontal hf hy0).intervalIntegrable _ _)
          (hfi.const_mul _) fun x hx => nf_le_fareySum hK0 hK hx hy0 hy
    _ = K * Real.sqrt y * ∫ x in (0 : ℝ)..1, fareySum y x :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ K * Real.sqrt y * (4 * (2 + Real.log 4) * (Real.sqrt y)⁻¹) :=
        mul_le_mul_of_nonneg_left (integral_fareySum_le hy0 hy) (by positivity)
    _ = 4 * (2 + Real.log 4) * K := by field_simp

/-! ## Fourier coefficients on a horizontal line -/

theorem fourierCoeffOn_horizontal {N : ℕ} {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) {y : ℝ}
    (hy : 0 < y) (n : ℕ) :
    fourierCoeffOn zero_lt_one (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) n =
      thetaTypeCoeff f n * Real.exp (-(2 * Real.pi * n * y)) := by
  rw [fourierCoeffOn_eq_integral _ _ zero_lt_one]
  unfold thetaTypeCoeff
  rw [UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral one_pos hf.periodic hf.mdiff hf.bdd n hy]
  simp only [sub_zero, one_mul, one_smul, Complex.ofReal_one, div_one]
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [fourier_coe_apply, smul_eq_mul, Function.Periodic.qParam, UpperHalfPlane.coe_I,
    Complex.ofReal_one, div_one]
  have e : ∀ z : ℂ, 1 / cexp z ^ n = cexp (-(n * z)) := by
    intro z; rw [← Complex.exp_nat_mul, one_div, ← Complex.exp_neg]
  rw [e, show ((Real.exp (-(2 * Real.pi * n * y)) : ℝ) : ℂ) =
    cexp (((-(2 * Real.pi * n * y)) : ℝ) : ℂ) from Complex.ofReal_exp _]
  rw [mul_right_comm (cexp _) (f _) (cexp _), ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## The mean-square bound -/

/-- **Mean square ("Ramanujan on average").** -/
theorem sum_sq_coeff_le {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 4 → ∀ M : ℕ,
      ∑ n ∈ Finset.range M, ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n * y)) ≤
        C * (Real.sqrt y)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := integral_nf_le h4 hN hf
  refine ⟨4 * (2 + Real.log 4) * K, by positivity, fun y hy0 hy M => ?_⟩
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  set F : ℝ → ℂ := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I) with hF
  have hFc : Continuous F := continuous_horizontal hf hy0
  -- `F ∈ L²(0,1]`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hFc.continuousOn
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine MemLp.of_bound hFc.aestronglyMeasurable B ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hB x (Ioc_subset_Icc_self hx)
  have hP := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  simp only [sub_zero, inv_one, one_smul] at hP
  -- partial sums of the `n ≥ 0` coefficients
  have hterm : ∀ n : ℕ, ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n * y)) =
      ‖fourierCoeffOn zero_lt_one F n‖ ^ 2 := by
    intro n
    rw [hF, fourierCoeffOn_horizontal hf hy0 n, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  have hsum : ∑ n ∈ Finset.range M, ‖thetaTypeCoeff f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n * y))
      ≤ ∫ x in (0 : ℝ)..1, ‖F x‖ ^ 2 := by
    simp_rw [hterm]
    have hmap : ∑ n ∈ Finset.range M, ‖fourierCoeffOn zero_lt_one F (n : ℤ)‖ ^ 2 =
        ∑ i ∈ (Finset.range M).map Nat.castEmbedding, ‖fourierCoeffOn zero_lt_one F i‖ ^ 2 := by
      rw [Finset.sum_map]; rfl
    rw [hmap, ← hP.tsum_eq]
    exact hP.summable.sum_le_tsum _ fun i _ => sq_nonneg _
  -- the integral of `‖F‖²`
  have hint : ∫ x in (0 : ℝ)..1, ‖F x‖ ^ 2 =
      (Real.sqrt y)⁻¹ * ∫ x in (0 : ℝ)..1, nf f ((x : ℂ) + (y : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [nf, hF]
    have : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [this]
    field_simp
  calc _ ≤ ∫ x in (0 : ℝ)..1, ‖F x‖ ^ 2 := hsum
    _ = (Real.sqrt y)⁻¹ * ∫ x in (0 : ℝ)..1, nf f ((x : ℂ) + (y : ℂ) * I) := hint
    _ ≤ (Real.sqrt y)⁻¹ * (4 * (2 + Real.log 4) * K) :=
        mul_le_mul_of_nonneg_left (hK y hy0 hy) (by positivity)
    _ = 4 * (2 + Real.log 4) * K * (Real.sqrt y)⁻¹ := by ring

end SSHecke

end VOA.Classification.COne

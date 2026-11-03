/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkUpClass

/-!
# Serre–Stark S5-2a: the invariant `‖f‖² (Im τ)^{1/2}` and its uniform cusp bound

For a θ-type form `f` of level `N` (`4 ∣ N`) the function `nf f τ = ‖f τ‖² √(Im τ)` is
`Γ₁(N)`-invariant (`nf_mobius`), and there is one constant `K` with

`nf f (g w) ≤ K √(Im w)` for every `g ∈ SL₂(ℤ)` and `Im w ≥ 1/5`

(`exists_nf_bound`; finitely many cosets of `Γ₁(N)`, one cusp bound each). This is the input of
the Farey-arc mean-square estimate (`SerreStarkBoundedMeanSq.lean`).
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-- The `Γ₁(N)`-invariant `‖f τ‖² (Im τ)^{1/2}` of a weight-`½` θ-type form. -/
def nf (f : ℂ → ℂ) (τ : ℂ) : ℝ := ‖f τ‖ ^ 2 * Real.sqrt τ.im

theorem nf_nonneg (f : ℂ → ℂ) (τ : ℂ) : 0 ≤ nf f τ :=
  mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

theorem im_mobius_eq (γ : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    (mobius γ τ).im = τ.im / ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ 2 := by
  rw [show τ = ((⟨τ, hτ⟩ : ℍ) : ℂ) from rfl, mobius_eq_smul]
  rw [UpperHalfPlane.coe_im, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
    Complex.normSq_eq_norm_sq]
  rfl

theorem denom_ne_zero' (γ : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ≠ 0 := by
  rw [norm_ne_zero_iff]; exact denom_ne_zero γ hτ

theorem norm_mobius_of_mem_Gamma1 {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖f (mobius γ τ)‖ = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) * ‖f τ‖ := by
  have hc : 4 ∣ γ 1 0 := by
    have := ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ).2.2
    have hN : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    exact (Int.natCast_dvd_natCast.2 h4).trans hN
  have hθ := thetaRef_ne_zero_of_im_pos hτ
  have h1 := congrArg norm (hf.multiplier γ hγ τ hτ)
  rw [norm_mul, norm_mul, norm_thetaRef_mobius hc hτ] at h1
  have hθn : ‖thetaRef τ‖ ≠ 0 := norm_ne_zero_iff.2 hθ
  apply mul_right_cancel₀ hθn
  linear_combination h1

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

/-- **Invariance**: `nf f (γτ) = nf f τ` for `γ ∈ Γ₁(N)`. -/
theorem nf_mobius {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ} (hτ : 0 < τ.im) :
    nf f (mobius γ τ) = nf f τ := by
  unfold nf
  rw [norm_mobius_of_mem_Gamma1 h4 hf hγ hτ, im_mobius_eq γ hτ, mul_pow,
    rpow_half_sq (norm_nonneg _)]
  have hD := denom_ne_zero' γ hτ
  have hDp : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hDp.le]
  field_simp

/-- The bound at one cusp, in terms of `nf`. -/
theorem nf_cusp_bound {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (δ : SL(2, ℤ)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 1 / 5 ≤ w.im →
      nf f (mobius δ w) ≤ K * Real.sqrt w.im := by
  obtain ⟨C, hC⟩ := IsThetaTypeForm.cusp_bound_of_le h4 hN hf δ (by norm_num : (0 : ℝ) < 1 / 5)
  refine ⟨C ^ 2, sq_nonneg _, fun w hw => ?_⟩
  have hw0 : 0 < w.im := lt_of_lt_of_le (by norm_num) hw
  have hb := hC w hw
  have hD := denom_ne_zero' δ hw0
  have hDp : 0 < ‖(δ 1 0 : ℂ) * w + δ 1 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
  set D := ‖(δ 1 0 : ℂ) * w + δ 1 1‖
  have hsq : ‖f (mobius δ w)‖ ^ 2 ≤ C ^ 2 * D := by
    have h1 : ‖f (mobius δ w)‖ ^ 2 ≤ (C * D ^ (1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    rwa [mul_pow, rpow_half_sq hDp.le] at h1
  unfold nf
  rw [im_mobius_eq δ hw0, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hDp.le]
  calc ‖f (mobius δ w)‖ ^ 2 * (Real.sqrt w.im / D) ≤ C ^ 2 * D * (Real.sqrt w.im / D) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = C ^ 2 * Real.sqrt w.im := by field_simp

/-- **Uniform cusp bound**: one `K` for all `g ∈ SL₂(ℤ)` and `Im w ≥ 1/5`. -/
theorem exists_nf_bound {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : ∃ K : ℝ, 0 ≤ K ∧ ∀ g : SL(2, ℤ), ∀ w : ℂ, 1 / 5 ≤ w.im →
      nf f (mobius g w) ≤ K * Real.sqrt w.im := by
  haveI : NeZero N := ⟨hN.ne'⟩
  set H := CongruenceSubgroup.Gamma1 N
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  choose K hK0 hK using fun q : SL(2, ℤ) ⧸ H => nf_cusp_bound h4 hN hf (q.out)⁻¹
  refine ⟨∑ q, K q, Finset.sum_nonneg fun q _ => hK0 q, fun g w hw => ?_⟩
  have hw0 : 0 < w.im := lt_of_lt_of_le (by norm_num) hw
  set q : SL(2, ℤ) ⧸ H := QuotientGroup.mk g⁻¹
  have hmem : g * q.out ∈ H := by
    have : (QuotientGroup.mk (q.out) : SL(2, ℤ) ⧸ H) = QuotientGroup.mk g⁻¹ := q.out_eq
    have := H.inv_mem (QuotientGroup.eq.1 this)
    simpa using this
  have hg : g = (g * q.out) * (q.out)⁻¹ := by group
  have hδw := im_mobius_pos (q.out)⁻¹ hw0
  rw [hg, mobius_mul _ _ hw0, nf_mobius h4 hf hmem hδw]
  refine (hK q w hw).trans ?_
  have hle : K q ≤ ∑ q, K q :=
    Finset.single_le_sum (fun q _ => hK0 q) (Finset.mem_univ q)
  exact mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)

end SSHecke

end VOA.Classification.COne

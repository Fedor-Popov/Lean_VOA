/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeOp

/-!
# Serre–Stark S3-1f: cusp bounds below `Im τ = 1`, and the column reduction

* `IsThetaTypeForm.cusp_bound_of_le`: the cusp condition `‖f(δw)‖ ≤ C ‖cw + d‖^{1/2}`, given
  on `Im w ≥ 1`, extends to `Im w ≥ ε` for any `ε > 0` (the quotient is `N`-periodic, by the
  `θ`-multiplier law on `Γ(N)`, and bounded on a compact fundamental strip);
* `exists_SL_mul_upper`: every integer matrix of positive determinant is `δ U` with
  `δ ∈ SL₂(ℤ)` and `U` upper triangular with positive diagonal.
-/

open Complex Filter Topology
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Column reduction -/

/-- Every integer matrix `X` with `det X > 0` is `δ U`, `δ ∈ SL₂(ℤ)`, `U` upper triangular with
positive diagonal. -/
theorem exists_SL_mul_upper (X : Matrix (Fin 2) (Fin 2) ℤ) (hX : 0 < X.det) :
    ∃ (δ : SL(2, ℤ)) (U : Matrix (Fin 2) (Fin 2) ℤ), X = (δ : Matrix (Fin 2) (Fin 2) ℤ) * U ∧
      U 1 0 = 0 ∧ 0 < U 0 0 ∧ 0 < U 1 1 ∧ U 0 0 * U 1 1 = X.det := by
  set x := X 0 0 with hx
  set y := X 1 0 with hy
  have hdet := hX
  rw [Matrix.det_fin_two] at hdet
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    rw [← hx, ← hy, h.1, h.2] at hdet
    simp at hdet
  set g : ℤ := (Int.gcd x y : ℤ) with hg
  have hg0 : 0 < g := by rw [hg]; exact_mod_cast Int.gcd_pos_iff.2 hxy
  obtain ⟨x', hx'⟩ : g ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : g ∣ y := Int.gcd_dvd_right x y
  set A := Int.gcdA x y
  set B := Int.gcdB x y
  have hbez : g = x * A + y * B := Int.gcd_eq_gcd_ab x y
  have hdet1 : x' * A + y' * B = 1 := by
    have : g * (x' * A + y' * B) = g * 1 := by rw [mul_one]; nth_rw 2 [hbez]; rw [hx', hy']; ring
    exact mul_left_cancel₀ hg0.ne' this
  set δ : SL(2, ℤ) := ⟨!![x', -B; y', A], by simp [Matrix.det_fin_two]; linarith⟩ with hδ
  set V : Matrix (Fin 2) (Fin 2) ℤ := !![A, B; -y', x'] with hV
  have hδV : (δ : Matrix (Fin 2) (Fin 2) ℤ) * V = 1 := by
    rw [hδ, hV]
    simp only [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  set U := V * X with hU
  have hU10 : U 1 0 = 0 := by
    simp only [hU, hV, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← hx, ← hy, hx', hy']; ring
  have hU00 : U 0 0 = g := by
    simp only [hU, hV, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← hx, ← hy, hbez]; ring
  have hdetU : U 0 0 * U 1 1 = X.det := by
    have h1 : U.det = X.det := by
      rw [hU, Matrix.det_mul, hV, Matrix.det_fin_two_of]
      rw [show A * x' - B * -y' = 1 by linarith, one_mul]
    rw [← h1, Matrix.det_fin_two, hU10, mul_zero, sub_zero]
  refine ⟨δ, U, ?_, hU10, by rw [hU00]; exact hg0, ?_, hdetU⟩
  · rw [hU, ← Matrix.mul_assoc, hδV, Matrix.one_mul]
  · rw [hU00] at hdetU
    by_contra h
    push Not at h
    have : g * U 1 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0.le h
    linarith


/-! ## Extending the cusp bound below `Im = 1` -/

theorem matT_zpow_mem_Gamma (N : ℕ) : matT ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem, coe_matT_zpow]
  simp

theorem mem_Gamma1_of_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma N) :
    γ ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨h.1, h.2.2.2, h.2.2.1⟩

/-- The normalised size `‖f(δw)‖ / ‖cw + d‖^{1/2}`. -/
def cuspRatio (f : ℂ → ℂ) (δ : SL(2, ℤ)) (w : ℂ) : ℝ :=
  ‖f (mobius δ w)‖ / ‖(δ 1 0 : ℂ) * w + δ 1 1‖ ^ (1 / 2 : ℝ)

theorem cuspRatio_add {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (δ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    cuspRatio f δ (w + N) = cuspRatio f δ w := by
  set γ' := δ * matT ^ (N : ℤ) * δ⁻¹ with hγ'
  have hn : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N
  have hΓ : γ' ∈ CongruenceSubgroup.Gamma N := hn.conj_mem _ (matT_zpow_mem_Gamma N) δ
  have hΓ1 := mem_Gamma1_of_mem_Gamma hΓ
  have h4c : 4 ∣ γ' 1 0 := by
    have := (CongruenceSubgroup.Gamma_mem.1 hΓ).2.2.1
    have hN : (N : ℤ) ∣ γ' 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    exact (Int.natCast_dvd_natCast.2 h4).trans hN
  have hz := im_mobius_pos δ hw
  have hmob : mobius δ (w + N) = mobius γ' (mobius δ w) := by
    rw [← mobius_mul _ _ hw, hγ', inv_mul_cancel_right, mobius_mul _ _ hw, matT_eq,
      mobius_T_zpow]
    push_cast; ring_nf
  have hθz := thetaRef_ne_zero_of_im_pos hz
  have hmul := hf.multiplier γ' hΓ1 _ hz
  have hnorm : ‖f (mobius γ' (mobius δ w))‖ =
      ‖(γ' 1 0 : ℂ) * mobius δ w + γ' 1 1‖ ^ (1 / 2 : ℝ) * ‖f (mobius δ w)‖ := by
    have := congrArg norm hmul
    rw [norm_mul, norm_mul, norm_thetaRef_mobius h4c hz] at this
    have hθn : ‖thetaRef (mobius δ w)‖ ≠ 0 := norm_ne_zero_iff.2 hθz
    apply mul_right_cancel₀ hθn
    linear_combination this
  have hden : ((δ 1 0 : ℂ) * (w + N) + δ 1 1) =
      ((γ' 1 0 : ℂ) * mobius δ w + γ' 1 1) * ((δ 1 0 : ℂ) * w + δ 1 1) := by
    rw [← denom_mul γ' δ hw]
    have hγδ : γ' * δ = δ * matT ^ (N : ℤ) := by rw [hγ', inv_mul_cancel_right]
    rw [hγδ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_matT_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp
    ring
  unfold cuspRatio
  rw [hmob, hnorm, hden, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hpos : 0 < ‖(γ' 1 0 : ℂ) * mobius δ w + γ' 1 1‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 (denom_ne_zero γ' hz)) _
  rw [mul_div_mul_left _ _ hpos.ne']

theorem cuspRatio_add_int {N : ℕ} (h4 : 4 ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (δ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) (k : ℤ) :
    cuspRatio f δ (w + k * N) = cuspRatio f δ w := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hw' : 0 < (w + ((k : ℤ) : ℂ) * N).im := by simp [hw]
    have e : w + (((k : ℤ) + 1 : ℤ) : ℂ) * N = (w + ((k : ℤ) : ℂ) * N) + N := by push_cast; ring
    rw [e, cuspRatio_add h4 hf δ hw', ih]
  | pred k ih =>
    have hw' : 0 < (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * N).im := by simp [hw]
    have e : w + ((-(k : ℤ) : ℤ) : ℂ) * N = (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * N) + N := by
      push_cast; ring
    rw [← ih, e, cuspRatio_add h4 hf δ hw']

/-- **The cusp bound on `Im w ≥ ε`.** -/
theorem IsThetaTypeForm.cusp_bound_of_le {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) (δ : SL(2, ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ w : ℂ, ε ≤ w.im →
      ‖f (mobius δ w)‖ ≤ C * ‖(δ 1 0 : ℂ) * w + δ 1 1‖ ^ (1 / 2 : ℝ) := by
  set K : Set ℂ := Set.Icc (0 : ℝ) N ×ℂ Set.Icc ε 1 with hK
  have hKc : IsCompact K := (isCompact_Icc).reProdIm isCompact_Icc
  have hKH : K ⊆ upperSet := fun w hw => by
    have := hw.2.1; show 0 < w.im; linarith
  have hcont : ContinuousOn (cuspRatio f δ) K := by
    have h1 : ContinuousOn (fun w => ‖f (mobius δ w)‖) K :=
      ((differentiableOn_comp_mobius hf.holo δ).continuousOn.mono hKH).norm
    have h2 : ContinuousOn (fun w : ℂ => ‖(δ 1 0 : ℂ) * w + δ 1 1‖ ^ (1 / 2 : ℝ)) K := by
      refine ContinuousOn.rpow_const ?_ (fun _ _ => Or.inr (by norm_num))
      exact (((continuous_const.mul continuous_id).add continuous_const).norm).continuousOn
    refine h1.div h2 fun w hw => ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 (denom_ne_zero δ (hKH hw))) _).ne'
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hcont
  obtain ⟨C₂, hC₂⟩ := hf.cusps δ
  refine ⟨max C₁ C₂, fun w hw => ?_⟩
  have hwpos : 0 < w.im := lt_of_lt_of_le hε hw
  have hD : 0 < ‖(δ 1 0 : ℂ) * w + δ 1 1‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 (denom_ne_zero δ hwpos)) _
  by_cases h1 : 1 ≤ w.im
  · exact (hC₂ w h1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hD.le)
  · push Not at h1
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    set k : ℤ := ⌊w.re / N⌋ with hk
    set w' : ℂ := w + ((-k : ℤ) : ℂ) * N with hw'
    have hw'K : w' ∈ K := by
      have hre : w'.re = w.re - k * N := by rw [hw']; simp; ring
      have him : w'.im = w.im := by rw [hw']; simp
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [hre]
        have := Int.floor_le (w.re / N)
        rw [← hk] at this
        have := (le_div_iff₀ hNr).1 this
        linarith
      · rw [hre]
        have := Int.lt_floor_add_one (w.re / N)
        rw [← hk] at this
        have := (div_lt_iff₀ hNr).1 this
        nlinarith
      · rw [him]; exact hw
      · rw [him]; exact h1.le
    have hr := cuspRatio_add_int h4 hf δ hwpos (-k)
    have hb := hC₁ w' hw'K
    rw [hw', hr, Real.norm_eq_abs] at hb
    have hb' : cuspRatio f δ w ≤ max C₁ C₂ := (le_abs_self _).trans (hb.trans (le_max_left _ _))
    unfold cuspRatio at hb'
    rwa [div_le_iff₀ hD] at hb'

end SSHecke

end VOA.Classification.COne

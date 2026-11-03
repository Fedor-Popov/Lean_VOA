/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.HKLRationalAssocSeries

/-! # O3: the associator relation at a complex point

`VOA.Huang.HKLRational.assoc_series_eq` proves, for coefficient sequences `P, Q : ℤ → ℂ`
related by the associator form of the Jacobi identity, that the iterate series
`Σ_r Q_r s^{-r-1}` and the product series `Σ_k P_k (1+s)^{k-D-1}` agree at real `s ∈ (0,1)`.

The logarithmic tensor category tests maps on completed iterates at the complex points
`s = e^t`, `t ∈ overlapDomain`. This file proves the same identity at every complex `s₀ ≠ 0`
with `‖1 + s₀‖ > 1` at which the iterate series converges (`assoc_series_eq_complex`). The proof
is that of `assoc_series_eq`; only Step 2 (now at a complex point) and Step 5 (evaluation of
the identity theorem at the complex point `1/(1+s₀)` of the unit disc) change. Real summability
of the product series is still used, for holomorphy on the disc.

Pure analysis; no `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HKLRational

open VOA Complex Filter Topology

/-- **Equality of the iterate and product expansions at a complex point.** -/
theorem assoc_series_eq_complex (P Q : ℤ → ℂ) (D : ℤ) (K : ℕ) (k1 r0 : ℤ)
    (hP : ∀ k, k1 ≤ k → P k = 0) (hQ : ∀ r, r0 ≤ r → Q r = 0)
    (hrel : ∀ ℓ : ℤ, ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * Q (ℓ + i) =
      ∑' i : ℕ, cbz (i - ℓ - 1) i * P (D - K - ℓ + i))
    (hProd : ∀ s : ℝ, 0 < s → s < 1 →
      Summable fun k : ℤ => P k * (1 + (s : ℂ)) ^ (k - D - 1))
    {s₀ : ℂ} (hs0 : s₀ ≠ 0) (hs1 : 1 < ‖1 + s₀‖)
    (hIt₀ : Summable fun r : ℤ => Q r * s₀ ^ (-r - 1)) :
    ∑' r : ℤ, Q r * s₀ ^ (-r - 1) = ∑' k : ℤ, P k * (1 + s₀) ^ (k - D - 1) := by
  classical
  let c : ℤ → ℂ := fun ℓ => ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * Q (ℓ + i)
  let S : Finset ℤ := Finset.Ioo (D - K - k1) r0
  have hcS : ∀ ℓ, ℓ ∉ S → c ℓ = 0 := by
    intro ℓ hℓ
    simp only [S, Finset.mem_Ioo, not_and_or, not_lt] at hℓ
    rcases hℓ with h | h
    · simp only [c]
      rw [hrel ℓ]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [hP _ (by omega), mul_zero]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [hQ _ (by omega), mul_zero]
  let E : ℂ → ℂ := fun z => ∑ ℓ ∈ S, c ℓ * z ^ (-ℓ - 1)
  have hE : ∀ z : ℂ, ∑' ℓ : ℤ, c ℓ * z ^ (-ℓ - 1) = E z := fun z =>
    tsum_eq_sum fun ℓ hℓ => by rw [hcS ℓ hℓ, zero_mul]
  -- Step 2: the iterate side on `(0, 1)`
  have hstep2 : ∀ x : ℂ, x ≠ 0 → (Summable fun r : ℤ => Q r * x ^ (-r - 1)) →
      (1 + x) ^ K * ∑' r : ℤ, Q r * x ^ (-r - 1) = E x := by
    intro x hx0 hsum
    have hshift : ∀ i : ℕ, Summable fun ℓ : ℤ => (K.choose i : ℂ) * Q (ℓ + i) * x ^ (-ℓ - 1) := by
      intro i
      have h := (hsum.comp_injective (Equiv.addRight (i : ℤ)).injective).mul_left
        ((K.choose i : ℂ) * x ^ (i : ℤ))
      refine h.congr fun ℓ => ?_
      simp only [Function.comp, Equiv.coe_addRight]
      rw [show -(ℓ + (i : ℤ)) - 1 = -ℓ - 1 - i by ring, zpow_sub₀ hx0, zpow_natCast]
      field_simp
    have hpow : (1 + x) ^ K = ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * x ^ (i : ℤ) := by
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, zpow_natCast, mul_comm]
    rw [hpow, Finset.sum_mul, ← hE]
    have hterm : ∀ i ∈ Finset.range (K + 1),
        (K.choose i : ℂ) * x ^ (i : ℤ) * ∑' r : ℤ, Q r * x ^ (-r - 1) =
          ∑' ℓ : ℤ, (K.choose i : ℂ) * Q (ℓ + i) * x ^ (-ℓ - 1) := by
      intro i _
      rw [← tsum_mul_left, ← (Equiv.addRight (i : ℤ)).tsum_eq]
      refine tsum_congr fun ℓ => ?_
      simp only [Equiv.coe_addRight]
      rw [show -(ℓ + (i : ℤ)) - 1 = -ℓ - 1 - i by ring, zpow_sub₀ hx0, zpow_natCast]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum fun i _ => hshift i]
    refine tsum_congr fun ℓ => ?_
    simp only [c, Finset.sum_mul]
  -- Step 3: the product side for `s ≥ 3`
  have hP32 : Summable fun k : ℤ => P k * (((3 / 2 : ℝ)) : ℂ) ^ (k - D - 1) := by
    have h := hProd (1 / 2) (by norm_num) (by norm_num)
    convert h using 3
    push_cast
    norm_num
  have hstep3 : ∀ s : ℝ, 3 ≤ s →
      (1 + (s : ℂ)) ^ K * ∑' k : ℤ, P k * (1 + (s : ℂ)) ^ (k - D - 1) = E s := by
    intro s hs
    have hs1 : (1 + (s : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]; linarith
    rw [← tsum_mul_left]
    have e1 : ∀ k : ℤ, (1 + (s : ℂ)) ^ K * (P k * (1 + (s : ℂ)) ^ (k - D - 1)) =
        P k * (1 + (s : ℂ)) ^ (k + K - D - 1) := by
      intro k
      rw [show k + (K : ℤ) - D - 1 = (k - D - 1) + K by ring, zpow_add₀ hs1, zpow_natCast]
      ring
    rw [tsum_congr e1, prod_tsum_eq_large P D K k1 hP hP32 hs, ← hE]
    refine tsum_congr fun ℓ => ?_
    rw [← hrel ℓ]
  -- Step 4: the variable `t = 1/(1+s)`
  let M : ℕ := (k1 - D).toNat
  have hM : k1 ≤ D + 2 + M := by simp only [M]; omega
  let a : ℕ → ℂ := fun n => P (D + 1 + M - n)
  let φ : ℂ → ℂ := fun t => ∑' n : ℕ, a n * t ^ n
  let ψ : ℂ → ℂ := fun t => ∑ ℓ ∈ S, c ℓ * (t ^ ((M : ℤ) + K + ℓ + 1) * (1 - t) ^ (-ℓ - 1))
  have hexpS : ∀ ℓ ∈ S, 0 ≤ (M : ℤ) + K + ℓ + 1 := by
    intro ℓ hℓ
    simp only [S, Finset.mem_Ioo] at hℓ
    omega
  -- `φ` and `ψ` against the series, at real `t ∈ (0,1)`, `s = 1/t - 1`
  have hφ_eq : ∀ t : ℝ, 0 < t → t < 1 →
      φ t = (t : ℂ) ^ M * ∑' k : ℤ, P k * (1 + ((1 / t - 1 : ℝ) : ℂ)) ^ (k - D - 1) := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
    let g : ℕ → ℤ := fun n => D + 1 + M - n
    have hg : Function.Injective g := fun n m h => by simp only [g] at h; omega
    let f : ℤ → ℂ := fun k => P k * (1 + ((1 / t - 1 : ℝ) : ℂ)) ^ (k - D - 1)
    have hsupp : Function.support f ⊆ Set.range g := by
      intro k hk
      have hPk : P k ≠ 0 := fun h0 => hk (by simp only [f, h0, zero_mul])
      have hk1 : k < k1 := by
        by_contra h; exact hPk (hP k (not_lt.mp h))
      exact ⟨(D + 1 + M - k).toNat, by simp only [g]; omega⟩
    rw [← hg.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [a, f, g, h1s]
    rw [show D + 1 + (M : ℤ) - n - D - 1 = (M : ℤ) - n by ring, inv_zpow', neg_sub,
      zpow_sub₀ ht, zpow_natCast, zpow_natCast]
    field_simp
  have hψ_eq : ∀ t : ℝ, 0 < t → t < 1 →
      ψ t = (t : ℂ) ^ ((M : ℤ) + K) * E ((1 / t - 1 : ℝ) : ℂ) := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have h1t : (1 - (t : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]; linarith
    have hs : ((1 / t - 1 : ℝ) : ℂ) = (1 - (t : ℂ)) / t := by push_cast; field_simp
    simp only [ψ, E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [hs, div_zpow, show (M : ℤ) + K + ℓ + 1 = ((M : ℤ) + K) - (-ℓ - 1) by ring,
      zpow_sub₀ ht]
    field_simp
  -- agreement for `t ∈ (0, 1/4]`
  have hagree : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 → φ t = ψ t := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hs3 : 3 ≤ 1 / t - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ ht0]; linarith
    rw [hφ_eq t ht0 (by linarith), hψ_eq t ht0 (by linarith), ← hstep3 _ hs3]
    have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
    rw [h1s, inv_pow, zpow_add₀ ht, zpow_natCast, zpow_natCast]
    field_simp
  -- analyticity on the unit disc
  have ha : ∀ q : ℂ, ‖q‖ < 1 → Summable fun n => a n * q ^ n := by
    intro q hq
    obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hq (by norm_num : (1 / 2 : ℝ) < 1))
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
    have hts : Summable fun n => a n * (t : ℂ) ^ n := by
      have hsum := hProd (1 / t - 1) (by
          rw [sub_pos, lt_div_iff₀ ht0]; linarith)
        (by
          have : (1 / 2 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht1
          rw [sub_lt_iff_lt_add, div_lt_iff₀ ht0]; nlinarith)
      have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
      have hc := (hsum.comp_injective (fun n m h => by simp only at h; omega :
        Function.Injective fun n : ℕ => D + 1 + (M : ℤ) - n)).mul_left ((t : ℂ) ^ M)
      refine hc.congr fun n => ?_
      simp only [Function.comp, a, h1s]
      rw [show D + 1 + (M : ℤ) - n - D - 1 = (M : ℤ) - n by ring, inv_zpow', neg_sub,
        zpow_sub₀ ht, zpow_natCast, zpow_natCast]
      field_simp
    refine Summable.of_norm_bounded (summable_norm_iff.mpr hts) fun n => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    gcongr
    exact (le_max_left _ _).trans ht1.le
  have hφd : DifferentiableOn ℂ φ (Metric.ball 0 1) := fun z hz =>
    (VOA.Huang.HKLLoc.differentiableAt_powerSeries a ha
      (by simpa using hz)).differentiableWithinAt
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 1) := by
    intro z hz
    have hz1 : 1 - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this, Metric.mem_ball, dist_zero_right, norm_one] at hz
      exact lt_irrefl _ hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun ℓ hℓ => ?_
    refine DifferentiableAt.const_mul (DifferentiableAt.mul ?_ ?_) _
    · exact (differentiableAt_zpow).mpr (Or.inr (hexpS ℓ hℓ))
    · exact ((differentiableAt_zpow).mpr (Or.inl hz1)).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
  have hEq : Set.EqOn φ ψ (Metric.ball 0 1) := by
    refine (hφd.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (hψd.analyticOnNhd Metric.isOpen_ball) (convex_ball 0 1).isPreconnected
      (z₀ := (((1 / 8 : ℝ)) : ℂ)) ?_ ?_
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    · exact frequently_real_near fun x hx0 hx1 => hagree x hx0 hx1
  -- Step 5: conclusion at the complex point `t₀ = 1/(1+s₀)`
  have h1s0 : (1 + s₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs1
    linarith
  set t₀ : ℂ := 1 / (1 + s₀) with ht₀
  have ht : t₀ ≠ 0 := one_div_ne_zero h1s0
  have h1s : (1 + s₀) = t₀⁻¹ := by rw [ht₀, one_div, inv_inv]
  clear_value t₀
  have hmem : t₀ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, ht₀, norm_div, norm_one,
      div_lt_one (by linarith)]
    exact hs1
  have h1t : 1 - t₀ ≠ 0 := by
    intro h
    have : t₀ = 1 := by linear_combination -h
    rw [this, Metric.mem_ball, dist_zero_right, norm_one] at hmem
    exact lt_irrefl _ hmem
  have hφ0 : φ t₀ = t₀ ^ M * ∑' k : ℤ, P k * (1 + s₀) ^ (k - D - 1) := by
    let g : ℕ → ℤ := fun n => D + 1 + M - n
    have hg : Function.Injective g := fun n m h => by simp only [g] at h; omega
    let f : ℤ → ℂ := fun k => P k * (1 + s₀) ^ (k - D - 1)
    have hsupp : Function.support f ⊆ Set.range g := by
      intro k hk
      have hPk : P k ≠ 0 := fun h0 => hk (by simp only [f, h0, zero_mul])
      have hk1 : k < k1 := by
        by_contra h; exact hPk (hP k (not_lt.mp h))
      exact ⟨(D + 1 + M - k).toNat, by simp only [g]; omega⟩
    rw [← hg.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [a, f, g, h1s]
    rw [show D + 1 + (M : ℤ) - n - D - 1 = (M : ℤ) - n by ring, inv_zpow', neg_sub,
      zpow_sub₀ ht, zpow_natCast, zpow_natCast]
    field_simp
  have hψ0 : ψ t₀ = t₀ ^ ((M : ℤ) + K) * E s₀ := by
    have hs : s₀ = (1 - t₀) / t₀ := by
      rw [sub_div, one_div, div_self ht, ← h1s]
      ring
    simp only [ψ, E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [hs, div_zpow, show (M : ℤ) + K + ℓ + 1 = ((M : ℤ) + K) - (-ℓ - 1) by ring,
      zpow_sub₀ ht]
    field_simp
  have key := hEq hmem
  rw [hφ0, hψ0, ← hstep2 s₀ hs0 hIt₀] at key
  have htM : t₀ ^ M ≠ 0 := pow_ne_zero _ ht
  have htK : t₀ ^ K ≠ 0 := pow_ne_zero _ ht
  have hK : t₀ ^ ((M : ℤ) + K) * (1 + s₀) ^ K = t₀ ^ M := by
    rw [h1s, zpow_add₀ ht, zpow_natCast, zpow_natCast, inv_pow, mul_assoc,
      mul_inv_cancel₀ htK, mul_one]
  rw [← mul_assoc, hK] at key
  exact (mul_left_cancel₀ htM key).symm

end VOA.Huang.HKLRational

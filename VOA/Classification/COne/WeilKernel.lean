/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.WeilGalois

/-!
# The kernel law (G5)

We prove `WeilGalois.weilKernelLaw : WeilKernelLaw`: for `4N ∣ M`, `24 ∣ M` and
`γ ∈ Γ(M)`, every Weil word matrix `A` of `γ` has `A₀₀ = 1` (the congruence property of the
η-twisted Weil representation `Θ_{N,·}/η`). Consequently `weilGaloisLaw` and `thetaGaloisLaw`
(GR Prop. 3.8) hold unconditionally.

## Route

* **Gauss's sign theorem** `gaussG_one`: `∑_{k mod 2K} e(k²/4K) = e(1/8) √(2K)`. It is read off
  from the analytic transformation law: `γ = 1` has the Weil word `dlMat K 1 1`, whose `(0,0)`
  entry is `ω₂₄³ G₁/√(2K)`, and `entry_eq_one_of_inv` forces this entry to be `1` because
  `Θ_{K,0}/η` is not identically zero (its limit at `i∞` after multiplying by `η` is `1`).
* **The anchor `N = 6`** (`six_entry`): `χ₁₂` is a fixed row vector of every `N = 6` Weil word
  (`η = ∑ χ₁₂(n) q^{n²/24}`), which with monomiality forces `B₀₀ = 1` for `γ ∈ Γ(24)`.
* **The cusp** (`theta_mobius`, Poisson summation per residue class): for `c > 0`,
  `θ_N(γτ) = (−iσ/2Nc²)^{1/2} ∑_j K(j) e(j²τ/4N)`. The cross relation
  `θ_N(γτ) θ_6(τ) = A₀₀ θ_N(τ) θ_6(γτ)` compared at `τ = it → i∞` (`cusp_limit`) gives
  `√(1/2Nc²) g(c, Na) = A₀₀ √(1/12c²) g(c, 6a)`, and `cusp_ratio` (the Gauss-sum evaluation via
  `gaussRatioLaw`, `gaussG_one` and the Jacobi law) shows both sides' Gauss factors agree and are
  nonzero. `c < 0` is reduced to `c > 0` through `−γ` (same Möbius action; `g(c, −a)` is the
  complex conjugate), and `c = 0` means `γ = T^{24k}`, handled by `weilVec_zero_add_24`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace VOA.Classification.COne

namespace WeilGalois

/-! ## Analytic preliminaries -/

theorem summable_exp_neg_sq {α : ℝ} (hα : 0 < α) :
    Summable fun j : ℤ => Real.exp (-(α * (j : ℝ) ^ 2)) := by
  have hτ : 0 < (I * ((α / Real.pi : ℝ) : ℂ)).im := by
    simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
    exact div_pos hα Real.pi_pos
  have h := ((summable_jacobiTheta₂_term_iff 0 _).2 hτ).norm
  refine h.congr fun j => ?_
  rw [norm_jacobiTheta₂_term]
  simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, zero_im,
    sub_zero]
  congr 1
  field_simp

theorem tendsto_tsum_gauss (K : ℤ → ℂ) {B : ℝ} (hK : ∀ j, ‖K j‖ ≤ B) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => ∑' j : ℤ, K j * (Real.exp (-(α * (j : ℝ) ^ 2 * t)) : ℂ)) atTop
      (𝓝 (K 0)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hK 0)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (j : ℤ) => K j * (Real.exp (-(α * (j : ℝ) ^ 2 * t)) : ℂ))
    (g := fun j : ℤ => if j = 0 then K 0 else 0)
    (bound := fun j : ℤ => B * Real.exp (-(α * (j : ℝ) ^ 2)))
    ((summable_exp_neg_sq hα).mul_left B) ?_ ?_
  · simpa [tsum_ite_eq] using h
  · intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · simp only [hj, if_false]
      have hpos : 0 < α * (j : ℝ) ^ 2 := by
        have : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
        positivity
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(α * (j : ℝ) ^ 2 * t))) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (Tendsto.const_mul_atTop hpos tendsto_id)
        refine this.congr fun t => ?_
        simp [Function.comp]
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (K j)
      simpa using h2
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht j
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul (hK j) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hB
    have : 0 ≤ α * (j : ℝ) ^ 2 := by positivity
    nlinarith

/-- `(z r)^{1/2} = z^{1/2} √r` for `r > 0`. -/
theorem cpow_half_mul_ofReal {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) :
    (z * (r : ℂ)) ^ (1 / 2 : ℂ) = z ^ (1 / 2 : ℂ) * (Real.sqrt r : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hz hr'), log_mul_ofReal r hr z hz,
    cpow_def_of_ne_zero hz, Real.sqrt_eq_rpow, ofReal_cpow hr.le, cpow_def_of_ne_zero hr',
    ← ofReal_log hr.le, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {N : ℕ}

/-- **The `(0,0)` row of a congruence word**: if `4N ∣ b, c`, then `F₀(γτ) = A₀₀ F₀(τ)`. -/
theorem weilVec_zero_mobius (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A)
    (hb : ((4 * N : ℕ) : ℤ) ∣ γ 0 1) (hc : ((4 * N : ℕ) : ℤ) ∣ γ 1 0) {τ : ℂ} (hτ : 0 < τ.im) :
    weilVec N 0 (mobius γ τ) = A (fz hN) (fz hN) * weilVec N 0 τ := by
  obtain ⟨s, -, hd⟩ := weilWord_diag hN h hb hc
  have hT := weilWord_transform hN h hτ (fz hN)
  have h0 : (((fz hN : Fin (2 * N)) : ℕ) : ℤ) = 0 := by simp [fz]
  rw [h0] at hT
  rw [hT, Finset.sum_eq_single (fz hN)]
  · rw [h0]
  · intro j _ hj
    rw [hd, if_neg, zero_mul]
    intro hj'
    apply hj
    apply fin_eq_of_modEq
    rw [h0]
    simpa using hj'
  · simp

theorem weilTheta_zero_I (hN : 0 < N) (t : ℝ) :
    weilTheta N 0 (I * t) =
      ∑' m : ℤ, (fun _ : ℤ => (1 : ℂ)) m *
        (Real.exp (-(2 * Real.pi * N * (m : ℝ) ^ 2 * t)) : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold weilTheta rankOneTheta
  refine tsum_congr fun m => ?_
  unfold rankOneThetaTerm
  rw [one_mul, ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem tendsto_weilTheta_zero (hN : 0 < N) :
    Tendsto (fun t : ℝ => weilTheta N 0 (I * t)) atTop (𝓝 1) := by
  have hα : 0 < 2 * Real.pi * N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 hN
    positivity
  have h := tendsto_tsum_gauss (fun _ : ℤ => (1 : ℂ)) (B := 1) (fun _ => by simp) hα
  refine h.congr fun t => ?_
  rw [weilTheta_zero_I hN]

theorem exists_weilVec_zero_ne (hN : 0 < N) : ∃ τ : ℂ, 0 < τ.im ∧ weilVec N 0 τ ≠ 0 := by
  have h := ((tendsto_weilTheta_zero hN).eventually_ne one_ne_zero).and
    (eventually_gt_atTop (0 : ℝ))
  obtain ⟨t, ht, ht0⟩ := h.exists
  refine ⟨I * t, by simpa using ht0, ?_⟩
  rw [weilVec]
  exact div_ne_zero ht (ModularForm.eta_ne_zero (by simpa using ht0))

/-- If `4N ∣ b, c` and `F₀ ∘ γ = F₀`, then every Weil word of `γ` has `A₀₀ = 1`. -/
theorem entry_eq_one_of_inv (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A)
    (hb : ((4 * N : ℕ) : ℤ) ∣ γ 0 1) (hc : ((4 * N : ℕ) : ℤ) ∣ γ 1 0)
    (hinv : ∀ τ : ℂ, 0 < τ.im → weilVec N 0 (mobius γ τ) = weilVec N 0 τ) :
    A (fz hN) (fz hN) = 1 := by
  obtain ⟨τ, hτ, hne⟩ := exists_weilVec_zero_ne hN
  have h1 := weilVec_zero_mobius hN h hb hc hτ
  rw [hinv τ hτ] at h1
  have : (A (fz hN) (fz hN) - 1) * weilVec N 0 τ = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 this with h2 | h2
  · linear_combination h2
  · exact absurd h2 hne

theorem dl_one_one : dl 1 1 = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := dl_apply 1 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

/-- **Gauss's sign theorem** for even moduli: `∑_{k mod 2K} e(k²/4K) = e(1/8) √(2K)`. -/
theorem gaussG_one {K : ℕ} (hK : 0 < K) :
    gaussG K 1 = cexp (2 * Real.pi * I / 8) * (Real.sqrt (2 * K) : ℂ) := by
  have h1 := entry_eq_one_of_inv hK (dl_weilWord K 1 1) (by rw [dl_one_one]; simp)
    (by rw [dl_one_one]; simp) (fun τ _ => by rw [dl_one_one, mobius_one])
  rw [dlMat_apply hK 1 1 (by norm_num)] at h1
  have hr : (Real.sqrt (2 * K) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * K := by have : (0 : ℝ) < K := Nat.cast_pos.2 hK; positivity
    exact ofReal_ne_zero.2 (Real.sqrt_pos.2 this).ne'
  have he : omega24 ^ 3 * cexp (2 * Real.pi * I / 8) = 1 := by
    unfold omega24
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast; ring
  push_cast at h1
  field_simp at h1
  linear_combination (cexp (2 * Real.pi * I / 8)) * h1 - gaussG K 1 * he

/-! ## The anchor `N = 6`: `χ₁₂` is a fixed vector -/

/-- `χ₁₂`, the character of `η`: `η = ∑_n χ₁₂(n) q^{n²/24}`. -/
def chi12 (n : ℕ) : ℂ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1 else if n % 12 = 5 ∨ n % 12 = 7 then -1 else 0

/-- `ζ = e(1/12)`. -/
def zeta12 : ℂ := cexp (2 * Real.pi * I / 12)

theorem zeta12_pow (n : ℕ) : cexp (2 * Real.pi * I * (n : ℂ) / 12) = zeta12 ^ n := by
  rw [zeta12, ← Complex.exp_nat_mul]; congr 1; ring

theorem zeta12_pow_twelve : zeta12 ^ 12 = 1 := by
  rw [← zeta12_pow]; push_cast
  rw [show 2 * (Real.pi : ℂ) * I * 12 / 12 = 2 * Real.pi * I by ring, Complex.exp_two_pi_mul_I]

theorem zeta12_pow_mod (n : ℕ) : zeta12 ^ n = zeta12 ^ (n % 12) := by
  conv_lhs => rw [← Nat.div_add_mod n 12, pow_add, pow_mul, zeta12_pow_twelve, one_pow, one_mul]

theorem zeta12_pow_six : zeta12 ^ 6 = -1 := by
  rw [← zeta12_pow]; push_cast
  rw [show 2 * (Real.pi : ℂ) * I * 6 / 12 = Real.pi * I by ring, Complex.exp_pi_mul_I]

theorem zeta12_eq : zeta12 = (Real.sqrt 3 : ℂ) / 2 + (1 / 2 : ℂ) * I := by
  rw [zeta12, show 2 * (Real.pi : ℂ) * I / 12 = ((Real.pi / 6 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast; ring

theorem zeta12_add : zeta12 + zeta12 ^ 11 = Real.sqrt 3 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hzw : zeta12 * ((Real.sqrt 3 : ℂ) / 2 - (1 / 2 : ℂ) * I) = 1 := by
    rw [zeta12_eq]
    linear_combination (1 / 4 : ℂ) * h3 - (1 / 4 : ℂ) * I_sq
  have h11 : zeta12 ^ 11 = (Real.sqrt 3 : ℂ) / 2 - (1 / 2 : ℂ) * I := by
    linear_combination (-zeta12 ^ 11) * hzw +
      ((Real.sqrt 3 : ℂ) / 2 - (1 / 2 : ℂ) * I) * zeta12_pow_twelve
  rw [h11, zeta12_eq]; ring

theorem weilS_six (μ j : Fin (2 * 6)) :
    weilS 6 μ j = ((Real.sqrt 12)⁻¹ : ℝ) * zeta12 ^ (((j : ℕ) * (μ : ℕ)) % 12) := by
  rw [weilS, ← zeta12_pow_mod, ← zeta12_pow]
  congr 2
  · norm_num
  · push_cast; ring

theorem chi12_weilS (j : Fin (2 * 6)) :
    ∑ μ : Fin (2 * 6), chi12 μ * weilS 6 μ j = chi12 j := by
  simp_rw [weilS_six]
  set c : ℂ := (((Real.sqrt 12)⁻¹ : ℝ) : ℂ)
  have hc : c * (2 * Real.sqrt 3) = 1 := by
    have : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    simp only [c, this]; push_cast
    field_simp
  have h5 : zeta12 ^ 5 + zeta12 ^ 11 = 0 := by
    linear_combination (-zeta12 ^ 5) * zeta12_pow_twelve + zeta12 ^ 11 * zeta12_pow_six
  have h7 : zeta12 ^ 7 + zeta12 = 0 := by
    linear_combination zeta12 * zeta12_pow_six
  have hs := zeta12_add
  fin_cases j <;> simp [Fin.sum_univ_succ, chi12] <;>
    first
    | ring1
    | linear_combination 2 * c * hs - c * h5 - c * h7 + hc
    | linear_combination c * h5 + c * h7 - 2 * c * hs - hc

theorem chi12_weilPhase (j : Fin (2 * 6)) : chi12 j * weilPhase 6 ((j : ℕ) : ℤ) = chi12 j := by
  have e : ∀ (k m : ℤ), k ^ 2 - 1 = 24 * m →
      weilPhase 6 k = 1 := by
    intro k m hkm
    rw [weilPhase, ← Complex.exp_add]
    have : (k : ℂ) ^ 2 = 24 * m + 1 := by
      have := congrArg (fun x : ℤ => (x : ℂ)) hkm; push_cast at this; linear_combination this
    rw [this, show 2 * (Real.pi : ℂ) * I * (24 * m + 1) / (4 * ((6 : ℕ) : ℂ)) +
        -(2 * Real.pi * I / 24) = m * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  fin_cases j <;> simp only [chi12] <;> norm_num <;>
    first
    | exact e 1 0 (by norm_num)
    | exact e 5 1 (by norm_num)
    | exact e 7 2 (by norm_num)
    | exact e 11 5 (by norm_num)

theorem chi12_diag (d : Fin (2 * 6) → ℂ) (hd : ∀ j : Fin (2 * 6), chi12 j * d j = chi12 j)
    (j : Fin (2 * 6)) :
    ∑ μ : Fin (2 * 6), chi12 μ * Matrix.diagonal d μ j = chi12 j := by
  simp [Matrix.diagonal_apply, hd]

/-- `χ₁₂` is a fixed row vector of every `N = 6` Weil word (the finite shadow of
`η = ∑ χ₁₂(n) q^{n²/24}`). -/
theorem chi12_word {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * 6)) (Fin (2 * 6)) ℂ} (h : WeilWord 6 γ A) (j : Fin (2 * 6)) :
    ∑ μ : Fin (2 * 6), chi12 μ * A μ j = chi12 j := by
  have step : ∀ (B C : Matrix (Fin (2 * 6)) (Fin (2 * 6)) ℂ),
      (∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * B μ ν = chi12 ν) →
      (∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * C μ ν = chi12 ν) →
      ∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * (B * C) μ ν = chi12 ν := by
    intro B C hB hC ν
    simp_rw [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hB]
    exact hC ν
  have hS : ∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * weilS 6 μ ν = chi12 ν := chi12_weilS
  have hT : ∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * weilT 6 μ ν = chi12 ν :=
    chi12_diag _ chi12_weilPhase
  have hTi : ∀ ν, ∑ μ : Fin (2 * 6), chi12 μ * weilTinv 6 μ ν = chi12 ν := by
    refine chi12_diag _ fun (ν : Fin (2 * 6)) => ?_
    have h1 := chi12_weilPhase ν
    by_cases h0 : chi12 ν = 0
    · simp [h0]
    · have : weilPhase 6 ((ν : ℕ) : ℤ) = 1 := by
        have := mul_left_cancel₀ h0 (h1.trans (mul_one _).symm); exact this
      simp [this]
  induction h generalizing j with
  | one => simp [Matrix.one_apply]
  | S _ ih => exact step _ _ hS ih j
  | Sinv _ ih => exact step _ _ hS ih j
  | T _ ih => exact step _ _ hT ih j
  | Tinv _ ih => exact step _ _ hTi ih j

/-- **The kernel law at `N = 6`**: `γ ≡ 1 (mod 24)`-type words have `A₀₀ = 1`. -/
theorem six_entry {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * 6)) (Fin (2 * 6)) ℂ} (h : WeilWord 6 γ A)
    (hb : ((4 * 6 : ℕ) : ℤ) ∣ γ 0 1) (hc : ((4 * 6 : ℕ) : ℤ) ∣ γ 1 0)
    (ha : γ 0 0 ≡ 1 [ZMOD 12]) : A (fz (by norm_num)) (fz (by norm_num)) = 1 := by
  obtain ⟨s, hs, hd⟩ := weilWord_diag (by norm_num) h hb hc
  have hw := chi12_word h ⟨1, by norm_num⟩
  have hcond : ∀ μ : Fin (2 * 6), (((1 : ℕ) : ℤ) ≡ s * γ 0 0 * ((μ : ℕ) : ℤ) [ZMOD (2 * 6 : ℕ)]
      ↔ (1 : ℤ) ≡ s * ((μ : ℕ) : ℤ) [ZMOD 12]) := by
    intro μ
    have : s * γ 0 0 * ((μ : ℕ) : ℤ) ≡ s * ((μ : ℕ) : ℤ) [ZMOD 12] := by
      have := (ha.mul_left s).mul_right ((μ : ℕ) : ℤ); simpa using this
    constructor
    · intro h'; push_cast at h'; exact h'.trans this
    · intro h'; push_cast; exact h'.trans this.symm
  replace hw : ∑ μ : Fin (2 * 6), chi12 μ * (if (1 : ℤ) ≡ s * ((μ : ℕ) : ℤ) [ZMOD 12] then
      A (fz (by norm_num)) (fz (by norm_num)) else 0) = chi12 1 := by
    rw [← hw]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hd μ ⟨1, by norm_num⟩]
    exact congrArg _ (if_congr (hcond μ) rfl rfl).symm
  have h1 : chi12 1 = 1 := by simp [chi12]
  have h11 : chi12 11 = 1 := by simp [chi12]
  rcases hs with rfl | rfl
  · rw [Finset.sum_eq_single (⟨1, by norm_num⟩ : Fin (2 * 6))] at hw
    · simpa [Int.ModEq, h1] using hw
    · intro μ _ hμ
      rw [if_neg, mul_zero]
      intro hc'
      apply hμ
      have hlt := μ.isLt
      ext
      show (μ : ℕ) = 1
      simp only [Int.ModEq] at hc'
      push_cast at hc'
      omega
    · simp
  · rw [Finset.sum_eq_single (⟨11, by norm_num⟩ : Fin (2 * 6))] at hw
    · simpa [Int.ModEq, h11, h1] using hw
    · intro μ _ hμ
      rw [if_neg, mul_zero]
      intro hc'
      apply hμ
      have hlt := μ.isLt
      ext
      show (μ : ℕ) = 11
      simp only [Int.ModEq] at hc'
      push_cast at hc'
      omega
    · simp

/-! ## The theta series at a cusp -/

/-- `σ = c (cτ + d)`. -/
def sig (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + γ 1 1)

/-- The coefficient `K(j) = (∑_{x mod c} e((N a x² + j x)/c)) e(j² d/4Nc)`. -/
def Kc (N : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (c : ℕ) (j : ℤ) : ℂ :=
  (∑ x : Fin c, cexp (2 * Real.pi * I *
      (((N : ℤ) * γ 0 0 * ((x : ℕ) : ℤ) ^ 2 + j * ((x : ℕ) : ℤ) : ℤ) : ℂ) / c)) *
    cexp (2 * Real.pi * I * ((j ^ 2 * γ 1 1 : ℤ) : ℂ) / (4 * N * c))

theorem im_neg_inv_pos {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-1 / σ).im := by
  rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hσ (normSq_pos.2 fun h => by simp [h] at hσ)

/-- **The theta series at a cusp** (Poisson summation per residue class): for `c > 0`,
`θ_N(γτ) = (−iσ/2Nc²)^{1/2} ∑_j K(j) e(j²τ/4N)` with `σ = c(cτ + d)`. -/
theorem theta_mobius {N : ℕ} (hN : 0 < N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {c : ℕ}
    (hc : 0 < c) (hcγ : γ 1 0 = c) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta 0 1 N (mobius γ τ) =
      (-I * (sig γ τ / (2 * ((N : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2))) ^ (1 / 2 : ℂ) *
        ∑' j : ℤ, Kc N γ c j * cexp (2 * Real.pi * I * τ * (j : ℂ) ^ 2 / (4 * N)) := by
  haveI : NeZero c := ⟨hc.ne'⟩
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcz : ((c : ℤ) : ℂ) = (c : ℂ) := by push_cast; rfl
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := det_SL γ
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hdet
    simp only [hcγ] at this; push_cast at this; exact this
  have hσdef : sig γ τ = (c : ℂ) * ((c : ℂ) * τ + (γ 1 1 : ℂ)) := by
    simp only [sig, hcγ]; push_cast; rfl
  have hcd : (c : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rcases this with h1 | h1
    · exact hc0 (by exact_mod_cast h1)
    · linarith
  have hσ : 0 < (sig γ τ).im := by
    rw [hσdef]
    have : (c : ℂ) * ((c : ℂ) * τ + (γ 1 1 : ℂ)) =
        ((c : ℝ) ^ 2 : ℝ) * τ + ((c * γ 1 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [this, add_im, im_ofReal_mul]
    simp only [intCast_im, add_zero]
    have : (0 : ℝ) < c := Nat.cast_pos.2 hc
    positivity
  have hσ0 : sig γ τ ≠ 0 := fun h => by rw [h] at hσ; simp at hσ
  set σ := sig γ τ with hσσ
  have hmob : mobius γ τ = (γ 0 0 : ℂ) / c + (-1 / σ) := by
    rw [mobius, hσdef, show ((γ 1 0 : ℤ) : ℂ) = (c : ℂ) by rw [hcγ]; push_cast; rfl]
    rw [div_add_div _ _ hc0 (mul_ne_zero hc0 hcd),
      div_eq_div_iff hcd (mul_ne_zero hc0 (mul_ne_zero hc0 hcd))]
    linear_combination (-((c : ℂ) * ((c : ℂ) * τ + (γ 1 1 : ℂ)))) * hdetC
  -- regroup `m = k c + x`
  set f : ℤ → ℂ := rankOneThetaTerm 0 1 N (mobius γ τ) with hf
  have hsum : Summable f := summable_rankOneThetaTerm 0 one_ne_zero hNr (im_mobius_pos γ hτ)
  set e : Fin c → ℂ := fun x =>
    cexp (2 * Real.pi * I * (((N : ℤ) * γ 0 0 * ((x : ℕ) : ℤ) ^ 2 : ℤ) : ℂ) / c)
    with he
  have hterm : ∀ (x : Fin c) (k : ℤ), f ((Int.divModEquiv c).symm (k, x)) =
      e x * rankOneThetaTerm ((x : ℕ) : ℤ) (c : ℤ) N (-1 / σ) k := by
    intro x k
    simp only [hf, he, Int.divModEquiv_symm_apply, rankOneThetaTerm, hmob]
    rw [← Complex.exp_add]
    have : 2 * Real.pi * I * ((N : ℝ) : ℂ) *
        (((0 : ℤ) + 1 * (k * (c : ℤ) + ((x : ℕ) : ℤ)) : ℤ) : ℂ) ^ 2
        * ((γ 0 0 : ℂ) / c + -1 / σ) =
        2 * Real.pi * I * (((N : ℤ) * γ 0 0 * ((x : ℕ) : ℤ) ^ 2 : ℤ) : ℂ) / c +
          2 * Real.pi * I * ((N : ℝ) : ℂ) * ((((x : ℕ) : ℤ) + (c : ℤ) * k : ℤ) : ℂ) ^ 2 * (-1 / σ) +
          ((N : ℤ) * γ 0 0 * (k ^ 2 * c + 2 * k * ((x : ℕ) : ℤ)) : ℤ) * (2 * Real.pi * I) := by
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hprod : HasSum (fun p : Fin c × ℤ => f ((Int.divModEquiv c).symm (p.2, p.1)))
      (∑' m, f m) := by
    have := ((Int.divModEquiv c).symm.hasSum_iff.mpr hsum.hasSum)
    exact (Equiv.prodComm (Fin c) ℤ).hasSum_iff.mpr this
  have hNeg : 0 < (-1 / σ).im := im_neg_inv_pos hσ
  have hfib : ∀ x : Fin c, HasSum (fun k : ℤ => f ((Int.divModEquiv c).symm (k, x)))
      (e x * rankOneTheta ((x : ℕ) : ℤ) (c : ℤ) N (-1 / σ)) := by
    intro x
    simp_rw [hterm]
    exact ((summable_rankOneThetaTerm ((x : ℕ) : ℤ) (Int.natCast_ne_zero.2 hc.ne') hNr
      hNeg).hasSum).mul_left _
  have hsplit : rankOneTheta 0 1 N (mobius γ τ) =
      ∑ x : Fin c, e x * rankOneTheta ((x : ℕ) : ℤ) (c : ℤ) N (-1 / σ) := by
    rw [rankOneTheta]
    exact (hprod.prod_fiberwise hfib).unique (hasSum_fintype _)
  set J : ℂ := (-I * (σ / (2 * ((N : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2))) ^ (1 / 2 : ℂ) with hJ
  set g : Fin c → ℤ → ℂ := fun x j =>
    cexp (2 * Real.pi * I * (j : ℂ) * (((x : ℕ) : ℤ) : ℂ) / ((c : ℤ) : ℂ)) *
      cexp (2 * Real.pi * I * σ * (j : ℂ) ^ 2 / (4 * ((N : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2)) with hg
  have hS : ∀ x : Fin c, rankOneTheta ((x : ℕ) : ℤ) (c : ℤ) N (-1 / σ) = J * ∑' j : ℤ, g x j :=
    fun x => rankOneTheta_S_tsum _ (Int.natCast_ne_zero.2 hc.ne') hNr hσ
  have hτ' : 0 < (σ / (2 * ((N : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2)).im := by
    rw [show (2 * ((N : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2) = ((2 * N * (c : ℝ) ^ 2 : ℝ) : ℂ) by
      push_cast; ring, div_ofReal_im]
    have : (0 : ℝ) < c := Nat.cast_pos.2 hc
    positivity
  have hgs : ∀ x : Fin c, Summable (g x) := by
    intro x
    refine ((summable_jacobiTheta₂_term_iff ((((x : ℕ) : ℤ) : ℂ) / ((c : ℤ) : ℂ)) _).2 hτ').congr
      fun j => ?_
    rw [jacobiTheta₂_term]
    simp only [hg]
    rw [← Complex.exp_add]
    congr 1
    rw [hcz]
    field_simp
    ring
  rw [hsplit, Finset.sum_congr rfl fun x _ => by rw [hS x]]
  calc ∑ x : Fin c, e x * (J * ∑' j : ℤ, g x j)
      = J * ∑ x : Fin c, ∑' j : ℤ, e x * g x j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [tsum_mul_left]; ring
    _ = J * ∑' j : ℤ, ∑ x : Fin c, e x * g x j := by
        rw [Summable.tsum_finsetSum fun x _ => (hgs x).mul_left _]
    _ = J * ∑' j : ℤ, Kc N γ c j * cexp (2 * Real.pi * I * τ * (j : ℂ) ^ 2 / (4 * N)) := by
        congr 1
        refine tsum_congr fun j => ?_
        rw [Kc, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [he, hg]
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        rw [hσdef, hcz]
        push_cast
        field_simp
        ring

theorem sig_im_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {c : ℕ} (hc : 0 < c)
    (hcγ : γ 1 0 = c) {τ : ℂ} (hτ : 0 < τ.im) : 0 < (sig γ τ).im := by
  have : sig γ τ = ((c : ℝ) ^ 2 : ℝ) * τ + ((c * γ 1 1 : ℤ) : ℂ) := by
    simp only [sig, hcγ]; push_cast; ring
  rw [this, add_im, im_ofReal_mul]
  simp only [intCast_im, add_zero]
  have : (0 : ℝ) < c := Nat.cast_pos.2 hc
  positivity

/-! ## Gauss sums at the cusp -/

theorem gs_scale {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : ℤ) :
    gs (n * m) (n * a) = n * gs m a := by
  unfold gs
  have h1 : ∀ y : ℤ, E (n * m) ((n : ℤ) * a * y ^ 2) = E m (a * y ^ 2) := by
    intro y
    rw [Nat.mul_comm n m, show (n : ℤ) * a * y ^ 2 = n * (a * y ^ 2) by ring, E_mul_left hn]
  simp_rw [h1]
  have hs := sum_split (c := n * m) (m := m) (n := n) (Nat.mul_comm n m) (Nat.mul_pos hn hm)
    (fun x => E m (a * x ^ 2)) (fun x => by
      simp only
      rw [← E_period hm (a * x ^ 2) (a * (2 * x * n + n ^ 2 * m))]
      congr 1; push_cast; ring)
  simp only at hs
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : ∀ z : Fin n, E m (a * (((y : ℕ) : ℤ) + m * ((z : ℕ) : ℤ)) ^ 2) =
      E m (a * ((y : ℕ) : ℤ) ^ 2) := by
    intro z
    rw [← E_period hm (a * ((y : ℕ) : ℤ) ^ 2) (a * (2 * ((y : ℕ) : ℤ) * ((z : ℕ) : ℤ) +
      m * ((z : ℕ) : ℤ) ^ 2))]
    congr 1; ring
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gs_congr {m : ℕ} (hm : 0 < m) {a a' : ℤ} (h : a ≡ a' [ZMOD m]) : gs m a = gs m a' := by
  unfold gs
  exact Finset.sum_congr rfl fun x _ => E_congr hm (h.mul_right _)

/-- `g(4K, ℓ) = 2 (2K/ℓ) e(1/8) √(2K)` for `ℓ ≡ 1 (mod 8)` prime to `2K`. -/
theorem gs_four_eval {K : ℕ} (hK : 0 < K) {ℓ : ℕ} (hcop : ℓ.Coprime (2 * K)) (h8 : ℓ % 8 = 1) :
    gs (4 * K) ℓ = 2 * (jacobiSym (2 * (K : ℤ)) ℓ : ℂ) * cexp (2 * Real.pi * I / 8) *
      (Real.sqrt (2 * K) : ℂ) := by
  rw [gs_four_mul hK, gaussRatioLaw K hK ℓ hcop, gaussG_one hK]
  have : cexp (2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8) = 1 := by
    obtain ⟨q, hq⟩ : ∃ q : ℕ, ℓ = 8 * q + 1 := ⟨ℓ / 8, by omega⟩
    rw [hq, show 2 * (Real.pi : ℂ) * I * (((8 * q + 1 : ℕ) : ℂ) - 1) / 8 =
      ((q : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I]
  rw [this]; ring

theorem sqrt_cusp {N K c : ℕ} (hN : 0 < N) (hK : 0 < K) (hcK : c = 4 * N * K) :
    Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) * (N * (2 * Real.sqrt (2 * K))) =
      Real.sqrt (1 / c) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hs : Real.sqrt ((2 * N) ^ 2 * (2 * K)) = 2 * N * Real.sqrt (2 * K) := by
    rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by positivity)]
  rw [show (N : ℝ) * (2 * Real.sqrt (2 * K)) = Real.sqrt ((2 * N) ^ 2 * (2 * K)) by
    rw [hs]; ring, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [hcK]; push_cast; field_simp; ring

/-- The leading cusp coefficient: `√(1/2Nc²) g(c, N a) = (2K/ℓ) e(1/8) √(1/c)` for `c = 4NK`. -/
theorem cusp_value {N K c : ℕ} (hN : 0 < N) (hK : 0 < K) (hcK : c = 4 * N * K) {a : ℤ} {ℓ : ℕ}
    (hℓa : (ℓ : ℤ) ≡ a [ZMOD c]) (hcop : ℓ.Coprime c) (h8 : ℓ % 8 = 1) :
    (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) * gs c (N * a) =
      (jacobiSym (2 * (K : ℤ)) ℓ : ℂ) * cexp (2 * Real.pi * I / 8) *
        (Real.sqrt (1 / c) : ℂ) := by
  have hc' : c = N * (4 * K) := by rw [hcK]; ring
  have h4K : 0 < 4 * K := by omega
  have hcop2 : ℓ.Coprime (2 * K) :=
    Nat.Coprime.coprime_dvd_right ⟨2 * N, by rw [hcK]; ring⟩ hcop
  have hmod : a ≡ ℓ [ZMOD (4 * K : ℕ)] :=
    (Int.ModEq.of_dvd (by rw [hc']; exact ⟨N, by push_cast; ring⟩) hℓa).symm
  rw [hc', gs_scale hN h4K a, ← hc', gs_congr h4K hmod, gs_four_eval hK hcop2 h8]
  have hr := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_cusp hN hK hcK)
  push_cast at hr
  linear_combination (jacobiSym (2 * (K : ℤ)) ℓ : ℂ) * cexp (2 * Real.pi * I / 8) * hr

theorem jacobi_cusp {N K K' c ℓ : ℕ} (hcK : c = 4 * N * K) (hcK' : c = 24 * K')
    (h8 : ℓ % 8 = 1) (h4N : ℓ % (4 * N) = 1) (h3 : ℓ % 3 = 1) :
    jacobiSym (2 * (K : ℤ)) ℓ = jacobiSym (2 * (K' : ℤ)) ℓ := by
  have hodd : Odd ℓ := Nat.odd_iff.2 (by omega)
  have J2 : jacobiSym 2 ℓ = 1 := by
    rw [jacobiSym.mod_right 2 hodd]
    norm_num [h8, jacobiSym.one_right]
  have JN : jacobiSym N ℓ = 1 := by
    rw [jacobiSym.mod_right _ hodd, Int.natAbs_natCast, h4N, jacobiSym.one_right]
  have J3 : jacobiSym 3 ℓ = 1 := by
    rw [jacobiSym.mod_right 3 hodd]
    norm_num
    rw [show ℓ % 12 = 1 by omega, jacobiSym.one_right]
  have hcz : (2 * (N : ℤ)) * (2 * K) = 12 * (2 * K') := by
    have := congrArg (Nat.cast : ℕ → ℤ) (hcK.symm.trans hcK'); push_cast at this; linarith
  calc jacobiSym (2 * (K : ℤ)) ℓ = jacobiSym (2 * (N : ℤ)) ℓ * jacobiSym (2 * (K : ℤ)) ℓ := by
        rw [show jacobiSym (2 * (N : ℤ)) ℓ = 1 by rw [jacobiSym.mul_left, J2, JN]; ring,
          one_mul]
    _ = jacobiSym (12 * (2 * (K' : ℤ))) ℓ := by rw [← jacobiSym.mul_left, hcz]
    _ = jacobiSym (2 * (K' : ℤ)) ℓ := by
        rw [jacobiSym.mul_left, show (12 : ℤ) = 2 * 2 * 3 by norm_num, jacobiSym.mul_left,
          jacobiSym.mul_left, J2, J3]; ring

/-! ## Limits at `i∞` -/

theorem norm_exp_two_pi_I_div (q : ℤ) (r : ℕ) :
    ‖cexp (2 * Real.pi * I * (q : ℂ) / (r : ℂ))‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * I * (q : ℂ) / (r : ℂ) = ((2 * Real.pi * q / r : ℝ) : ℂ) * I by
    push_cast; ring, norm_exp_ofReal_mul_I]

theorem norm_Kc_le (N : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (c : ℕ) (j : ℤ) :
    ‖Kc N γ c j‖ ≤ c := by
  rw [Kc, norm_mul, show (4 * (N : ℂ) * c) = ((4 * N * c : ℕ) : ℂ) by push_cast; ring,
    norm_exp_two_pi_I_div, mul_one]
  calc _ ≤ ∑ x : Fin c, ‖cexp (2 * Real.pi * I *
        (((N : ℤ) * γ 0 0 * ((x : ℕ) : ℤ) ^ 2 + j * ((x : ℕ) : ℤ) : ℤ) : ℂ) / c)‖ :=
        norm_sum_le _ _
    _ = ∑ x : Fin c, (1 : ℝ) := Finset.sum_congr rfl fun x _ => norm_exp_two_pi_I_div _ _
    _ = c := by simp

theorem tendsto_P {N : ℕ} (hN : 0 < N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (c : ℕ) :
    Tendsto (fun t : ℝ => ∑' j : ℤ, Kc N γ c j *
      cexp (2 * Real.pi * I * (I * t) * (j : ℂ) ^ 2 / (4 * N))) atTop (𝓝 (Kc N γ c 0)) := by
  have hα : 0 < Real.pi / (2 * N) := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 hN
    positivity
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine (tendsto_tsum_gauss (Kc N γ c) (norm_Kc_le N γ c) hα).congr fun t => ?_
  refine tsum_congr fun j => ?_
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem weilTheta_zero_eq {N : ℕ} (hN : 0 < N) (τ : ℂ) :
    weilTheta N 0 τ = rankOneTheta 0 1 N τ := by
  have := rankOneTheta_eq_weilTheta 0 (r := 1) (t := N) one_pos hN τ
  simpa using this.symm

theorem Kc_zero (N : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (c : ℕ) :
    Kc N γ c 0 = gs c (N * γ 0 0) := by
  simp [Kc, gs, E]

/-! ## The kernel law -/

theorem nat_mod_of_modEq {ℓ n : ℕ} (hn : 1 < n) (h : (ℓ : ℤ) ≡ 1 [ZMOD n]) : ℓ % n = 1 := by
  have h' : ℓ ≡ 1 [MOD n] := Int.natCast_modEq_iff.1 (by exact_mod_cast h)
  rw [h', Nat.mod_eq_of_lt hn]

theorem SL_neg_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    (-γ) i j = -(γ i j) := by
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem mobius_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) :
    mobius (-γ) τ = mobius γ τ := by
  simp only [mobius, SL_neg_apply]
  push_cast
  rw [show -(γ 0 0 : ℂ) * τ + -(γ 0 1 : ℂ) = -((γ 0 0 : ℂ) * τ + γ 0 1) by ring,
    show -(γ 1 0 : ℂ) * τ + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * τ + γ 1 1) by ring, neg_div_neg_eq]

/-- `g(c, −a) = conj g(c, a)`. -/
theorem gs_neg (c : ℕ) (a : ℤ) : gs c (-a) = starRingEnd ℂ (gs c a) := by
  simp only [gs, E, map_sum, ← Complex.exp_conj]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast,
    map_natCast]
  push_cast
  ring

/-- **The cusp limit.** If `γ ∈ Γ(M)` has the Weil word `A`, and `δ` has the same Möbius action
as `γ` with lower-left entry `c > 0`, then comparing the leading cusp coefficients of
`θ_N(γτ) θ_6(τ) = A₀₀ θ_N(τ) θ_6(γτ)` as `τ = it → i∞` gives
`√(1/2Nc²) g(c, N δ₀₀) = A₀₀ √(1/12c²) g(c, 6 δ₀₀)`. -/
theorem cusp_limit {N M : ℕ} (hN : 0 < N) (h4N : 4 * N ∣ M) (h24 : 24 ∣ M)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (h00 : γ 0 0 ≡ 1 [ZMOD M])
    (h01 : γ 0 1 ≡ 0 [ZMOD M]) (h10 : γ 1 0 ≡ 0 [ZMOD M])
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (hA : WeilWord N γ A)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hδ : ∀ τ, mobius δ τ = mobius γ τ)
    {c : ℕ} (hc : 0 < c) (hcδ : δ 1 0 = c) :
    (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) * gs c (N * δ 0 0) =
      A (fz hN) (fz hN) * (Real.sqrt (1 / (2 * ((6 : ℕ) : ℝ) * (c : ℝ) ^ 2)) : ℂ) *
        gs c (((6 : ℕ) : ℤ) * δ 0 0) := by
  -- the anchor `N = 6`
  obtain ⟨B, hB⟩ := exists_weilWord 6 γ
  have hB1 := six_entry hB (dvd_of_modEq_zero (show 4 * 6 ∣ M from h24) h01)
    (dvd_of_modEq_zero (show 4 * 6 ∣ M from h24) h10)
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 ((by norm_num : 12 ∣ 24).trans h24)) h00)
  -- the cross relation `θ_N(γτ) θ_6(τ) = A₀₀ θ_N(τ) θ_6(γτ)`
  have hcross : ∀ τ : ℂ, 0 < τ.im →
      rankOneTheta 0 1 N (mobius γ τ) * rankOneTheta 0 1 ((6 : ℕ) : ℝ) τ =
      A (fz hN) (fz hN) * rankOneTheta 0 1 N τ * rankOneTheta 0 1 ((6 : ℕ) : ℝ) (mobius γ τ) := by
    intro τ hτ
    have e1 := weilVec_zero_mobius hN hA (dvd_of_modEq_zero h4N h01)
      (dvd_of_modEq_zero h4N h10) hτ
    have e2 := weilVec_zero_mobius (by norm_num) hB (dvd_of_modEq_zero (show 4 * 6 ∣ M from h24)
      h01) (dvd_of_modEq_zero (show 4 * 6 ∣ M from h24) h10) hτ
    rw [hB1, one_mul] at e2
    simp only [weilVec, weilTheta_zero_eq hN, weilTheta_zero_eq (show 0 < 6 by norm_num)]
      at e1 e2
    have hη := ModularForm.eta_ne_zero hτ
    have hη' := ModularForm.eta_ne_zero (im_mobius_pos γ hτ)
    have e1' : rankOneTheta 0 1 N (mobius γ τ) * ModularForm.eta τ =
        A (fz hN) (fz hN) * rankOneTheta 0 1 N τ * ModularForm.eta (mobius γ τ) := by
      rw [div_eq_iff hη'] at e1; rw [e1]; field_simp
    have e2' : rankOneTheta 0 1 ((6 : ℕ) : ℝ) (mobius γ τ) * ModularForm.eta τ =
        rankOneTheta 0 1 ((6 : ℕ) : ℝ) τ * ModularForm.eta (mobius γ τ) := by
      rw [div_eq_iff hη'] at e2; rw [e2]; field_simp
    apply mul_right_cancel₀ hη
    linear_combination rankOneTheta 0 1 ((6 : ℕ) : ℝ) τ * e1' -
      A (fz hN) (fz hN) * rankOneTheta 0 1 N τ * e2'
  -- substitute the cusp expansion (of `δ`) on `τ = it`
  set kN : ℂ := (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) with hkN
  set k6 : ℂ := (Real.sqrt (1 / (2 * ((6 : ℕ) : ℝ) * (c : ℝ) ^ 2)) : ℂ) with hk6
  have hEq : ∀ t : ℝ, 0 < t →
      kN * (∑' j : ℤ, Kc N δ c j * cexp (2 * Real.pi * I * (I * t) * (j : ℂ) ^ 2 / (4 * N))) *
        rankOneTheta 0 1 ((6 : ℕ) : ℝ) (I * t) =
      A (fz hN) (fz hN) * k6 * rankOneTheta 0 1 N (I * t) *
        (∑' j : ℤ, Kc 6 δ c j *
          cexp (2 * Real.pi * I * (I * t) * (j : ℂ) ^ 2 / (4 * ((6 : ℕ) : ℂ)))) := by
    intro t ht
    have hτ : 0 < (I * t).im := by simpa using ht
    have h := hcross _ hτ
    rw [← hδ, theta_mobius hN δ hc hcδ hτ, theta_mobius (show 0 < 6 by norm_num) δ hc hcδ hτ] at h
    have hσ := sig_im_pos δ hc hcδ hτ
    have hz : -I * sig δ (I * t) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.2 I_ne_zero) fun h0 => by rw [h0] at hσ; simp at hσ
    have hsplit : ∀ n : ℕ, 0 < n →
        (-I * (sig δ (I * t) / (2 * ((n : ℝ) : ℂ) * ((c : ℤ) : ℂ) ^ 2))) ^ (1 / 2 : ℂ) =
          (-I * sig δ (I * t)) ^ (1 / 2 : ℂ) * (Real.sqrt (1 / (2 * n * (c : ℝ) ^ 2)) : ℂ) := by
      intro n hn
      have hpos : (0 : ℝ) < 1 / (2 * n * (c : ℝ) ^ 2) := by
        have : (0 : ℝ) < n := Nat.cast_pos.2 hn
        have : (0 : ℝ) < c := Nat.cast_pos.2 hc
        positivity
      rw [← cpow_half_mul_ofReal hz hpos]
      congr 1
      have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
      push_cast
      field_simp
    rw [hsplit N hN, hsplit 6 (by norm_num)] at h
    have hzne : (-I * sig δ (I * t)) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    apply mul_left_cancel₀ hzne
    linear_combination h
  -- pass to the limit `t → ∞`
  have hθN : Tendsto (fun t : ℝ => rankOneTheta 0 1 N (I * t)) atTop (𝓝 1) :=
    (tendsto_weilTheta_zero hN).congr fun t => weilTheta_zero_eq hN _
  have hθ6 : Tendsto (fun t : ℝ => rankOneTheta 0 1 ((6 : ℕ) : ℝ) (I * t)) atTop (𝓝 1) :=
    (tendsto_weilTheta_zero (show 0 < 6 by norm_num)).congr fun t =>
      weilTheta_zero_eq (show 0 < 6 by norm_num) _
  have hL := ((tendsto_P hN δ c).const_mul kN).mul hθ6
  have hR := (((tendsto_P (show 0 < 6 by norm_num) δ c).const_mul
    (A (fz hN) (fz hN) * k6)).mul hθN)
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hEq t ht]; ring))
  rw [Kc_zero, Kc_zero, mul_one, mul_one] at hlim
  exact hlim

/-- **The two Gauss sums at the cusp agree** (Gauss's sign theorem + the Jacobi law):
for `a ≡ 1 (mod M)` prime to `c > 0` with `M ∣ c`,
`√(1/2Nc²) g(c, N a) = √(1/12c²) g(c, 6 a) ≠ 0`. -/
theorem cusp_ratio {N M : ℕ} (hN : 0 < N) (h4N : 4 * N ∣ M) (h24 : 24 ∣ M) {a : ℤ}
    (h00 : a ≡ 1 [ZMOD M]) {c : ℕ} (hc : 0 < c) (hMc : M ∣ c) (hac : IsCoprime a (c : ℤ)) :
    (Real.sqrt (1 / (2 * ((6 : ℕ) : ℝ) * (c : ℝ) ^ 2)) : ℂ) * gs c (((6 : ℕ) : ℤ) * a) =
      (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) * gs c (N * a) ∧
    (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) * gs c (N * a) ≠ 0 := by
  obtain ⟨K, hK⟩ := h4N.trans hMc
  obtain ⟨K', hK'⟩ := h24.trans hMc
  have hKpos : 0 < K := Nat.pos_of_ne_zero fun h => by rw [h] at hK; omega
  have hK'pos : 0 < K' := Nat.pos_of_ne_zero fun h => by rw [h] at hK'; omega
  -- the residue `ℓ ≡ a (mod c)`
  set ℓ : ℕ := (a % (c : ℤ)).toNat with hℓdef
  have hℓ : (ℓ : ℤ) = a % c := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hℓa : (ℓ : ℤ) ≡ a [ZMOD c] := by rw [hℓ]; exact Int.mod_modEq _ _
  have hℓ1 : (ℓ : ℤ) ≡ 1 [ZMOD M] :=
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hMc) hℓa).trans h00
  have hmodM : ∀ n : ℕ, 1 < n → n ∣ M → ℓ % n = 1 := fun n hn hnM =>
    nat_mod_of_modEq hn (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hnM) hℓ1)
  have h8 : ℓ % 8 = 1 := hmodM 8 (by norm_num) ((by norm_num : 8 ∣ 24).trans h24)
  have h3 : ℓ % 3 = 1 := hmodM 3 (by norm_num) ((by norm_num : 3 ∣ 24).trans h24)
  have h4N' : ℓ % (4 * N) = 1 := hmodM (4 * N) (by omega) h4N
  have hcop : ℓ.Coprime c := by
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 hℓa
    have h2 := hac.add_mul_left_left (-k)
    rw [show a + (c : ℤ) * (-k) = ℓ by linear_combination hk] at h2
    exact Nat.isCoprime_iff_coprime.1 h2
  have vN := cusp_value hN hKpos hK hℓa hcop h8
  have v6 := cusp_value (N := 6) (show 0 < 6 by norm_num) hK'pos (by rw [hK']) hℓa hcop h8
  rw [jacobi_cusp hK hK' h8 h4N' h3] at vN
  have hne : (jacobiSym (2 * (K' : ℤ)) ℓ : ℂ) * cexp (2 * Real.pi * I / 8) *
      (Real.sqrt (1 / c) : ℂ) ≠ 0 := by
    have hg : (2 * (K' : ℤ)).gcd ℓ = 1 := by
      have : Nat.Coprime (2 * K') ℓ :=
        Nat.Coprime.coprime_dvd_left ⟨12, by rw [hK']; ring⟩ hcop.symm
      rw [show (2 * (K' : ℤ)) = ((2 * K' : ℕ) : ℤ) by push_cast; ring, Int.gcd_natCast_natCast]
      exact this
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) ?_
    · rcases jacobiSym.eq_one_or_neg_one hg with h | h <;> rw [h] <;> norm_num
    · have : (0 : ℝ) < c := Nat.cast_pos.2 hc
      exact ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  exact ⟨by rw [vN, v6], by rw [vN]; exact hne⟩

/-- **The kernel law for `c ≠ 0`**, via a sign `δ = ±γ` with positive lower-left entry. -/
theorem kernel_of_cusp {N M : ℕ} (hN : 0 < N) (h4N : 4 * N ∣ M) (h24 : 24 ∣ M)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (h00 : γ 0 0 ≡ 1 [ZMOD M])
    (h01 : γ 0 1 ≡ 0 [ZMOD M]) (h10 : γ 1 0 ≡ 0 [ZMOD M])
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (hA : WeilWord N γ A)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hδ : ∀ τ, mobius δ τ = mobius γ τ)
    {c : ℕ} (hc : 0 < c) (hcδ : δ 1 0 = c) (hcγ : γ 1 0 = c ∨ γ 1 0 = -c)
    (hδ00 : δ 0 0 = γ 0 0 ∨ δ 0 0 = -γ 0 0) :
    A (fz hN) (fz hN) = 1 := by
  have hlim := cusp_limit hN h4N h24 h00 h01 h10 hA hδ hc hcδ
  have hMc : M ∣ c := by
    have := Int.modEq_zero_iff_dvd.1 h10
    rcases hcγ with h | h <;> rw [h] at this
    · exact_mod_cast this
    · exact_mod_cast (dvd_neg.1 this)
  have hac : IsCoprime (γ 0 0) (c : ℤ) := by
    have hdet := det_SL γ
    rcases hcγ with h | h
    · exact ⟨γ 1 1, -(γ 0 1), by rw [← h]; linear_combination hdet⟩
    · exact ⟨γ 1 1, γ 0 1, by rw [show (c : ℤ) = -γ 1 0 by rw [h]; ring]; linear_combination hdet⟩
  obtain ⟨hr, hne⟩ := cusp_ratio hN h4N h24 h00 hc hMc hac
  set kN : ℂ := (Real.sqrt (1 / (2 * N * (c : ℝ) ^ 2)) : ℂ) with hkN
  set k6 : ℂ := (Real.sqrt (1 / (2 * ((6 : ℕ) : ℝ) * (c : ℝ) ^ 2)) : ℂ) with hk6
  -- in both signs: `kN g(N δ₀₀) = k6 g(6 δ₀₀) ≠ 0`
  have key : k6 * gs c (((6 : ℕ) : ℤ) * δ 0 0) = kN * gs c (N * δ 0 0) ∧
      kN * gs c (N * δ 0 0) ≠ 0 := by
    rcases hδ00 with h | h
    · rw [h]; exact ⟨hr, hne⟩
    · have ckN : starRingEnd ℂ kN = kN := Complex.conj_ofReal _
      have ck6 : starRingEnd ℂ k6 = k6 := Complex.conj_ofReal _
      rw [h, mul_neg, mul_neg, gs_neg, gs_neg]
      refine ⟨?_, ?_⟩
      · have := congrArg (starRingEnd ℂ) hr
        rw [map_mul, map_mul, ckN, ck6] at this
        exact this
      · intro h0
        apply hne
        have := congrArg (starRingEnd ℂ) h0
        rw [map_mul, ckN, Complex.conj_conj, map_zero] at this
        exact this
  obtain ⟨hk6', hne'⟩ := key
  have : (A (fz hN) (fz hN) - 1) * (kN * gs c (N * δ 0 0)) = 0 := by
    linear_combination -hlim - A (fz hN) (fz hN) * hk6'
  rcases mul_eq_zero.1 this with h | h
  · linear_combination h
  · exact absurd h hne'

/-- `F₀(τ + 24k) = F₀(τ)`. -/
theorem weilVec_zero_add_24 {N : ℕ} (hN : 0 < N) (τ : ℂ) (k : ℤ) :
    weilVec N 0 (τ + 24 * k) = weilVec N 0 τ := by
  have hph : weilPhase N 0 ^ 24 = 1 := by
    rw [weilPhase, ← Complex.exp_add, ← Complex.exp_nat_mul]
    convert Complex.exp_int_mul_two_pi_mul_I (-1) using 2
    push_cast; ring
  have hstep : ∀ (n : ℕ) (σ : ℂ), weilVec N 0 (σ + n) = weilPhase N 0 ^ n * weilVec N 0 σ := by
    intro n σ
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, weilVec_T hN, ih, pow_succ]; ring
  have hnat : ∀ (n : ℕ) (σ : ℂ), weilVec N 0 (σ + 24 * n) = weilVec N 0 σ := by
    intro n σ
    rw [show (24 : ℂ) * n = ((24 * n : ℕ) : ℂ) by push_cast; ring, hstep, pow_mul, hph, one_pow,
      one_mul]
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · exact_mod_cast hnat n τ
  · have := hnat n (τ - 24 * n)
    rw [sub_add_cancel] at this
    push_cast
    rw [show τ + 24 * -(n : ℂ) = τ - 24 * n by ring]
    exact this.symm

/-- **The kernel law for `c = 0`**: then `γ = T^b` with `24 ∣ b`. -/
theorem kernel_zero {N M : ℕ} (hN : 0 < N) (h4N : 4 * N ∣ M) (h24 : 24 ∣ M)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (h00 : γ 0 0 ≡ 1 [ZMOD M])
    (h01 : γ 0 1 ≡ 0 [ZMOD M]) (h10 : γ 1 0 = 0)
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (hA : WeilWord N γ A) :
    A (fz hN) (fz hN) = 1 := by
  have hdet := det_SL γ
  rw [h10, mul_zero, sub_zero] at hdet
  have h24' : (24 : ℤ) ∣ M := by exact_mod_cast h24
  have ha : γ 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · exfalso
      rw [h] at h00
      have := (Int.ModEq.of_dvd h24' h00)
      simp [Int.ModEq] at this
  have hd : γ 1 1 = 1 := by rw [ha, one_mul] at hdet; exact hdet
  obtain ⟨k, hk⟩ := (h24'.trans (Int.modEq_zero_iff_dvd.1 h01))
  refine entry_eq_one_of_inv hN hA (dvd_of_modEq_zero h4N h01) (by rw [h10]; simp)
    fun τ _ => ?_
  have : mobius γ τ = τ + 24 * k := by
    simp only [mobius, ha, hd, h10, hk]; push_cast; ring
  rw [this, weilVec_zero_add_24 hN]

/-- **The kernel law (G5)**: `Γ(M)` acts trivially on `Θ_{N,0}/η` — every Weil word of
`γ ∈ Γ(M)` (`4N ∣ M`, `24 ∣ M`) has `A₀₀ = 1`. -/
theorem weilKernelLaw : WeilKernelLaw := by
  intro N M hN h4N h24 γ h00 _ h01 h10 A hA
  rcases lt_trichotomy (γ 1 0) 0 with hneg | hzero | hpos
  · obtain ⟨c, hc⟩ : ∃ c : ℕ, -γ 1 0 = c := ⟨(-γ 1 0).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    refine kernel_of_cusp hN h4N h24 h00 h01 h10 hA (δ := -γ) (mobius_neg γ) (c := c)
      (by omega) (by rw [SL_neg_apply, hc]) (Or.inr (by omega)) (Or.inr (SL_neg_apply _ _ _))
  · exact kernel_zero hN h4N h24 h00 h01 hzero hA
  · obtain ⟨c, hc⟩ : ∃ c : ℕ, γ 1 0 = c := ⟨(γ 1 0).toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
    exact kernel_of_cusp hN h4N h24 h00 h01 h10 hA (fun _ => rfl) (by omega) hc (Or.inl hc)
      (Or.inl rfl)

/-- The Weil Galois law, unconditionally. -/
theorem weilGaloisLaw : WeilGaloisLaw := weilGaloisLaw_of_weilKernelLaw weilKernelLaw

/-- The theta Galois law (GR Prop. 3.8), unconditionally. -/
theorem thetaGaloisLaw : ThetaGaloisLaw := thetaGaloisLaw_of_weilKernelLaw weilKernelLaw

end WeilGalois

end VOA.Classification.COne

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SerreDerivative
import VOA.Modularity.EisensteinBridge
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The analytic Eisenstein family `G_{2j}` of Zhu's recursion

`Modularity.ZhuNormalization` pins the **formal** coefficient family `zhuG j : ℕ → ℂ`,
`zhuG j 0 = −B_{2j}/(2j)!` and `zhuG j m = (2/(2j−1)!)·σ_{2j−1}(m)`.  This file evaluates it:

  `zhuGC j z := Σ_{n ≥ 0} zhuG j n · qⁿ`,   `q = e^{2πiz}`,

and identifies the result with Mathlib's Eisenstein series, in the plain `ℂ` variable of
`Modularity.QEvalHolomorphic`/`Modularity.SerreDerivative`:

* `zhuGC_eq_mul_E` — for `j ≥ 2`, `zhuGC j = (−B_{2j}/(2j)!)·E_{2j}` with `E_{2j}`
  **Mathlib's normalised modular form** `ModularForm.E`.  Hence
* `slashC_zhuGC` — `zhuGC j ∣[2j] γ = zhuGC j` for **every** `γ ∈ SL₂(ℤ)`, `j ≥ 2`:
  the higher Zhu coefficients are genuinely modular of weight `2j`.
* `zhuGC_one` — the anomalous weight: `zhuGC 1 = (2πi)⁻²·G₂`, so the `j = 1` term of Zhu's
  recursion is *exactly* the `G₂`-term of the Serre derivative `serreDerivC`
  (`Modularity.SerreDerivative`).  This is what makes the whole `S`-law work.

A by-product proved here rather than carried: `bernoulli_two_mul_ne_zero`
(`B_{2j} ≠ 0` for `j ≥ 1`), which `Modularity.ZhuNormalization` had to carry as a hypothesis —
it follows from `riemannZeta_two_mul_nat` together with `riemannZeta_ne_zero_of_one_lt_re`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma

/-! ## `B_{2j} ≠ 0` -/

/-- **`B_{2j} ≠ 0` for `j ≥ 1`** — the hypothesis `Modularity.ZhuNormalization` had to carry.
From `ζ(2j) = (−1)^{j+1}2^{2j−1}π^{2j}B_{2j}/(2j)!` and `ζ(s) ≠ 0` for `Re s > 1`. -/
theorem bernoulli_two_mul_ne_zero {j : ℕ} (hj : j ≠ 0) :
    ((bernoulli (2 * j) : ℚ) : ℂ) ≠ 0 := by
  intro h0
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  have hne : riemannZeta (2 * (j : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    have hre : (2 * (j : ℂ)).re = 2 * (j : ℝ) := by simp
    rw [hre]; linarith
  exact hne (by rw [riemannZeta_two_mul_nat hj, h0]; ring)

/-! ## `q` in the plain `ℂ` variable -/

/-- `q = e^{2πiz}` as a function of `z : ℂ`. -/
noncomputable def qC (z : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)

theorem qexp_eq_qC_pow (n : ℕ) (z : ℂ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) = qC z ^ n := by
  rw [qC, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem norm_qC (z : ℂ) : ‖qC z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [qC, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_qC_lt_one {z : ℂ} (hz : z ∈ imGT 0) : ‖qC z‖ < 1 := by
  have hz0 : (0 : ℝ) < z.im := hz
  rw [norm_qC, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

theorem qC_coe (τ : UpperHalfPlane) : qC (τ : ℂ) = qParam τ := rfl

/-! ## The analytic Eisenstein function -/

/-- **Zhu's Eisenstein function** `G_{2j}(z) = Σ_{n ≥ 0} zhuG j n · qⁿ`, in the `ℂ` variable.
The `n = 0` term is the constant `zhuG j 0 = −B_{2j}/(2j)!`. -/
noncomputable def zhuGC (j : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, zhuG j n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)

/-- The coefficient bound `‖zhuG j n‖ ≤ ‖zhuG j 0‖ + C·n^{2j}`, valid for **all** `n`. -/
theorem norm_zhuG_le (j n : ℕ) :
    ‖zhuG j n‖ ≤ ‖zhuG j 0‖
      + ‖(2 : ℂ) / (Nat.factorial (2 * j - 1) : ℂ)‖ * (n : ℝ) ^ (2 * j - 1 + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : ((0 : ℕ) : ℝ) ^ (2 * j - 1 + 1) = 0 := by
      rw [Nat.cast_zero]; exact zero_pow (by omega)
    rw [this, mul_zero, add_zero]
  · rw [zhuG_of_ne_zero j hn, lambertCoeff_eq_sigma, norm_mul, Complex.norm_natCast]
    have hs : ((ArithmeticFunction.sigma (2 * j - 1) n : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 * j - 1 + 1) := by
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ (2 * j - 1) n
    have := mul_le_mul_of_nonneg_left hs (norm_nonneg ((2 : ℂ) / (Nat.factorial (2 * j - 1) : ℂ)))
    linarith [norm_nonneg (zhuG j 0)]

/-- The Eisenstein `q`-series converges absolutely on the upper half-plane. -/
theorem summable_norm_zhuG_qexp (j : ℕ) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable fun n : ℕ =>
      ‖zhuG j n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ := by
  set r : ℝ := ‖qC z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := norm_qC_lt_one hz
  set C : ℝ := ‖(2 : ℂ) / (Nat.factorial (2 * j - 1) : ℂ)‖ with hC
  have hgeo : Summable fun n : ℕ => ‖zhuG j 0‖ * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hpow : Summable fun n : ℕ => C * ((n : ℝ) ^ (2 * j - 1 + 1) * r ^ n) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (2 * j - 1 + 1)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.add hpow)
  rw [norm_mul, qexp_eq_qC_pow, norm_pow, ← hr]
  have hb := norm_zhuG_le j n
  have hpn : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  calc ‖zhuG j n‖ * r ^ n
      ≤ (‖zhuG j 0‖ + C * (n : ℝ) ^ (2 * j - 1 + 1)) * r ^ n :=
        mul_le_mul_of_nonneg_right hb hpn
    _ = ‖zhuG j 0‖ * r ^ n + C * ((n : ℝ) ^ (2 * j - 1 + 1) * r ^ n) := by ring

theorem summable_zhuG_qexp (j : ℕ) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable fun n : ℕ => zhuG j n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) :=
  Summable.of_norm (summable_norm_zhuG_qexp j hz)

/-- Split off the constant term: `G_{2j}(z) = zhuG j 0 + Σ_{n ≥ 1} zhuG j n qⁿ`. -/
theorem zhuGC_eq_head_add (j : ℕ) {z : ℂ} (hz : z ∈ imGT 0) :
    zhuGC j z = zhuG j 0 + ∑' n : ℕ+, zhuG j (n : ℕ) * qC z ^ (n : ℕ) := by
  have hkey := (summable_zhuG_qexp j hz).sum_add_tsum_nat_add 1
  rw [zhuGC, ← hkey, Finset.sum_range_one]
  congr 1
  · rw [Nat.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  · rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => zhuG j n * qC z ^ n)]
    exact tsum_congr (fun n => by rw [qexp_eq_qC_pow])

/-! ## Identification with Mathlib's Eisenstein series, `j ≥ 2` -/

/-- **`G_{2j} = (−B_{2j}/(2j)!)·E_{2j}`** for `j ≥ 2`: Zhu's normalisation is Mathlib's
normalised Eisenstein modular form `ModularForm.E`, rescaled by its constant term. -/
theorem zhuGC_eq_mul_E {j : ℕ} (hj : 2 ≤ j) {z : ℂ} (hz : z ∈ imGT 0) :
    zhuGC j z = zhuG j 0 * ModularForm.E (show 3 ≤ 2 * j by omega) (⟨z, hz⟩ : UpperHalfPlane) := by
  have hj0 : j ≠ 0 := by omega
  have hB : ((bernoulli (2 * j) : ℚ) : ℂ) ≠ 0 := bernoulli_two_mul_ne_zero hj0
  have hk2 : Even (2 * j) := ⟨j, by ring⟩
  have hE := EisensteinSeries.q_expansion_bernoulli (show 3 ≤ 2 * j by omega) hk2
    (⟨z, hz⟩ : UpperHalfPlane)
  have hqz : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((⟨z, hz⟩ : UpperHalfPlane) : ℂ))
      = qC z := rfl
  -- the Mathlib tail, in `qC`-form
  set T : ℂ := ∑' n : ℕ+, ((ArithmeticFunction.sigma (2 * j - 1) (n : ℕ) : ℕ) : ℂ) * qC z ^ (n : ℕ)
    with hT
  have hEz : ModularForm.E (show 3 ≤ 2 * j by omega) (⟨z, hz⟩ : UpperHalfPlane)
      = 1 - (2 * ((2 * j : ℕ) : ℂ) / ((bernoulli (2 * j) : ℚ) : ℂ)) * T := by
    rw [hE, hT]
    congr 2
  have hzhu : ∑' n : ℕ+, zhuG j (n : ℕ) * qC z ^ (n : ℕ)
      = (2 / (Nat.factorial (2 * j - 1) : ℂ)) * T := by
    rw [hT, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [zhuG_of_ne_zero j n.ne_zero, lambertCoeff_eq_sigma]
    ring
  rw [zhuGC_eq_head_add j hz, hEz, hzhu, zhuG_zero]
  have hfac : (Nat.factorial (2 * j - 1) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hstep : (Nat.factorial (2 * j) : ℂ)
      = (2 * (j : ℂ)) * (Nat.factorial (2 * j - 1) : ℂ) := factorial_two_mul_cast hj0
  have hfac2 : (Nat.factorial (2 * j) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hjc : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
  rw [hstep]
  push_cast
  field_simp
  ring

/-! ## Modularity of the higher Zhu coefficients -/

/-- **`G_{2j}` is a modular form of weight `2j` for `j ≥ 2`**, in the `ℂ`-picture slash
calculus of `Modularity.SerreDerivative`.  This — together with `zhuGC_one` below — is what makes
Zhu's block conditions `SL₂(ℤ)`-covariant. -/
theorem slashC_zhuGC {j : ℕ} (hj : 2 ≤ j) (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ imGT 0) :
    slashC (2 * j : ℤ) γ (zhuGC j) z = zhuGC j z := by
  have hk : 3 ≤ 2 * j := by omega
  have hmz : mobiusC γ z ∈ imGT 0 := mobiusC_mem_imGT γ hz
  have hpt : (⟨mobiusC γ z, hmz⟩ : UpperHalfPlane) = γ • (⟨z, hz⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext (mobiusC_coe γ ⟨z, hz⟩)
  have hslash : (ModularForm.E hk : UpperHalfPlane → ℂ) ∣[((2 * j : ℕ) : ℤ)] γ
      = (ModularForm.E hk : UpperHalfPlane → ℂ) := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn (ModularForm.E hk) _ ⟨γ, rfl⟩
  have h2 := congrFun hslash (⟨z, hz⟩ : UpperHalfPlane)
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply] at h2
  have hden : ((γ 1 0 : ℂ) * ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) + (γ 1 1 : ℂ)) = denomC γ z := rfl
  rw [hden] at h2
  have hw : ((2 * j : ℕ) : ℤ) = (2 * j : ℤ) := by push_cast; ring
  rw [slashC, zhuGC_eq_mul_E hj hmz, zhuGC_eq_mul_E hj hz, hpt, mul_assoc, ← hw, h2]

/-! ## The anomalous weight `j = 1` -/

/-- **`G₂ = (2πi)⁻²·G₂^{Mathlib}`.**  The `j = 1` coefficient family that Zhu's recursion
*forces* is precisely the `G₂`-term of the Serre derivative `serreDerivC`; the normalisation
`(2πi)⁻²` is the one `Modularity.SerreDerivative` derived from cancellation. -/
theorem zhuGC_one {z : ℂ} (hz : z ∈ imGT 0) :
    zhuGC 1 z = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * G2C z := by
  have hbr := zhuG_one_eq_neg_E2_div_twelve (⟨z, hz⟩ : UpperHalfPlane)
  have hq : qParam (⟨z, hz⟩ : UpperHalfPlane) = qC z := rfl
  rw [hq] at hbr
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 = (-(4 * (Real.pi : ℂ) ^ 2))⁻¹ := by
    rw [inv_pow]
    congr 1
    rw [mul_pow, mul_pow, Complex.I_sq]
    ring
  have hE2 : EisensteinSeries.E2 (⟨z, hz⟩ : UpperHalfPlane)
      = (1 / (2 * riemannZeta 2)) * EisensteinSeries.G2 (⟨z, hz⟩ : UpperHalfPlane) := rfl
  rw [zhuGC_eq_head_add 1 hz, hbr, G2C_coe hz, hE2, riemannZeta_two, key]
  field_simp
  ring

end VOA

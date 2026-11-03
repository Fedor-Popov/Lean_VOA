/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BraidingSkewJacobi
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The translation rearrangement (pure analysis)

The skew-symmetry `𝒴₄(w₁, z₀)w₂ = e^{z₀L₋₁} 𝒴̃(w₂, e^{πi}z₀)w₁` turns an iterate
`⟨f, 𝒴₃(𝒴₄(w₁,z₀)w₂, z₂)w₃⟩` into a double series whose inner sums are negative binomial series:
`Σ_j C(N+j, j) (−z₀)ʲ z₂^{−N−j−1} = (z₂ + z₀)^{−N−1}` (`hasSum_inner`).  This file proves the
rearrangement abstractly (`tsum_skew_translate`): for any coefficient sequence `d` whose
iterate series is absolutely convergent at inner radius `x` and outer radius `y − x`,

`Σ_k (e^{−πi(ν−k+1)} Σ_{j≤k} C(a+k, j) d_{k−j}) y^{−(a+k)−1} x^{−(ν−k)−1}
   = Σ_p d_p (y+x)^{−(a+p)−1} (−x)^{−(ν−p)−1}`     (`0 < x`, `2x < y`, principal powers).

The double series is absolutely summable: `|C(a+p+j, j)| ≤ C(‖a‖+p+j, j)` and the real negative
binomial series reduce the `(p, j)`-sum to a constant multiple of the hypothesis series.

## Main results
* `bc`, `bc_eq_choose`, `hasSum_bc` (complex negative binomial series, from Mathlib's
  `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`), `hasSum_choose_real`.
* `neg_cpow_real` (`(−x)^s = x^s e^{πis}` for `x > 0`), `hasSum_inner`.
* `tsum_skew_translate`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.BraidingSkew

open scoped BigOperators

/-! ## Generalised binomial coefficients -/

/-- `C(n, j) = n(n−1)⋯(n−j+1)/j!` for complex `n`. -/
noncomputable def bc (n : ℂ) (j : ℕ) : ℂ := (∏ i ∈ Finset.range j, (n - i)) / (j.factorial : ℂ)

theorem bc_eq_choose (n : ℂ) (j : ℕ) : bc n j = Ring.choose n j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose n j
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    descPochhammer_map, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [bc, h]
  field_simp

theorem choose_real_eq (r : ℝ) (j : ℕ) :
    Ring.choose r j = (∏ i ∈ Finset.range j, (r - i)) / (j.factorial : ℝ) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose r j
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    descPochhammer_map, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [h]
  field_simp

/-- The complex negative binomial series `Σ_j C(b+j−1, j) tʲ = (1−t)^{−b}`, `‖t‖ < 1`. -/
theorem hasSum_bc (b : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun j : ℕ => bc (b + j - 1) j * t ^ j) (1 / (1 - t) ^ b) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero b).hasSum (y := t)
    (by simpa [enorm_eq_nnnorm] using ht)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  simpa [bc_eq_choose] using h

/-- The real negative binomial series. -/
theorem hasSum_choose_real (b : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    HasSum (fun j : ℕ => Ring.choose (b + j - 1) j * t ^ j) (1 / (1 - t) ^ b) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero b).hasSum (y := t)
    (by
      have : ‖t‖₊ < 1 := by
        rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht
      simpa [enorm_eq_nnnorm] using this)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  exact h

/-- `‖C(c + m, j)‖ ≤ C(‖c‖ + m, j)` for real `m ≥ j`-type shifts: here `m = p + j`. -/
theorem norm_bc_le (c : ℂ) (p j : ℕ) :
    ‖bc (c + p + j) j‖ ≤ Ring.choose (‖c‖ + p + j) j := by
  rw [choose_real_eq, bc, norm_div, Complex.norm_natCast, norm_prod]
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  refine div_le_div_of_nonneg_right ?_ hf.le
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hpos : (0 : ℝ) ≤ (p : ℝ) + j - i := by
    have : (i : ℝ) ≤ j := by exact_mod_cast hi.le
    linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  calc ‖c + p + j - i‖ = ‖c + (((p : ℝ) + j - i : ℝ) : ℂ)‖ := by push_cast; ring_nf
    _ ≤ ‖c‖ + ‖((((p : ℝ) + j - i : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ = ‖c‖ + p + j - i := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]; ring

/-! ## Powers of negative reals -/

theorem neg_cpow_real {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (-(x : ℂ)) ^ s = (x : ℂ) ^ s * Complex.exp (↑Real.pi * Complex.I * s) := by
  have hx' : (-(x : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hx.ne')
  rw [Complex.cpow_def_of_ne_zero hx', Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.exp_add]
  congr 1
  have : Complex.log (-(x : ℂ)) = Real.log x + Real.pi * Complex.I := by
    rw [Complex.log, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_neg (by linarith)]
  rw [this, Complex.ofReal_log hx.le]
  ring

theorem norm_neg_cpow_real {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖(-(x : ℂ)) ^ s‖ = x ^ s.re * Real.exp (-(Real.pi * s.im)) := by
  rw [neg_cpow_real hx, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

/-- `(−x)^s · (−x)ʲ = (−x)^{s+j}`. -/
theorem neg_cpow_add_nat {x : ℝ} (hx : 0 < x) (s : ℂ) (j : ℕ) :
    (-(x : ℂ)) ^ s * (-(x : ℂ)) ^ j = (-(x : ℂ)) ^ (s + j) := by
  have hx' : (-(x : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hx.ne')
  rw [Complex.cpow_add _ _ hx', Complex.cpow_natCast]

/-! ## The inner sum -/

/-- `Σ_j C(A+j, j) (−x)ʲ y^{−(A+j)−1} = (y+x)^{−A−1}` for `0 < x < y`. -/
theorem hasSum_inner (A : ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    HasSum (fun j : ℕ => bc (A + j) j * (-(x : ℂ)) ^ j * (y : ℂ) ^ (-(A + j) - 1))
      (((y + x : ℝ) : ℂ) ^ (-A - 1)) := by
  have hy : 0 < y := hx.trans hxy
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set t : ℂ := -(x : ℂ) / (y : ℂ) with ht
  have htn : ‖t‖ < 1 := by
    rw [ht, norm_div, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy, div_lt_one hy]
    exact hxy
  have h := (hasSum_bc (A + 1) htn).mul_left ((y : ℂ) ^ (-A - 1))
  have e1 : ∀ j : ℕ, (y : ℂ) ^ (-A - 1) * (bc (A + 1 + j - 1) j * t ^ j)
      = bc (A + j) j * (-(x : ℂ)) ^ j * (y : ℂ) ^ (-(A + j) - 1) := by
    intro j
    rw [show A + 1 + (j : ℂ) - 1 = A + j by ring, ht, div_pow,
      show -(A + (j : ℂ)) - 1 = (-A - 1) + (-(j : ℂ)) by ring, Complex.cpow_add _ _ hy',
      Complex.cpow_neg, Complex.cpow_natCast]
    field_simp
  have e2 : (y : ℂ) ^ (-A - 1) * (1 / (1 - t) ^ (A + 1)) = (((y + x : ℝ) : ℂ) ^ (-A - 1)) := by
    have h1t : (1 - t) = ((1 + x / y : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    have hpos : (0 : ℝ) ≤ 1 + x / y := by positivity
    rw [show y + x = y * (1 + x / y) by field_simp, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hy.le hpos, h1t, show -A - 1 = -(A + 1) by ring,
      Complex.cpow_neg, Complex.cpow_neg, one_div]
  rw [← e2]
  convert h using 1
  funext j
  exact (e1 j).symm

/-! ## The double series -/

/-- The `(p, j)` term: `d_p (−x)^{−(ν−p)−1} · C(a+p+j, j) (−x)ʲ y^{−(a+p+j)−1}`. -/
noncomputable def skewTerm (d : ℕ → ℂ) (a ν : ℂ) (x y : ℝ) (q : ℕ × ℕ) : ℂ :=
  d q.1 * (-(x : ℂ)) ^ (-(ν - q.1) - 1)
    * (bc (a + q.1 + q.2) q.2 * (-(x : ℂ)) ^ q.2 * (y : ℂ) ^ (-(a + q.1 + q.2) - 1))

theorem hasSum_skewTerm_fiber (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (p : ℕ) :
    HasSum (fun j => skewTerm d a ν x y (p, j))
      (d p * ((y + x : ℝ) : ℂ) ^ (-(a + p) - 1) * (-(x : ℂ)) ^ (-(ν - p) - 1)) := by
  have h := (hasSum_inner (a + p) hx hxy).mul_left (d p * (-(x : ℂ)) ^ (-(ν - p) - 1))
  convert h using 1
  ring

theorem re_aux (a : ℂ) (p : ℕ) : (-(a + (p : ℂ)) - 1).re = -a.re - p - 1 := by simp; ring

theorem re_aux' (ν : ℂ) (p : ℕ) : (-(ν - (p : ℂ)) - 1).re = -ν.re + p - 1 := by simp; ring

theorem im_aux' (ν : ℂ) (p : ℕ) : (-(ν - (p : ℂ)) - 1).im = -ν.im := by simp

/-- The real majorant. -/
noncomputable def skewMaj (d : ℕ → ℂ) (a ν : ℂ) (x y : ℝ) (q : ℕ × ℕ) : ℝ :=
  (‖d q.1‖ * (x ^ (-ν.re + q.1 - 1) * Real.exp (Real.pi * ν.im)) * y ^ (-a.re - q.1 - 1))
    * (Ring.choose (‖a‖ + q.1 + q.2) q.2 * (x / y) ^ q.2)

theorem norm_skewTerm_le (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (q : ℕ × ℕ) : ‖skewTerm d a ν x y q‖ ≤ skewMaj d a ν x y q := by
  obtain ⟨p, j⟩ := q
  simp only [skewTerm, skewMaj]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg_cpow_real hx, re_aux', im_aux',
    norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hy,
    show (-(a + (p : ℂ) + (j : ℂ)) - 1).re = (-a.re - p - 1) - j by simp; ring,
    Real.rpow_sub hy, Real.rpow_natCast, div_pow, mul_neg, neg_neg]
  have hb := norm_bc_le a p j
  have h0 : 0 ≤ ‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im)) := by positivity
  have hyj : 0 < y ^ j := pow_pos hy j
  have hY : 0 < y ^ (-a.re - p - 1) := Real.rpow_pos_of_pos hy _
  calc ‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im))
        * (‖bc (a + p + j) j‖ * x ^ j * (y ^ (-a.re - p - 1) / y ^ j))
      ≤ ‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im))
        * (Ring.choose (‖a‖ + p + j) j * x ^ j * (y ^ (-a.re - p - 1) / y ^ j)) := by
        gcongr
    _ = _ := by field_simp

theorem skewMaj_nonneg (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (q : ℕ × ℕ) : 0 ≤ skewMaj d a ν x y q :=
  (norm_nonneg _).trans (norm_skewTerm_le d a ν hx hy q)

theorem hasSum_skewMaj_fiber (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (p : ℕ) :
    HasSum (fun j => skewMaj d a ν x y (p, j))
      ((‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im)) * y ^ (-a.re - p - 1))
        * (1 / (1 - x / y) ^ (‖a‖ + p + 1))) := by
  have hy : 0 < y := hx.trans hxy
  have h := (hasSum_choose_real (‖a‖ + p + 1) (t := x / y) (by positivity)
    (by rw [div_lt_one hy]; exact hxy)).mul_left
      (‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im)) * y ^ (-a.re - p - 1))
  convert h using 2 with j
  simp only [skewMaj]
  rw [show ‖a‖ + (p : ℝ) + 1 + j - 1 = ‖a‖ + p + j by ring]

/-- The fibre sums of the majorant are a constant multiple of the hypothesis series. -/
theorem skewMaj_fiber_eq (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) (p : ℕ) :
    (‖d p‖ * (x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im)) * y ^ (-a.re - p - 1))
        * (1 / (1 - x / y) ^ (‖a‖ + p + 1))
      = (Real.exp (Real.pi * ν.im) * y ^ (‖a‖ - a.re) * (y - x) ^ (a.re - ‖a‖))
        * ‖d p * ((y - x : ℝ) : ℂ) ^ (-(a + p) - 1) * (x : ℂ) ^ (-(ν - p) - 1)‖ := by
  have hy : 0 < y := hx.trans hxy
  have hyx : 0 < y - x := by linarith
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyx,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, re_aux, re_aux',
    show 1 - x / y = (y - x) / y by field_simp, Real.div_rpow hyx.le hy.le]
  have e1 : y ^ (-a.re - p - 1) * y ^ (‖a‖ + p + 1) = y ^ (‖a‖ - a.re) := by
    rw [← Real.rpow_add hy]; ring_nf
  have e2 : (y - x) ^ (a.re - ‖a‖) * (y - x) ^ (-a.re - p - 1)
      = ((y - x) ^ (‖a‖ + p + 1))⁻¹ := by
    rw [← Real.rpow_add hyx, ← Real.rpow_neg hyx.le]; ring_nf
  rw [one_div_div, div_eq_mul_inv, ← e2]
  linear_combination (‖d p‖ * x ^ (-ν.re + p - 1) * Real.exp (Real.pi * ν.im)
      * ((y - x) ^ (a.re - ‖a‖) * (y - x) ^ (-a.re - p - 1))) * e1

/-- The double series is absolutely summable. -/
theorem summable_skewTerm (d : ℕ → ℂ) (a ν : ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hS : Summable fun p : ℕ => ‖d p * ((y - x : ℝ) : ℂ) ^ (-(a + p) - 1)
      * (x : ℂ) ^ (-(ν - p) - 1)‖) :
    Summable (skewTerm d a ν x y) := by
  have hy : 0 < y := hx.trans hxy
  have hM : Summable (skewMaj d a ν x y) := by
    rw [summable_prod_of_nonneg (fun q => skewMaj_nonneg d a ν hx hy q)]
    refine ⟨fun p => (hasSum_skewMaj_fiber d a ν hx hxy p).summable, ?_⟩
    refine (hS.mul_left (Real.exp (Real.pi * ν.im) * y ^ (‖a‖ - a.re)
      * (y - x) ^ (a.re - ‖a‖))).congr fun p => ?_
    rw [(hasSum_skewMaj_fiber d a ν hx hxy p).tsum_eq, skewMaj_fiber_eq d a ν hx hxy p]
  exact Summable.of_norm_bounded hM (fun q => norm_skewTerm_le d a ν hx hy q)

/-- The `k`-th antidiagonal sum is the `k`-th term of the skew-expanded iterate. -/
theorem sum_antidiagonal_skewTerm (d : ℕ → ℂ) (a ν : ℂ) {x : ℝ} (hx : 0 < x) (y : ℝ) (k : ℕ) :
    ∑ q ∈ Finset.antidiagonal k, skewTerm d a ν x y q
      = (omegaPhase (ν - k) * ∑ j ∈ Finset.range (k + 1), bc (a + k) j * d (k - j))
        * (y : ℂ) ^ (-(a + k) - 1) * (x : ℂ) ^ (-(ν - k) - 1) := by
  have h1 : ∑ q ∈ Finset.antidiagonal k, skewTerm d a ν x y q
      = ∑ q ∈ Finset.antidiagonal k, (fun j p => skewTerm d a ν x y (p, j)) q.1 q.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]; rfl
  rw [h1, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j p => skewTerm d a ν x y (p, j)) k]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  simp only [skewTerm]
  rw [Nat.cast_sub (by omega : j ≤ k), show a + ((k : ℂ) - j) + j = a + k by ring]
  have key : (-(x : ℂ)) ^ (-(ν - ((k : ℂ) - j)) - 1) * (-(x : ℂ)) ^ j
      = omegaPhase (ν - k) * (x : ℂ) ^ (-(ν - k) - 1) := by
    rw [neg_cpow_add_nat hx, show -(ν - ((k : ℂ) - j)) - 1 + j = -(ν - k) - 1 by ring,
      neg_cpow_real hx, omegaPhase, mul_comm]
    congr 1
    ring_nf
  linear_combination (d (k - j) * bc (a + k) j * (y : ℂ) ^ (-(a + k) - 1)) * key

/-- **The translation rearrangement.** -/
theorem tsum_skew_translate {d : ℕ → ℂ} {a ν : ℂ} {x y : ℝ} (hx : 0 < x) (hxy : 2 * x < y)
    (hS : Summable fun p : ℕ => ‖d p * ((y - x : ℝ) : ℂ) ^ (-(a + p) - 1)
      * (x : ℂ) ^ (-(ν - p) - 1)‖) :
    ∑' k : ℕ, (omegaPhase (ν - k) * ∑ j ∈ Finset.range (k + 1), bc (a + k) j * d (k - j))
        * (y : ℂ) ^ (-(a + k) - 1) * (x : ℂ) ^ (-(ν - k) - 1)
      = ∑' p : ℕ, d p * ((y + x : ℝ) : ℂ) ^ (-(a + p) - 1) * (-(x : ℂ)) ^ (-(ν - p) - 1) := by
  have hxy' : x < y := by linarith
  have hT := summable_skewTerm d a ν hx hxy' hS
  have hfib := hT.hasSum.prod_fiberwise (fun p => hasSum_skewTerm_fiber d a ν hx hxy' p)
  have hanti : HasSum (fun k => ∑ q ∈ Finset.antidiagonal k, skewTerm d a ν x y q)
      (∑' q, skewTerm d a ν x y q) := by
    have h := (Finset.sigmaAntidiagonalEquivProd.hasSum_iff
      (f := skewTerm d a ν x y)).mpr hT.hasSum
    refine h.sigma fun k => ?_
    have := hasSum_fintype (fun c : Finset.antidiagonal k => skewTerm d a ν x y c.1)
    rwa [Finset.sum_coe_sort] at this
  rw [hfib.tsum_eq, ← hanti.tsum_eq]
  exact tsum_congr fun k => (sum_antidiagonal_skewTerm d a ν hx y k).symm

end VOA.Huang.BraidingSkew

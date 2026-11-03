/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuBlockConditions
import VOA.Modularity.BuhlSpanningC2
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Holomorphy of `qEvalAt` — the repo's first complex-analysis layer

Everything upstream of this file is formal or algebraic; this is the first place where the
`q`-series of `Modularity.ConvergenceBridge` become **holomorphic functions of `τ`**.  It supplies
the pair that Zhu's `S`-law needs and that nothing in the repo had:

* `differentiableOn_qEvalC` — `z ↦ qEvalAt χ h z` is holomorphic on the upper half-plane,
  from the already-proved `Subexponential` growth datum (`Modularity.GrowthBound`);
* `deriv_qEvalC` — **term-by-term differentiation**:
  `deriv (qEvalC χ h) z = 2πi · qEvalC (qDeriv χ) h z`,
  with `qDeriv χ e = e · χ e` the *formal* derivative of `Modularity.ZhuBlockConditions`.  This is
  the bridge that lets Zhu's block condition (iii) — a statement about `qDeriv` — be read as a
  statement about `d/dτ`.

## Convention

We work with the **plain `ℂ` variable** on the open set `imGT 0 = {z : ℂ | 0 < z.im}` rather than
with `UpperHalfPlane` charts: the consumers (the Serre derivative, the slash action, the identity
theorem on a connected open set) all want `DifferentiableOn ℂ … {z | 0 < z.im}`.  `qEvalC χ h`
agrees with `qEvalAt χ h` under the coercion `ℍ → ℂ` (`qEvalC_coe`).

## Method

On the sub-half-plane `imGT c` (`c > 0`) one has `‖qⁿ‖ = e^{−2πn·Im z} ≤ rⁿ` with
`r = e^{−2πc} < 1`, uniformly.  Subexponentiality gives `‖χ(h+n)‖ ≤ C·sⁿ` for the specific
`s = (1 + r⁻¹)/2`, which satisfies `1 < s` **and** `s·r < 1`; so the termwise derivatives are
dominated by `C·2π·n·(sr)ⁿ`, summable by `summable_pow_mul_geometric_of_norm_lt_one`.  Mathlib's
`hasDerivAt_tsum_of_isPreconnected` then differentiates the series termwise on the (open, convex,
hence preconnected) half-plane.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex

/-! ## The open half-planes -/

/-- The open half-plane `Im z > c`. -/
def imGT (c : ℝ) : Set ℂ := {z : ℂ | c < z.im}

theorem isOpen_imGT (c : ℝ) : IsOpen (imGT c) :=
  isOpen_lt continuous_const Complex.continuous_im

theorem convex_imGT (c : ℝ) : Convex ℝ (imGT c) := by
  refine convex_halfSpace_gt ⟨fun x y => ?_, fun t x => ?_⟩ c
  · exact Complex.add_im x y
  · simp [Complex.smul_im]

theorem isPreconnected_imGT (c : ℝ) : IsPreconnected (imGT c) :=
  (convex_imGT c).isPreconnected

theorem mem_imGT_of_lt {c : ℝ} {z : ℂ} (h : c < z.im) : z ∈ imGT c := h

/-! ## The `q`-series in the `ℂ` variable -/

/-- The `n`-th term of the bare `q`-series, as a function of `z : ℂ`. -/
noncomputable def qTerm (χ : FormalQSeries) (h : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  χ (h + (n : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)

/-- Its derivative in `z`. -/
noncomputable def qTerm' (χ : FormalQSeries) (h : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  χ (h + (n : ℂ)) *
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) *
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))

/-- The bare `q`-series (no `q^h` prefactor). -/
noncomputable def qSeriesC (χ : FormalQSeries) (h : ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, qTerm χ h n z

/-- `qEvalAt` read in the plain `ℂ` variable. -/
noncomputable def qEvalC (χ : FormalQSeries) (h : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * h) * qSeriesC χ h z

theorem hasDerivAt_qTerm (χ : FormalQSeries) (h : ℂ) (n : ℕ) (z : ℂ) :
    HasDerivAt (qTerm χ h n) (qTerm' χ h n z) z := by
  have hlin : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * w)
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
  exact (hlin.cexp).const_mul (χ (h + (n : ℂ)))

/-- `‖q^n‖ = e^{−2πn·Im z}`. -/
theorem norm_qexp (n : ℕ) (z : ℂ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖
      = Real.exp (-(2 * Real.pi * n * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-! ## The domination bound -/

section Bound

variable (χ : FormalQSeries) (h : ℂ)

/-- The geometric ratio on `imGT c`. -/
noncomputable def qRatio (c : ℝ) : ℝ := Real.exp (-(2 * Real.pi * c))

theorem qRatio_pos (c : ℝ) : 0 < qRatio c := Real.exp_pos _

theorem qRatio_lt_one {c : ℝ} (hc : 0 < c) : qRatio c < 1 := by
  rw [qRatio, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

/-- On `imGT c` the `n`-th power of `q` is dominated by `(qRatio c)ⁿ`. -/
theorem norm_qexp_le {c : ℝ} {z : ℂ} (hz : z ∈ imGT c) (n : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ ≤ qRatio c ^ n := by
  rw [norm_qexp, qRatio, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hzc : c < z.im := hz
  have h0 : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ) := by positivity
  have hkey : 2 * Real.pi * (n : ℝ) * c ≤ 2 * Real.pi * (n : ℝ) * z.im :=
    mul_le_mul_of_nonneg_left hzc.le h0
  nlinarith [hkey]

end Bound

/-! ## Termwise differentiation -/

/-- The auxiliary exponent `s = (1 + r⁻¹)/2`, which is `> 1` and has `s·r < 1`. -/
noncomputable def qAux (r : ℝ) : ℝ := (1 + r⁻¹) / 2

theorem one_lt_qAux {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 1 < qAux r := by
  rw [qAux]
  have : 1 < r⁻¹ := one_lt_inv_iff₀.mpr ⟨hr0, hr1⟩
  linarith

theorem qAux_mul_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : qAux r * r < 1 := by
  rw [qAux]
  field_simp
  nlinarith

theorem qAux_mul_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < qAux r * r := by
  have := one_lt_qAux hr0 hr1
  nlinarith

/-- **Termwise differentiation of the `q`-series** on a half-plane `Im z > c`. -/
theorem hasDerivAt_qSeriesC (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ imGT c) :
    HasDerivAt (qSeriesC χ h) (∑' n : ℕ, qTerm' χ h n z) z := by
  classical
  set r : ℝ := qRatio c with hrdef
  have hr0 : 0 < r := qRatio_pos c
  have hr1 : r < 1 := qRatio_lt_one hc
  set s : ℝ := qAux r with hsdef
  have hs1 : 1 < s := one_lt_qAux hr0 hr1
  have hsr1 : s * r < 1 := qAux_mul_lt_one hr0 hr1
  have hsr0 : 0 < s * r := qAux_mul_pos hr0 hr1
  obtain ⟨C, hC⟩ := hsub s hs1
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  -- the dominating series
  set u : ℕ → ℝ := fun n => C * (2 * Real.pi) * ((n : ℝ) * (s * r) ^ n) with hudef
  have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (s * r) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_pos hsr0])
  have hu : Summable u := by
    refine (hgeom.mul_left (C * (2 * Real.pi))).congr (fun n => ?_)
    rw [hudef]
    simp
  -- the bound on the derivatives
  have hbound : ∀ (n : ℕ), ∀ w ∈ imGT c, ‖qTerm' χ h n w‖ ≤ u n := by
    intro n w hw
    rw [qTerm', norm_mul, norm_mul]
    have h1 : ‖χ (h + (n : ℂ))‖ ≤ C * s ^ n := hC n
    have h2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * w)‖ ≤ r ^ n :=
      norm_qexp_le hw n
    have h3 : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * n := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [Real.pi_nonneg, abs_of_nonneg Real.pi_pos.le]
    rw [h3, hudef]
    have hs0 : (0 : ℝ) ≤ s := by linarith
    have hpin : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
    have hb : (0 : ℝ) ≤ C * s ^ n := mul_nonneg hC0 (pow_nonneg hs0 n)
    calc ‖χ (h + (n : ℂ))‖ * (‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * w)‖
          * (2 * Real.pi * n))
        ≤ (C * s ^ n) * ((r ^ n) * (2 * Real.pi * n)) := by
          refine mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hpin) ?_ hb
          exact mul_nonneg (norm_nonneg _) hpin
      _ = C * (2 * Real.pi) * ((n : ℝ) * (s * r) ^ n) := by rw [mul_pow]; ring
  -- summability at a base point
  have hz0 : (Complex.I * ((c + 1 : ℝ) : ℂ)) ∈ imGT c := by
    show c < (Complex.I * ((c + 1 : ℝ) : ℂ)).im
    simp
  have hsum0 : Summable (fun n : ℕ => qTerm χ h n (Complex.I * ((c + 1 : ℝ) : ℂ))) := by
    refine Summable.of_norm ?_
    have hgeom0 : Summable (fun n : ℕ => C * (s * r) ^ n) :=
      (summable_geometric_of_lt_one hsr0.le hsr1).mul_left C
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom0
    rw [qTerm, norm_mul]
    have h1 : ‖χ (h + (n : ℂ))‖ ≤ C * s ^ n := hC n
    have h2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
        (Complex.I * ((c + 1 : ℝ) : ℂ)))‖ ≤ r ^ n := norm_qexp_le hz0 n
    calc ‖χ (h + (n : ℂ))‖ * _ ≤ (C * s ^ n) * (r ^ n) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * (s * r) ^ n := by rw [mul_pow]; ring
  exact hasDerivAt_tsum_of_isPreconnected hu (isOpen_imGT c) (isPreconnected_imGT c)
    (fun n w _ => hasDerivAt_qTerm χ h n w) hbound hz0 hsum0 hz


/-! ## Summability of the weighted series -/

/-- The `k`-weighted `q`-series is summable on `imGT c`. -/
theorem summable_pow_mul_qTerm (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ imGT c) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℂ) ^ k) * qTerm χ h n z) := by
  classical
  set r : ℝ := qRatio c with hrdef
  have hr0 : 0 < r := qRatio_pos c
  have hr1 : r < 1 := qRatio_lt_one hc
  set s : ℝ := qAux r with hsdef
  have hs1 : 1 < s := one_lt_qAux hr0 hr1
  have hsr1 : s * r < 1 := qAux_mul_lt_one hr0 hr1
  have hsr0 : 0 < s * r := qAux_mul_pos hr0 hr1
  obtain ⟨C, hC⟩ := hsub s hs1
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [pow_zero, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hs0 : (0 : ℝ) ≤ s := by linarith
  refine Summable.of_norm ?_
  have hgeom : Summable (fun n : ℕ => C * ((n : ℝ) ^ k * (s * r) ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one k
      (by rwa [Real.norm_eq_abs, abs_of_pos hsr0])).mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
  rw [norm_mul, qTerm, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 : ‖χ (h + (n : ℂ))‖ ≤ C * s ^ n := hC n
  have h2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ ≤ r ^ n :=
    norm_qexp_le hz n
  have hb : (0 : ℝ) ≤ C * s ^ n := mul_nonneg hC0 (pow_nonneg hs0 n)
  calc (n : ℝ) ^ k * (‖χ (h + (n : ℂ))‖
        * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖)
      ≤ (n : ℝ) ^ k * ((C * s ^ n) * (r ^ n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hb) ?_
        positivity
    _ = C * ((n : ℝ) ^ k * (s * r) ^ n) := by rw [mul_pow]; ring

/-! ## The derivative of `qEvalC` -/

/-- The `q`-series of the formal derivative `qDeriv χ` is `h·G + Σ n·(term)`. -/
theorem qSeriesC_qDeriv (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ imGT c) :
    qSeriesC (qDeriv χ) h z
      = h * qSeriesC χ h z + ∑' n : ℕ, (n : ℂ) * qTerm χ h n z := by
  have h0 := summable_pow_mul_qTerm χ h hsub hc hz 0
  have h1 := summable_pow_mul_qTerm χ h hsub hc hz 1
  have h0' : Summable (fun n : ℕ => qTerm χ h n z) := by
    refine h0.congr (fun n => ?_); simp
  have h1' : Summable (fun n : ℕ => (n : ℂ) * qTerm χ h n z) := by
    refine h1.congr (fun n => ?_); simp
  have hsplit : ∀ n : ℕ, qTerm (qDeriv χ) h n z
      = h * qTerm χ h n z + (n : ℂ) * qTerm χ h n z := by
    intro n
    rw [qTerm, qTerm, qDeriv]
    ring
  rw [qSeriesC, tsum_congr hsplit, (h0'.mul_left h).tsum_add h1', tsum_mul_left]
  rfl

/-- **Term-by-term differentiation of `qEvalC`.**
`d/dz qEvalC χ h z = 2πi · qEvalC (qDeriv χ) h z` — the bridge between the *formal* `qDeriv` of
Zhu's block condition (iii) and the honest derivative in `τ`. -/
theorem hasDerivAt_qEvalC (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ imGT c) :
    HasDerivAt (qEvalC χ h)
      (2 * (Real.pi : ℂ) * Complex.I * qEvalC (qDeriv χ) h z) z := by
  have hE : HasDerivAt (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w * h))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * h)
        * (2 * (Real.pi : ℂ) * Complex.I * h)) z := by
    have hlin : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * w * h)
        (2 * (Real.pi : ℂ) * Complex.I * h) z := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using
        ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).mul_const h
    exact hlin.cexp
  have hG := hasDerivAt_qSeriesC χ h hsub hc hz
  have hprod := hE.mul hG
  -- rewrite the derivative into the target shape
  have h1' : Summable (fun n : ℕ => (n : ℂ) * qTerm χ h n z) := by
    refine (summable_pow_mul_qTerm χ h hsub hc hz 1).congr (fun n => ?_); simp
  have hterm : (∑' n : ℕ, qTerm' χ h n z)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑' n : ℕ, (n : ℂ) * qTerm χ h n z := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [qTerm', qTerm]
    ring
  rw [hterm] at hprod
  have hgoal : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * h)
        * (2 * (Real.pi : ℂ) * Complex.I * h) * qSeriesC χ h z
      + Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * h)
        * (2 * (Real.pi : ℂ) * Complex.I * ∑' n : ℕ, (n : ℂ) * qTerm χ h n z)
      = 2 * (Real.pi : ℂ) * Complex.I * qEvalC (qDeriv χ) h z := by
    rw [qEvalC, qSeriesC_qDeriv χ h hsub hc hz]
    ring
  rw [hgoal] at hprod
  exact hprod

/-- **`qEvalC χ h` is holomorphic on the upper half-plane.** -/
theorem differentiableOn_qEvalC (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) :
    DifferentiableOn ℂ (qEvalC χ h) (imGT 0) := by
  intro z hz
  have hz0 : (0 : ℝ) < z.im := hz
  have hc : 0 < z.im / 2 := by linarith
  have hzc : z ∈ imGT (z.im / 2) := by
    show z.im / 2 < z.im; linarith
  exact ((hasDerivAt_qEvalC χ h hsub hc hzc).differentiableAt).differentiableWithinAt

/-- The derivative, in `deriv` form. -/
theorem deriv_qEvalC (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (qEvalC χ h) z = 2 * (Real.pi : ℂ) * Complex.I * qEvalC (qDeriv χ) h z := by
  have hz0 : (0 : ℝ) < z.im := hz
  have hc : 0 < z.im / 2 := by linarith
  have hzc : z ∈ imGT (z.im / 2) := by
    show z.im / 2 < z.im; linarith
  exact (hasDerivAt_qEvalC χ h hsub hc hzc).deriv

/-! ## Agreement with `qEvalAt` -/

/-- `qEvalC` is `qEvalAt` in the plain `ℂ` variable. -/
theorem qEvalC_coe (χ : FormalQSeries) (h : ℂ) (τ : UpperHalfPlane) :
    qEvalC χ h (τ : ℂ) = qEvalAt χ h τ := by
  rw [qEvalC, qEvalAt, qSeriesC]
  congr 1
  refine tsum_congr (fun n => ?_)
  rw [qTerm, qParam, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- The coercion of the upper half-plane lands in `imGT 0`. -/
theorem coe_mem_imGT_zero (τ : UpperHalfPlane) : (τ : ℂ) ∈ imGT 0 := τ.im_pos

/-! ## Sanity check: the characters are holomorphic -/

section Char

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The character of a module with the growth datum is holomorphic on `ℍ`.**  The hypothesis
is *verbatim* `Modularity.ConvergenceBridge.SubexponentialCoeffs`, which
`Modularity.BuhlSpanningC2` supplies from `C₂`-cofiniteness. -/
theorem differentiableOn_char (N : OrdVModule W M) (h : ℂ) (hsub : SubexponentialCoeffs N h) :
    DifferentiableOn ℂ (qEvalC (gradedDim N) h) (imGT 0) :=
  differentiableOn_qEvalC (gradedDim N) h hsub

/-- For a `C₂`-cofinite VOA the character of `𝒱` itself is holomorphic on `ℍ`,
**unconditionally** (the growth datum is `subexponentialCoeffs_adjoint_of_C2Cofinite`). -/
theorem differentiableOn_char_adjoint (W : VertexOperatorAlgebra 𝒱) (hne : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W) :
    DifferentiableOn ℂ
      (qEvalC (gradedDim (adjointModule W)) (0 - W.centralCharge / 24)) (imGT 0) :=
  differentiableOn_char (adjointModule W) _ (subexponentialCoeffs_adjoint_of_C2Cofinite W hne hC2)

end Char

end VOA

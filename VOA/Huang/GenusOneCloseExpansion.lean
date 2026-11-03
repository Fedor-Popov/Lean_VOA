import VOA.Modularity.QEvalShift
import VOA.Modularity.QEvalLinear
import VOA.Modularity.SubexpClosure
import VOA.Modularity.QConvModule
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Cusp expansions of quasi-periodic holomorphic functions of moderate growth

Two analytic facts used for genus-one cusp expansion (Miyamoto, math/0010180,
Theorem 4.9; Zhu, JAMS 9 (1996), §5):

* **uniqueness**: a `q`-series based at `b`, convergent on the upper half-plane,
  whose evaluation vanishes there, is zero;
* **existence**: a holomorphic function on the upper half-plane with
  `Φ(z+1) = e^{2πir} Φ(z)` and at most exponential growth `e^{K Im z}` on the
  strip `0 ≤ Re z ≤ 1` is a convergent `q`-series based at an explicit exponent
  `r − N`. The proof is Riemann's removable singularity theorem for the cusp
  function (Mathlib's `Function.Periodic.differentiableAt_cuspFunction_zero`)
  and the Taylor expansion on the unit disc.
-/
namespace VOA.Huang.GenusOne.Close
open VOA Complex Filter
open scoped Real Topology

/-! ## Uniqueness -/

theorem qTerm_imAxis (χ : FormalQSeries) (b : ℂ) (n : ℕ) (t : ℝ) :
    ‖qTerm χ b n (I * (t : ℂ))‖ = ‖χ (b + (n : ℂ))‖ * Real.exp (-(2 * π * t)) ^ n := by
  rw [qTerm, norm_mul, norm_qexp, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

/-- Convergence on the whole upper half-plane forces subexponential coefficients. -/
theorem subexp_of_summable (χ : FormalQSeries) (b : ℂ)
    (hs : ∀ z ∈ imGT 0, Summable (fun n : ℕ => qTerm χ b n z)) :
    Subexponential (fun n : ℕ => ‖χ (b + (n : ℂ))‖) := by
  intro r hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  set t : ℝ := Real.log r / (2 * π) with ht
  have htpos : 0 < t := div_pos (Real.log_pos hr) (by positivity)
  have hz : I * (t : ℂ) ∈ imGT 0 := by
    change (0 : ℝ) < (I * (t : ℂ)).im
    simpa using htpos
  have hexp : Real.exp (-(2 * π * t)) = r⁻¹ := by
    rw [ht, show -(2 * π * (Real.log r / (2 * π))) = -Real.log r by field_simp,
      Real.exp_neg, Real.exp_log hr0]
  have hb := ((hs _ hz).tendsto_cofinite_zero.norm).bddAbove_range_of_cofinite
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, fun n => ?_⟩
  have h1 : ‖qTerm χ b n (I * (t : ℂ))‖ ≤ C := hC ⟨n, rfl⟩
  rw [qTerm_imAxis, hexp, inv_pow] at h1
  have hrn : 0 < r ^ n := pow_pos hr0 n
  calc ‖χ (b + (n : ℂ))‖ = ‖χ (b + (n : ℂ))‖ * (r ^ n)⁻¹ * r ^ n := by
        field_simp
    _ ≤ C * r ^ n := mul_le_mul_of_nonneg_right h1 hrn.le

theorem qSummableAt_of_summable_qTerm {χ : FormalQSeries} {b : ℂ} {τ : UpperHalfPlane}
    (hs : Summable (fun n : ℕ => qTerm χ b n (τ : ℂ))) : QSummableAt χ b τ := by
  refine hs.congr fun n => ?_
  rw [qTerm, VOA.qParam, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- **Uniqueness of `q`-expansions on the upper half-plane.** -/
theorem eq_zero_of_qEvalC {χ : FormalQSeries} {b : ℂ} (hχ : χ ∈ QSeriesAt b)
    (hs : ∀ z ∈ imGT 0, Summable (fun n : ℕ => qTerm χ b n z))
    (h0 : ∀ z ∈ imGT 0, qEvalC χ b z = 0) : χ = 0 := by
  have hsub := subexp_of_summable χ b hs
  have hk : ∀ k : ℕ, χ (b + (k : ℂ)) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hsubk : Subexponential (fun n : ℕ => ‖χ (b + (k : ℂ) + (n : ℂ))‖) := by
        have := hsub.shift k
        refine (funext fun n => ?_ : (fun n : ℕ => ‖χ (b + ((n + k : ℕ) : ℂ))‖) =
          fun n : ℕ => ‖χ (b + (k : ℂ) + (n : ℂ))‖) ▸ this
        congr 2
        push_cast
        ring
      apply leading_coeff_eq_zero_of_qEvalAt_imAxis_eq_zero χ (b + (k : ℂ)) hsubk
      intro t ht
      have hτ := (imAxis t ht).im_pos
      rw [← qEvalAt_shift χ b k (imAxis t ht)
        (qSummableAt_of_summable_qTerm (hs _ hτ)) ih, ← qEvalC_coe]
      exact h0 _ hτ
  exact QSeriesAt.ext hχ (QSeriesAt b).zero_mem (fun n => by simpa using hk n)

/-! ## Existence -/

/-- The base exponent produced by the expansion theorem. -/
noncomputable def expBase (r : ℂ) (K : ℝ) : ℂ :=
  r - ((⌈K / (2 * π) + ‖r‖⌉₊ : ℕ) : ℂ)

theorem expBase_re_bound (r : ℂ) (K : ℝ) : 2 * π * (expBase r K).re + K ≤ 0 := by
  have hN := Nat.le_ceil (K / (2 * π) + ‖r‖)
  have hre : r.re ≤ ‖r‖ := Complex.re_le_norm r
  have hpi : 0 < 2 * π := by positivity
  simp only [expBase, Complex.sub_re, Complex.natCast_re]
  have h1 : K / (2 * π) * (2 * π) = K := by field_simp
  nlinarith

theorem expBase_im (r : ℂ) (K : ℝ) : (expBase r K).im = r.im := by
  simp [expBase]

theorem exp_two_pi_I_expBase (r : ℂ) (K : ℝ) :
    cexp (2 * π * I * expBase r K) = cexp (2 * π * I * r) := by
  rw [expBase, mul_sub, Complex.exp_sub,
    show 2 * π * I * ((⌈K / (2 * π) + ‖r‖⌉₊ : ℕ) : ℂ) =
      ((⌈K / (2 * π) + ‖r‖⌉₊ : ℕ) : ℂ) * (2 * π * I) by ring,
    Complex.exp_nat_mul_two_pi_mul_I, div_one]

/-- **Cusp expansion.** -/
theorem exists_expansion (Φ : ℂ → ℂ) (r : ℂ) (K C : ℝ)
    (hholo : DifferentiableOn ℂ Φ (imGT 0))
    (hper : ∀ z ∈ imGT 0, Φ (z + 1) = cexp (2 * π * I * r) * Φ z)
    (hbd : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im → ‖Φ z‖ ≤ C * Real.exp (K * z.im)) :
    ∃ a : ℕ → ℂ, ∀ z ∈ imGT 0, HasSum (fun n : ℕ => a n * cexp (2 * π * I * n * z))
      (cexp (-(2 * π * I * expBase r K * z)) * Φ z) := by
  set b := expBase r K with hbdef
  let g : ℂ → ℂ := fun z => cexp (-(2 * π * I * b * z)) * Φ z
  let f : ℂ → ℂ := (imGT 0).indicator g
  have himadd : ∀ z : ℂ, (z + 1).im = z.im := fun z => by simp
  have hmem_add : ∀ z : ℂ, z + 1 ∈ imGT 0 ↔ z ∈ imGT 0 := fun z => by
    change (0 : ℝ) < (z + 1).im ↔ (0 : ℝ) < z.im
    rw [himadd]
  have hgper : ∀ z ∈ imGT 0, g (z + 1) = g z := by
    intro z hz
    simp only [g]
    rw [hper z hz, show -(2 * π * I * b * (z + 1)) = -(2 * π * I * b * z) + -(2 * π * I * b)
      by ring, Complex.exp_add, Complex.exp_neg (2 * π * I * b), hbdef,
      exp_two_pi_I_expBase]
    field_simp [Complex.exp_ne_zero]
  have hfper : Function.Periodic f 1 := by
    intro z
    by_cases hz : z ∈ imGT 0
    · have hz1 := (hmem_add z).mpr hz
      simp only [f, Set.indicator_of_mem hz, Set.indicator_of_mem hz1]
      exact hgper z hz
    · have hz1 : z + 1 ∉ imGT 0 := fun h => hz ((hmem_add z).mp h)
      simp only [f, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz1]
  have hgdiff : ∀ z ∈ imGT 0, DifferentiableAt ℂ g z := by
    intro z hz
    have hΦ := (hholo z hz).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    exact (Complex.differentiable_exp.differentiableAt.comp z
      ((differentiableAt_id.const_mul _).neg)).mul hΦ
  have hfdiff : ∀ z ∈ imGT 0, DifferentiableAt ℂ f z := by
    intro z hz
    refine (hgdiff z hz).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
    simp only [f, Set.indicator_of_mem hw]
  -- boundedness at the cusp
  set C' : ℝ := |C| * Real.exp (2 * π * |r.im|) with hC'
  have hbound : ∀ z : ℂ, 1 ≤ z.im → ‖f z‖ ≤ C' := by
    intro z hz
    set n : ℤ := ⌊z.re⌋ with hn
    set z' : ℂ := z - (n : ℂ) * ((1 : ℝ) : ℂ) with hz'
    have hfz : f z = f z' := (hfper.sub_int_mul_eq n).symm
    have hre : z'.re = z.re - n := by simp [hz']
    have him : z'.im = z.im := by simp [hz']
    have hre0 : 0 ≤ z'.re := by rw [hre]; linarith [Int.floor_le z.re]
    have hre1 : z'.re ≤ 1 := by rw [hre]; linarith [Int.lt_floor_add_one z.re]
    have hz'mem : z' ∈ imGT 0 := by
      change (0 : ℝ) < z'.im
      rw [him]; linarith
    rw [hfz]
    simp only [f, Set.indicator_of_mem hz'mem, g, norm_mul, Complex.norm_exp]
    have hΦ := hbd z' hre0 hre1 (by rw [him]; exact hz)
    have hre_exp : (-(2 * π * I * b * z')).re = 2 * π * (b.re * z'.im + b.im * z'.re) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [hre_exp]
    have hbre := expBase_re_bound r K
    have hbim : b.im = r.im := expBase_im r K
    have hy : 0 ≤ z'.im := by rw [him]; linarith
    have hx : b.im * z'.re ≤ |r.im| := by
      rw [hbim]
      calc r.im * z'.re ≤ |r.im| * z'.re :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hre0
        _ ≤ |r.im| * 1 := mul_le_mul_of_nonneg_left hre1 (abs_nonneg _)
        _ = |r.im| := mul_one _
    have hC : C ≤ |C| := le_abs_self C
    have hnorm : 0 ≤ ‖Φ z'‖ := norm_nonneg _
    calc Real.exp (2 * π * (b.re * z'.im + b.im * z'.re)) * ‖Φ z'‖
        ≤ Real.exp (2 * π * (b.re * z'.im + b.im * z'.re)) * (C * Real.exp (K * z'.im)) :=
          mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le
      _ ≤ Real.exp (2 * π * (b.re * z'.im + b.im * z'.re)) * (|C| * Real.exp (K * z'.im)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = |C| * Real.exp ((2 * π * b.re + K) * z'.im + 2 * π * (b.im * z'.re)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
      _ ≤ |C| * Real.exp (2 * π * |r.im|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          apply Real.exp_le_exp.mpr
          have h1 : (2 * π * b.re + K) * z'.im ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) hy
          have h2 : 2 * π * (b.im * z'.re) ≤ 2 * π * |r.im| :=
            mul_le_mul_of_nonneg_left hx (by positivity)
          linarith
  have hI : ∀ᶠ z in comap Complex.im atTop, 1 ≤ z.im :=
    Filter.preimage_mem_comap (Filter.Ici_mem_atTop 1)
  have h_hol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ f z := by
    filter_upwards [hI] with z hz
    exact hfdiff z (by change (0 : ℝ) < z.im; linarith)
  have h_bd : BoundedAtFilter (comap Complex.im atTop) f := by
    refine Asymptotics.IsBigO.of_bound C' ?_
    filter_upwards [hI] with z hz
    simpa using hbound z hz
  -- the cusp function is holomorphic on the unit disc
  set F := Function.Periodic.cuspFunction 1 f with hF
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      exact (Function.Periodic.differentiableAt_cuspFunction_zero one_pos hfper h_hol
        h_bd).differentiableWithinAt
    · have hq1 : ‖q‖ < 1 := by simpa using hq
      have him : 0 < (Function.Periodic.invQParam 1 q).im := by
        rw [Function.Periodic.im_invQParam]
        have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq0) hq1
        have : 0 < -1 / (2 * π) * Real.log ‖q‖ := by
          rw [div_mul_eq_mul_div, neg_one_mul]
          exact div_pos (by linarith) (by positivity)
        simpa using this
      have hd := Function.Periodic.differentiableAt_cuspFunction one_ne_zero hfper
        (hfdiff _ him)
      rw [Function.Periodic.qParam_right_inv one_ne_zero hq0] at hd
      exact hd.differentiableWithinAt
  refine ⟨fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0, fun z hz => ?_⟩
  have hqmem : Function.Periodic.qParam 1 z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    apply Real.exp_lt_one_iff.mpr
    have : (0 : ℝ) < z.im := hz
    have : 0 < 2 * π * z.im := by positivity
    simp only [div_one]
    linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hFdiff hqmem
  rw [hF, Function.Periodic.eq_cuspFunction one_ne_zero hfper z] at hs
  simp only [f, Set.indicator_of_mem hz] at hs
  refine hs.congr_fun fun n => ?_
  simp only [sub_zero, smul_eq_mul, Function.Periodic.qParam, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul, hF]
  rw [show (n : ℂ) * (2 * π * I * z) = 2 * π * I * n * z by ring]
  ring

end VOA.Huang.GenusOne.Close

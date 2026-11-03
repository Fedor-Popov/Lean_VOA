import Mathlib

/-!
# Uniqueness of generalized power-series expansions near a branch point

Step (5h) of the proof of (G1), the analytic half of Huang's Prop. 2.11.

If finitely many series `Σ_s a_{i,s} u^{γ_i + s}` (principal powers, absolutely convergent at
radius `ρ`) sum to zero on a nonempty open subset of the right half of the punctured disc, then
for every complex exponent `μ` the total coefficient of `u^μ` vanishes. The proof works in the
logarithmic coordinate `L = log u`: the sum `Φ(L) = Σ_i Σ_s a_{i,s} e^{(γ_i+s)L}` is holomorphic on
the half-plane `Re L < log ρ`, vanishes identically there (identity theorem), hence also after the
shifts `L ↦ L + 2πim`; a Lagrange-interpolation argument on the multipliers `e^{2πiγ_i}` separates
the classes of `γ_i` mod `ℤ`, and on one class the series is an honest power series in `e^L`
vanishing on a punctured disc.

This is NOT exponent separation at fixed `τ` across channels of the same class (which fails at
`c = 1`); it only separates distinct classes mod `ℤ`, and identifies the coefficients inside one
class.

* `gen_series_unique`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open Complex
open scoped BigOperators Topology

/-- The log-coordinate series of one family. -/
def logSeries (γ : ℂ) (a : ℕ → ℂ) (L : ℂ) : ℂ := ∑' s : ℕ, a s * exp ((γ + s) * L)

theorem norm_exp_le_aux (γ L : ℂ) (s : ℕ) {K R : ℝ} (hK : ‖L‖ ≤ K) (hR : L.re ≤ R) :
    ‖exp ((γ + s) * L)‖ ≤ Real.exp (‖γ‖ * K) * Real.exp R ^ s := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ((γ + s) * L).re = (γ * L).re + s * L.re := by simp [add_mul]
  rw [h1]
  have h2' : ‖γ * L‖ ≤ ‖γ‖ * K := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)
  have h2 : (γ * L).re ≤ ‖γ‖ * K := (Complex.re_le_norm _).trans h2'
  have h3 : (s : ℝ) * L.re ≤ s * R := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg s)
  linarith

theorem logSeries_summable (γ : ℂ) (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (ha : Summable (fun s => ‖a s‖ * ρ ^ s)) {L : ℂ} (hL : L.re < Real.log ρ) :
    Summable (fun s : ℕ => ‖a s * exp ((γ + s) * L)‖) := by
  refine (ha.mul_left (Real.exp (‖γ‖ * ‖L‖))).of_nonneg_of_le (fun s => norm_nonneg _)
    fun s => ?_
  rw [norm_mul]
  have h := norm_exp_le_aux γ L s le_rfl hL.le
  have he : Real.exp (Real.log ρ) = ρ := Real.exp_log hρ
  rw [he] at h
  calc ‖a s‖ * ‖exp ((γ + s) * L)‖ ≤ ‖a s‖ * (Real.exp (‖γ‖ * ‖L‖) * ρ ^ s) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- The log-coordinate series is holomorphic on the half-plane `Re L < log ρ`. -/
theorem logSeries_differentiableOn (γ : ℂ) (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (ha : Summable (fun s => ‖a s‖ * ρ ^ s)) :
    DifferentiableOn ℂ (logSeries γ a) {L : ℂ | L.re < Real.log ρ} := by
  intro L0 hL0
  simp only [Set.mem_setOf_eq] at hL0
  set R : ℝ := (L0.re + Real.log ρ) / 2 with hR
  set K : ℝ := ‖L0‖ + 1 with hK
  set V : Set ℂ := {L | L.re < R} ∩ Metric.ball L0 1 with hV
  have hVo : IsOpen V :=
    (isOpen_lt Complex.continuous_re continuous_const).inter Metric.isOpen_ball
  have hL0R : L0.re < R := by rw [hR]; linarith
  have hL0V : L0 ∈ V := ⟨hL0R, Metric.mem_ball_self one_pos⟩
  have hRρ : Real.exp R ≤ ρ := by
    rw [← Real.exp_log hρ]; exact Real.exp_le_exp.mpr (by rw [hR]; linarith)
  have hdiff : DifferentiableOn ℂ (logSeries γ a) V := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun s => Real.exp (‖γ‖ * K) * (‖a s‖ * ρ ^ s)) (ha.mul_left _)
      (fun s => ((differentiable_exp.comp (differentiable_id.const_mul _)).const_mul
        _).differentiableOn) hVo fun s L hL => ?_
    obtain ⟨hL1, hL2⟩ := hL
    have hnL : ‖L‖ ≤ K := by
      have := norm_le_norm_add_norm_sub' L L0
      rw [Metric.mem_ball, dist_eq_norm] at hL2
      rw [hK]; linarith [norm_sub_rev L L0]
    have h := norm_exp_le_aux γ L s hnL hL1.le
    rw [norm_mul]
    calc ‖a s‖ * ‖exp ((γ + s) * L)‖ ≤ ‖a s‖ * (Real.exp (‖γ‖ * K) * Real.exp R ^ s) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ ‖a s‖ * (Real.exp (‖γ‖ * K) * ρ ^ s) := by
          gcongr
      _ = _ := by ring
  exact (hdiff.differentiableAt (hVo.mem_nhds hL0V)).differentiableWithinAt

/-! ## A power series vanishing on a punctured disc -/

theorem ps_coeff_zero (c : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hc : Summable (fun n => ‖c n‖ * ρ ^ n))
    (h0 : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → ∑' n, c n * w ^ n = 0) : ∀ n, c n = 0 := by
  have hsw : ∀ w : ℂ, ‖w‖ ≤ ρ → Summable (fun n => c n * w ^ n) := by
    intro w hw
    refine Summable.of_norm (hc.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw n) (norm_nonneg _)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- the shifted series vanishes on the punctured disc
    have hshift : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → ∑' m, c (m + n) * w ^ m = 0 := by
      intro w hw hwr
      have h := h0 w hw hwr
      rw [← (hsw w hwr.le).sum_add_tsum_nat_add n] at h
      have hlow : ∑ i ∈ Finset.range n, c i * w ^ i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]
      rw [hlow, zero_add] at h
      have h2 : ∑' m, c (m + n) * w ^ (m + n) = w ^ n * ∑' m, c (m + n) * w ^ m := by
        rw [← tsum_mul_left]; exact tsum_congr fun m => by rw [pow_add]; ring
      rw [h2] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw)
    -- a bound for the tail
    set r : ℝ := ρ / 2 with hr
    have hr0 : 0 < r := by positivity
    have hrρ : r < ρ := by linarith
    have htail : Summable (fun m => ‖c (m + n + 1)‖ * r ^ m) := by
      have h := (summable_nat_add_iff (n + 1)).mpr hc
      refine (h.mul_left (ρ ^ (n + 1))⁻¹).of_nonneg_of_le
        (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) fun m => ?_
      have hp : r ^ m ≤ ρ ^ m := pow_le_pow_left₀ hr0.le hrρ.le m
      have hρn : 0 < ρ ^ (n + 1) := pow_pos hρ _
      calc ‖c (m + n + 1)‖ * r ^ m ≤ ‖c (m + n + 1)‖ * ρ ^ m :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ = (ρ ^ (n + 1))⁻¹ * (‖c (m + (n + 1))‖ * ρ ^ (m + (n + 1))) := by
            rw [pow_add, show m + n + 1 = m + (n + 1) by ring]
            field_simp
            ring
    set B : ℝ := ∑' m, ‖c (m + n + 1)‖ * r ^ m with hB
    have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ r → ‖c n‖ ≤ ε * B := by
      intro ε hε hεr
      have hw : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hwn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
      have hz := hshift ε hw (by rw [hwn]; linarith)
      have hs : Summable (fun m => c (m + n) * (ε : ℂ) ^ m) := by
        have := (hsw ε (by rw [hwn]; linarith)).comp_injective (add_left_injective n)
        refine (this.mul_left ((ε : ℂ) ^ n)⁻¹).congr fun m => ?_
        simp only [Function.comp_apply, pow_add]
        field_simp
      rw [hs.tsum_eq_zero_add] at hz
      simp only [zero_add, pow_zero, mul_one] at hz
      have hcn : c n = -((ε : ℂ) * ∑' m, c (m + n + 1) * (ε : ℂ) ^ m) := by
        rw [← tsum_mul_left]
        have : ∑' m, c (m + 1 + n) * (ε : ℂ) ^ (m + 1) =
            ∑' m, (ε : ℂ) * (c (m + n + 1) * (ε : ℂ) ^ m) :=
          tsum_congr fun m => by rw [show m + 1 + n = m + n + 1 by ring, pow_succ]; ring
        rw [← this]; linear_combination hz
      rw [hcn, norm_neg, norm_mul, hwn]
      refine mul_le_mul_of_nonneg_left ?_ hε.le
      have hsn : Summable (fun m => ‖c (m + n + 1) * (ε : ℂ) ^ m‖) :=
        htail.of_nonneg_of_le (fun m => norm_nonneg _) fun m => by
          rw [norm_mul, norm_pow, hwn]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεr m) (norm_nonneg _)
      refine (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum (fun m => ?_) hsn htail)
      rw [norm_mul, norm_pow, hwn]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεr m) (norm_nonneg _)
    have hB0 : 0 ≤ B := tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    have : ‖c n‖ ≤ 0 := by
      by_contra hpos
      push Not at hpos
      set ε : ℝ := min r (‖c n‖ / (2 * (B + 1))) with hε
      have hε0 : 0 < ε := lt_min hr0 (by positivity)
      have h1 := hbound ε hε0 (min_le_left _ _)
      have h2 : ε * B ≤ ‖c n‖ / (2 * (B + 1)) * B :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hB0
      have h3 : ‖c n‖ / (2 * (B + 1)) * B < ‖c n‖ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    exact norm_le_zero_iff.mp this

/-! ## Separating the classes of the multipliers -/

theorem class_sep {J : Type*} [Fintype J] (lam v : J → ℂ)
    (h : ∀ m : ℕ, ∑ i, lam i ^ m * v i = 0) (i0 : J) :
    ∑ i ∈ Finset.univ.filter (fun i => lam i = lam i0), v i = 0 := by
  classical
  set Λ : Finset ℂ := Finset.univ.image lam with hΛ
  set p : Polynomial ℂ := ∏ μ ∈ Λ.erase (lam i0), (Polynomial.X - Polynomial.C μ) with hp
  have hP0 : p.eval (lam i0) ≠ 0 := by
    rw [hp, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro μ hμ
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ).symm
  have hPi : ∀ i, lam i ≠ lam i0 → p.eval (lam i) = 0 := by
    intro i hi
    rw [hp, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := lam i) (Finset.mem_erase.mpr ⟨hi,
      Finset.mem_image_of_mem lam (Finset.mem_univ i)⟩) ?_
    simp
  have hsum : ∑ i, p.eval (lam i) * v i = 0 := by
    simp only [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m _ => ?_
    have : ∑ x, p.coeff m * lam x ^ m * v x = p.coeff m * ∑ i, lam i ^ m * v i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h m, mul_zero]
  have hsplit : ∑ i, p.eval (lam i) * v i =
      p.eval (lam i0) * ∑ i ∈ Finset.univ.filter (fun i => lam i = lam i0), v i := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hi]
    · rw [hPi i hi, zero_mul]
  rw [hsplit] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hP0

/-! ## The uniqueness theorem -/

theorem exp_shift (γ L : ℂ) (s m : ℕ) :
    exp ((γ + s) * (L + 2 * (Real.pi : ℂ) * I * m)) =
      exp (2 * (Real.pi : ℂ) * I * γ) ^ m * exp ((γ + s) * L) := by
  have he : (γ + s) * (L + 2 * (Real.pi : ℂ) * I * m) =
      (γ + s) * L + (m : ℂ) * (2 * (Real.pi : ℂ) * I * γ) +
        ((s * m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
  rw [he, exp_add, exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul_two_pi_mul_I]
  ring

/-- Reindexing a shifted power series. -/
theorem tsum_shift_ite (b : ℕ → ℂ) (e : ℕ) (w : ℂ) :
    ∑' n : ℕ, (if e ≤ n then b (n - e) else 0) * w ^ n = ∑' s : ℕ, b s * w ^ (s + e) := by
  have hinj : Function.Injective (fun s : ℕ => s + e) := add_left_injective e
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun s => ?_
    simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases h : e ≤ n
    · exact ⟨n - e, by simp only; omega⟩
    · rw [if_neg h, zero_mul] at hn; exact absurd rfl hn

/-- **Uniqueness of generalized power-series expansions.** -/
theorem gen_series_unique {J : Type*} [Fintype J] (γ : J → ℂ) (a : J → ℕ → ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (ha : ∀ i, Summable (fun s => ‖a i s‖ * ρ ^ s)) {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (hUsub : ∀ u ∈ U, ‖u‖ < ρ ∧ 0 < u.re)
    (h0 : ∀ u ∈ U, ∑ i, ∑' s : ℕ, a i s * exp ((γ i + s) * log u) = 0) (μ : ℂ) :
    ∑ i, ∑' s : ℕ, (if γ i + s = μ then a i s else 0) = 0 := by
  classical
  set H : Set ℂ := {L | L.re < Real.log ρ} with hH
  have hHo : IsOpen H := isOpen_lt Complex.continuous_re continuous_const
  have hHc : IsPreconnected H := (convex_halfSpace_re_lt (Real.log ρ)).isPreconnected
  let Φ : ℂ → ℂ := fun L => ∑ i, logSeries (γ i) (a i) L
  have hΦd : DifferentiableOn ℂ Φ H :=
    DifferentiableOn.fun_sum fun i _ => logSeries_differentiableOn (γ i) (a i) hρ (ha i)
  have hΦa : AnalyticOnNhd ℂ Φ H := hΦd.analyticOnNhd hHo
  obtain ⟨u0, hu0⟩ := hne
  have hu0r := hUsub u0 hu0
  have hu00 : u0 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu0r; exact lt_irrefl _ hu0r.2
  have hL0H : log u0 ∈ H := by
    simp only [hH, Set.mem_setOf_eq, Complex.log_re]
    exact Real.log_lt_log (norm_pos_iff.mpr hu00) hu0r.1
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu0r.2))
  have hev : Φ =ᶠ[𝓝 (log u0)] 0 := by
    have hopen : IsOpen ({L : ℂ | exp L ∈ U} ∩ {L : ℂ | |L.im| < Real.pi / 2}) :=
      (hU.preimage continuous_exp).inter (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        continuous_const)
    have hmem : log u0 ∈ ({L : ℂ | exp L ∈ U} ∩ {L : ℂ | |L.im| < Real.pi / 2}) := by
      refine ⟨by simp only [Set.mem_setOf_eq, exp_log hu00]; exact hu0, ?_⟩
      simp only [Set.mem_setOf_eq, Complex.log_im]
      exact abs_lt.mpr harg
    filter_upwards [hopen.mem_nhds hmem] with L hL
    obtain ⟨hL1, hL2⟩ := hL
    simp only [Set.mem_setOf_eq] at hL1 hL2
    have hpi := Real.pi_pos
    have hL2' := abs_lt.mp hL2
    have hlog : log (exp L) = L := Complex.log_exp (by linarith) (by linarith)
    have h := h0 (exp L) hL1
    rw [hlog] at h
    exact h
  have hzero : Set.EqOn Φ 0 H := hΦa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHc hL0H hev
  -- the shifts `L ↦ L + 2πim`
  have hshift : ∀ (m : ℕ) (L : ℂ), L ∈ H →
      ∑ i, exp (2 * (Real.pi : ℂ) * I * γ i) ^ m * logSeries (γ i) (a i) L = 0 := by
    intro m L hL
    have hL' : L + 2 * (Real.pi : ℂ) * I * m ∈ H := by
      simp only [hH, Set.mem_setOf_eq] at hL ⊢
      have : (L + 2 * (Real.pi : ℂ) * I * m).re = L.re := by simp
      rw [this]; exact hL
    have h := hzero hL'
    simp only [Φ, Pi.zero_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold logSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun s => by rw [exp_shift]; ring
  -- the class sums vanish
  have hclass : ∀ (i0 : J) (L : ℂ), L ∈ H →
      ∑ i ∈ Finset.univ.filter (fun i => exp (2 * (Real.pi : ℂ) * I * γ i) =
        exp (2 * (Real.pi : ℂ) * I * γ i0)), logSeries (γ i) (a i) L = 0 :=
    fun i0 L hL => class_sep (fun i => exp (2 * (Real.pi : ℂ) * I * γ i))
      (fun i => logSeries (γ i) (a i) L) (fun m => hshift m L hL) i0
  by_cases hμ : ∃ i0 : J, ∃ s0 : ℕ, γ i0 + s0 = μ
  swap
  · push Not at hμ
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hμ i]
  obtain ⟨i0, s0, hs0⟩ := hμ
  set K := Finset.univ.filter (fun i => exp (2 * (Real.pi : ℂ) * I * γ i) =
    exp (2 * (Real.pi : ℂ) * I * γ i0)) with hK
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hdex : ∀ i ∈ K, ∃ dd : ℤ, γ i = γ i0 + dd := by
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp this
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ h2pi
    linear_combination hn
  choose! d hd using hdex
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℕ, D0 = ∑ i ∈ K, (d i).natAbs := ⟨_, rfl⟩
  have hdD : ∀ i ∈ K, 0 ≤ d i + D0 := by
    intro i hi
    have : (d i).natAbs ≤ ∑ i ∈ K, (d i).natAbs :=
      Finset.single_le_sum (f := fun i => (d i).natAbs) (fun _ _ => Nat.zero_le _) hi
    omega
  let e : J → ℕ := fun i => (d i + D0).toNat
  have he : ∀ i ∈ K, ((e i : ℕ) : ℂ) = (d i : ℂ) + D0 := by
    intro i hi
    have h1 : ((e i : ℕ) : ℤ) = d i + D0 := Int.toNat_of_nonneg (hdD i hi)
    have h2 : (((e i : ℕ) : ℤ) : ℂ) = ((d i + D0 : ℤ) : ℂ) := by rw [h1]
    push_cast at h2
    exact h2
  have hγ : ∀ i ∈ K, γ i = (γ i0 - D0) + e i := by
    intro i hi
    rw [hd i hi, he i hi]; ring
  let cn : ℕ → ℂ := fun n => ∑ i ∈ K, (if e i ≤ n then a i (n - e i) else 0)
  have hone : ∀ i, Summable (fun n => ‖(if e i ≤ n then a i (n - e i) else 0)‖ * ρ ^ n) := by
    intro i
    have hinj : Function.Injective (fun s : ℕ => s + e i) := add_left_injective (e i)
    rw [← hinj.summable_iff]
    · refine ((ha i).mul_left (ρ ^ e i)).congr fun s => ?_
      simp only [Function.comp_apply, le_add_iff_nonneg_left, zero_le, if_true,
        Nat.add_sub_cancel, pow_add]
      ring
    · intro n hn
      by_cases h : e i ≤ n
      · exact absurd ⟨n - e i, by simp only; omega⟩ hn
      · simp [h]
  have hcs : Summable (fun n => ‖cn n‖ * ρ ^ n) := by
    refine (summable_sum (s := K) fun i _ => hone i).of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le _)) fun n => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hρ.le _)
  have hps : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → ∑' n, cn n * w ^ n = 0 := by
    intro w hw hwr
    have hLH : log w ∈ H := by
      simp only [hH, Set.mem_setOf_eq, Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.mpr hw) hwr
    have hc := hclass i0 (log w) hLH
    have hls : ∀ i ∈ K, logSeries (γ i) (a i) (log w) =
        exp ((γ i0 - D0) * log w) * ∑' s, a i s * w ^ (s + e i) := by
      intro i hi
      unfold logSeries
      rw [← tsum_mul_left]
      refine tsum_congr fun s => ?_
      rw [hγ i hi]
      have h3 : ((γ i0 - D0) + e i + s) * log w =
          (γ i0 - D0) * log w + ((s + e i : ℕ) : ℂ) * log w := by push_cast; ring
      rw [h3, exp_add, Complex.exp_nat_mul, exp_log hw]
      ring
    rw [Finset.sum_congr rfl hls, ← Finset.mul_sum] at hc
    have hsum0 : ∑ i ∈ K, ∑' s, a i s * w ^ (s + e i) = 0 :=
      (mul_eq_zero.mp hc).resolve_left (exp_ne_zero _)
    have hsumm : ∀ i ∈ K, Summable (fun n => (if e i ≤ n then a i (n - e i) else 0) * w ^ n) := by
      intro i _
      refine Summable.of_norm ((hone i).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwr.le n) (norm_nonneg _)
    calc ∑' n, cn n * w ^ n =
          ∑' n, ∑ i ∈ K, (if e i ≤ n then a i (n - e i) else 0) * w ^ n :=
          tsum_congr fun n => by simp only [cn, Finset.sum_mul]
      _ = ∑ i ∈ K, ∑' n, (if e i ≤ n then a i (n - e i) else 0) * w ^ n :=
          Summable.tsum_finsetSum hsumm
      _ = ∑ i ∈ K, ∑' s, a i s * w ^ (s + e i) :=
          Finset.sum_congr rfl fun i _ => tsum_shift_ite _ _ _
      _ = 0 := hsum0
  have hcz := ps_coeff_zero cn hρ hcs hps
  have hterm_out : ∀ i ∉ K, ∀ s : ℕ, γ i + s ≠ μ := by
    intro i hi s hs
    apply hi
    simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and]
    have h4 : γ i = γ i0 + (((s0 : ℤ) - s : ℤ) : ℂ) := by
      push_cast; linear_combination hs - hs0
    rw [h4, mul_add, exp_add,
      show 2 * (Real.pi : ℂ) * I * (((s0 : ℤ) - s : ℤ) : ℂ) =
        (((s0 : ℤ) - s : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hterm_in : ∀ i ∈ K, ∑' s : ℕ, (if γ i + s = μ then a i s else 0) =
      if e i ≤ s0 + D0 then a i (s0 + D0 - e i) else 0 := by
    intro i hi
    have hiff : ∀ s : ℕ, γ i + s = μ ↔ e i + s = s0 + D0 := by
      intro s
      rw [hγ i hi, ← hs0]
      constructor
      · intro h5
        have h6 : ((e i + s : ℕ) : ℂ) = ((s0 + D0 : ℕ) : ℂ) := by
          push_cast; linear_combination h5
        exact_mod_cast h6
      · intro h5
        have h6 : ((e i + s : ℕ) : ℂ) = ((s0 + D0 : ℕ) : ℂ) := by rw [h5]
        push_cast at h6
        linear_combination h6
    by_cases hle : e i ≤ s0 + D0
    · rw [if_pos hle, tsum_eq_single (s0 + D0 - e i)]
      · rw [if_pos ((hiff _).mpr (by omega))]
      · intro s hs
        rw [if_neg (fun h5 => hs (by have := (hiff s).mp h5; omega))]
    · rw [if_neg hle]
      refine (tsum_congr fun s => ?_).trans tsum_zero
      rw [if_neg (fun h5 => hle (by have := (hiff s).mp h5; omega))]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => exp (2 * (Real.pi : ℂ) *
    I * γ i) = exp (2 * (Real.pi : ℂ) * I * γ i0))]
  rw [← hK, Finset.sum_congr rfl hterm_in]
  have hz2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ exp (2 * (Real.pi : ℂ) * I * γ i) =
      exp (2 * (Real.pi : ℂ) * I * γ i0)), ∑' s : ℕ, (if γ i + s = μ then a i s else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiK : i ∉ K := by
      simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hi).2
    refine (tsum_congr fun s => ?_).trans tsum_zero
    rw [if_neg (hterm_out i hiK s)]
  rw [hz2, add_zero]
  exact hcz (s0 + D0)

end VOA.Huang.GenusOneG1e

import VOA.Classification.COne.Conditional

/-!
# The classical gaps `GapQExpansion` and `GapThetaReduction`

This file discharges the two *classical* named gaps of `Conditional.lean`:

* `gapQExpansion : GapQExpansion` — the `q`-expansion principle:
  - `unique`: uniqueness of `q`-expansions on `ℍ` (`q = e^{2πiτ}` covers the punctured unit
    disc; the identity theorem for the analytic function `Σ dₙ qⁿ` plus
    `HasFPowerSeriesAt.eq_zero`);
  - `eta_mul`: `η(τ) = q^{1/24} ∏ (1 - qⁿ⁺¹) = q^{1/24} Σ eₙ qⁿ` with `eₙ` the coefficients of
    `eulerSeries` (finite products as polynomials, the majorant `∏ (1 + Xⁿ⁺¹)`, dominated
    convergence), followed by the Cauchy product of absolutely convergent series;
  - `theta`: regrouping `rankOneTheta` by `N = t m²` (`HasSum.tsum_fiberwise`).
* `gapThetaReduction : GapThetaReduction` — `θ_{n₀,r,a²b} = θ_{an₀,ar,b}` and the refinement
  `θ_{n₀,r,t} = Σ_{j mod R, j ≡ n₀ (r)} θ_{j,R,t}` for `r ∣ R`, with `R_b` the `lcm` of the
  moduli attached to the square-free part `b`.
-/

open Complex Real Filter Topology Finset

noncomputable section

namespace VOA.Classification.COne

/-! ## 1. Theta functions as sums over residue classes -/

/-- The term `e^{2πi t n² τ}`. -/
def thetaExp (t : ℝ) (τ : ℂ) (n : ℤ) : ℂ := cexp (2 * π * I * t * (n : ℂ) ^ 2 * τ)

theorem summable_thetaExp {t : ℝ} (ht : 0 < t) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (thetaExp t τ) := by
  refine (summable_rankOneThetaTerm 0 one_ne_zero ht hτ).congr fun m => ?_
  simp [rankOneThetaTerm, thetaExp]

theorem rankOneTheta_eq_tsum_ite (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) (t : ℝ) (τ : ℂ) :
    rankOneTheta n₀ r t τ = ∑' n : ℤ, if n ≡ n₀ [ZMOD r] then thetaExp t τ n else 0 := by
  have hg : Function.Injective (fun m : ℤ => n₀ + r * m) := fun a b h => by
    simpa [hr] using h
  rw [← hg.tsum_eq (f := fun n : ℤ => if n ≡ n₀ [ZMOD r] then thetaExp t τ n else 0),
    rankOneTheta]
  · refine tsum_congr fun m => ?_
    have : n₀ + r * m ≡ n₀ [ZMOD r] := by
      simp [Int.ModEq, Int.add_mul_emod_self_left]
    simp only [this, if_true, rankOneThetaTerm, thetaExp]
  · intro n hn
    rw [Function.mem_support] at hn
    have hc : n ≡ n₀ [ZMOD r] := by
      by_contra hc
      exact hn (if_neg hc)
    obtain ⟨k, hk⟩ := hc.symm.dvd
    exact ⟨k, by simp only; linarith⟩

theorem hasSum_rankOneTheta_ite (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) {τ : ℂ}
    (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => if n ≡ n₀ [ZMOD r] then thetaExp t τ n else 0)
      (rankOneTheta n₀ r t τ) := by
  rw [rankOneTheta_eq_tsum_ite n₀ hr]
  refine Summable.hasSum ?_
  exact ((summable_thetaExp ht hτ).indicator {n | n ≡ n₀ [ZMOD r]}).congr fun n => by
    simp [Set.indicator_apply]

/-- `θ_{n₀,r,a²b} = θ_{a n₀, a r, b}`. -/
theorem rankOneTheta_sq_mul (n₀ r : ℤ) (a b : ℕ) (τ : ℂ) :
    rankOneTheta n₀ r ((b ^ 2 * a : ℕ) : ℝ) τ = rankOneTheta (b * n₀) (b * r) (a : ℝ) τ := by
  unfold rankOneTheta
  refine tsum_congr fun m => ?_
  simp only [rankOneThetaTerm]
  congr 1
  push_cast
  ring

/-- Refinement of the modulus: for `r ∣ R`,
`θ_{n₀,r,t} = Σ_{j mod R, j ≡ n₀ (r)} θ_{j,R,t}`. -/
theorem rankOneTheta_refine (n₀ : ℤ) {r : ℤ} (hr : r ≠ 0) (R : ℕ) [NeZero R]
    (hrR : r ∣ (R : ℤ)) {t : ℝ} (ht : 0 < t) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t τ = ∑ j : ZMod R,
      (if ((j.val : ℕ) : ℤ) ≡ n₀ [ZMOD r] then 1 else 0) *
        rankOneTheta ((j.val : ℕ) : ℤ) (R : ℤ) t τ := by
  have hR : (R : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne R
  rw [rankOneTheta_eq_tsum_ite _ hr]
  simp_rw [rankOneTheta_eq_tsum_ite _ hR, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  · refine tsum_congr fun n => ?_
    rw [Finset.sum_eq_single (n : ZMod R)]
    · have h1 : n ≡ (((n : ZMod R).val : ℕ) : ℤ) [ZMOD (R : ℤ)] := by
        rw [ZMod.val_intCast]
        exact (Int.mod_modEq n R).symm
      have h2 : (((n : ZMod R).val : ℕ) : ℤ) ≡ n₀ [ZMOD r] ↔ n ≡ n₀ [ZMOD r] :=
        ⟨fun h => (h1.of_dvd hrR).trans h, fun h => (h1.of_dvd hrR).symm.trans h⟩
      by_cases hn : n ≡ n₀ [ZMOD r]
      · rw [if_pos hn, if_pos (h2.2 hn), if_pos h1, one_mul]
      · rw [if_neg hn, if_neg (mt h2.1 hn), zero_mul]
    · intro j _ hj
      have : ¬ n ≡ ((j.val : ℕ) : ℤ) [ZMOD (R : ℤ)] := by
        intro h
        apply hj
        rw [← ZMod.intCast_eq_intCast_iff] at h
        rw [h]
        simp
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _
    exact ((summable_thetaExp ht hτ).indicator
      {n | n ≡ ((j.val : ℕ) : ℤ) [ZMOD (R : ℤ)]}).mul_left
        (if ((j.val : ℕ) : ℤ) ≡ n₀ [ZMOD r] then 1 else 0) |>.congr fun n => by
        simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-! ## 2. `GapQExpansion.theta` -/

theorem gap_theta (r : ℕ) [NeZero r] (j : ZMod r) (t : ℕ) (ht : 0 < t) (τ : ℂ)
    (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (thetaCoeff r j t n : ℂ) * cexp (2 * Real.pi * I * n * τ))
      (rankOneTheta (j.val : ℕ) r t τ) := by
  classical
  have hr : (r : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h := (hasSum_rankOneTheta_ite ((j.val : ℕ) : ℤ) hr ht' hτ).tsum_fiberwise
    (fun m : ℤ => t * m.natAbs ^ 2)
  refine h.congr_fun fun N => ?_
  have hcond : ∀ m : ℤ, m ≡ ((j.val : ℕ) : ℤ) [ZMOD (r : ℤ)] ↔ (m : ZMod r) = j := by
    intro m
    rw [← ZMod.intCast_eq_intCast_iff]
    simp
  have hfib : ∀ m : ℤ, t * m.natAbs ^ 2 = N ↔ (t : ℤ) * m ^ 2 = N := by
    intro m
    rw [← Int.natAbs_sq m]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [_root_.tsum_subtype ((fun m : ℤ => t * m.natAbs ^ 2) ⁻¹' {N})
    (fun m : ℤ => if m ≡ ((j.val : ℕ) : ℤ) [ZMOD (r : ℤ)] then thetaExp t τ m else 0),
    tsum_eq_sum (s := Icc (-(N : ℤ)) N)]
  · rw [thetaCoeff, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, hfib]
    by_cases h1 : m ≡ ((j.val : ℕ) : ℤ) [ZMOD (r : ℤ)] <;> by_cases h2 : (t : ℤ) * m ^ 2 = N
    · rw [if_pos ⟨(hcond m).1 h1, h2⟩, if_pos h2, if_pos h1, Nat.cast_one, one_mul, thetaExp]
      congr 1
      have h2' : ((t : ℝ) : ℂ) * (m : ℂ) ^ 2 = (N : ℂ) := by
        push_cast
        exact_mod_cast h2
      linear_combination (-(2 * π * I * τ)) * h2'
    · rw [if_neg (fun h => h2 h.2), if_neg h2, Nat.cast_zero, zero_mul]
    · rw [if_neg (fun h => h1 ((hcond m).2 h.1)), if_pos h2, if_neg h1, Nat.cast_zero, zero_mul]
    · rw [if_neg (fun h => h2 h.2), if_neg h2, Nat.cast_zero, zero_mul]
  · intro m hm
    rw [Set.indicator_apply, if_neg]
    intro hmem
    apply hm
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    have h3 : m.natAbs ≤ N := by
      calc m.natAbs ≤ m.natAbs ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ t * m.natAbs ^ 2 := Nat.le_mul_of_pos_left _ ht
        _ = N := hmem
    rw [Finset.mem_Icc]
    omega

/-! ## 3. `GapThetaReduction` -/

theorem lcm_sq_dvd {x y M : ℕ} (hx : x ^ 2 ∣ M) (hy : y ^ 2 ∣ M) : (Nat.lcm x y) ^ 2 ∣ M := by
  rcases Nat.eq_zero_or_pos (Nat.gcd x y) with hg | hg
  · rw [Nat.gcd_eq_zero_iff] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simpa using hx
  obtain ⟨x', y', hco, hx', hy'⟩ := Nat.exists_coprime x y
  set g := Nat.gcd x y
  have hl : Nat.lcm x y = x' * y' * g := by
    rw [hx', hy', Nat.lcm_mul_right, hco.lcm_eq_mul]
  obtain ⟨K, hK⟩ : g ^ 2 ∣ M := (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left x y) 2).trans hx
  have hg2 : 0 < g ^ 2 := by positivity
  have hxK : x' ^ 2 ∣ K := by
    rw [hx', hK, mul_pow, mul_comm (g ^ 2)] at hx
    exact Nat.dvd_of_mul_dvd_mul_right hg2 hx
  have hyK : y' ^ 2 ∣ K := by
    rw [hy', hK, mul_pow, mul_comm (g ^ 2)] at hy
    exact Nat.dvd_of_mul_dvd_mul_right hg2 hy
  have := (Nat.Coprime.pow 2 2 hco).mul_dvd_of_dvd_of_dvd hxK hyK
  rw [hl, hK, mul_pow, mul_pow, mul_comm (g ^ 2)]
  exact Nat.mul_dvd_mul_right this _

theorem finset_lcm_sq_dvd {β : Type*} (S : Finset β) (x : β → ℕ) {M : ℕ}
    (h : ∀ p ∈ S, x p ^ 2 ∣ M) : (S.lcm x) ^ 2 ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.lcm_insert]
    exact lcm_sq_dvd (h a (Finset.mem_insert_self a S))
      (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- The square-free part of `t` (`t = sqPart t ^ 2 * sfPart t`). -/
def sfPart (t : ℕ) : ℕ := (Nat.sq_mul_squarefree t).choose

/-- The square root of the square part of `t`. -/
def sqPart (t : ℕ) : ℕ := (Nat.sq_mul_squarefree t).choose_spec.choose

theorem sqPart_spec (t : ℕ) : sqPart t ^ 2 * sfPart t = t ∧ Squarefree (sfPart t) :=
  (Nat.sq_mul_squarefree t).choose_spec.choose_spec

/-- One reduction step: `θ_{n₀,r,t} = Σ_{j mod R, j ≡ s n₀ (s r)} θ_{j,R,b}` where `t = s² b`. -/
theorem rankOneTheta_reduce (n₀ : ℤ) (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (R : ℕ+)
    (hR : sqPart t * r ∣ (R : ℕ)) {τ : ℂ} (hτ : 0 < τ.im) :
    rankOneTheta n₀ r t τ = ∑ j : ZMod (R : ℕ),
      (if ((j.val : ℕ) : ℤ) ≡ (sqPart t : ℤ) * n₀ [ZMOD ((sqPart t * r : ℕ) : ℤ)] then 1 else 0) *
        rankOneTheta ((j.val : ℕ) : ℤ) ((R : ℕ) : ℤ) (sfPart t) τ := by
  have hspec := (sqPart_spec t).1
  have hsq0 : sqPart t ≠ 0 := by
    intro h0; rw [h0] at hspec; simp at hspec; omega
  have hsf0 : sfPart t ≠ 0 := by
    intro h0; rw [h0] at hspec; simp at hspec; omega
  have ht' : ((t : ℕ) : ℝ) = ((sqPart t ^ 2 * sfPart t : ℕ) : ℝ) := by rw [hspec]
  rw [ht', rankOneTheta_sq_mul]
  have hx : ((sqPart t * r : ℕ) : ℤ) ≠ 0 := by
    have : sqPart t * r ≠ 0 := Nat.mul_ne_zero hsq0 (by omega)
    exact_mod_cast this
  have := rankOneTheta_refine ((sqPart t : ℤ) * n₀) hx (R : ℕ) (by exact_mod_cast hR)
    (t := (sfPart t : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero hsf0) hτ
  rw [← this]
  push_cast
  rfl

theorem gapThetaReduction : GapThetaReduction := by
  classical
  intro N hN s coef hs
  set b : ℤ × ℕ × ℕ → ℕ := fun p => sfPart p.2.2 with hb
  set x : ℤ × ℕ × ℕ → ℕ := fun p => sqPart p.2.2 * p.2.1 with hxdef
  set n : ℤ × ℕ × ℕ → ℤ := fun p => (sqPart p.2.2 : ℤ) * p.1 with hn
  set fib : ℕ → Finset (ℤ × ℕ × ℕ) := fun β => s.filter (fun p => b p = β) with hfib
  set L : ℕ → ℕ := fun β => (fib β).lcm x with hL
  have hx0 : ∀ p ∈ s, x p ≠ 0 := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := hs p hp
    have hspec := (sqPart_spec p.2.2).1
    have hsq0 : sqPart p.2.2 ≠ 0 := by
      intro h0; rw [h0] at hspec; simp at hspec; omega
    exact Nat.mul_ne_zero hsq0 (by omega)
  have hL0 : ∀ β, L β ≠ 0 := by
    intro β h0
    rw [hL, Finset.lcm_eq_zero_iff] at h0
    obtain ⟨p, hp, hp0⟩ := h0
    exact hx0 p (Finset.mem_filter.1 hp).1 hp0
  refine ⟨s.image b, fun β => ⟨L β, Nat.pos_of_ne_zero (hL0 β)⟩,
    fun β j => ∑ p ∈ fib β, coef p *
      (if ((j.val : ℕ) : ℤ) ≡ n p [ZMOD ((x p : ℕ) : ℤ)] then 1 else 0), ?_, ?_⟩
  · intro β hβ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hβ
    refine ⟨(sqPart_spec p.2.2).2, ?_⟩
    have key : ∀ q ∈ s, 4 * q.2.2 * q.2.1 ^ 2 = 4 * b q * x q ^ 2 := by
      intro q _
      have hspec := (sqPart_spec q.2.2).1
      simp only [hb, hxdef]
      conv_lhs => rw [← hspec]
      ring
    have h4 : 4 * b p ∣ N := by
      have := (hs p hp).2.2
      rw [key p hp] at this
      exact (Dvd.intro _ rfl).trans this
    change 4 * b p * L (b p) ^ 2 ∣ N
    rw [← Nat.dvd_div_iff_mul_dvd h4]
    refine finset_lcm_sq_dvd _ _ fun q hq => ?_
    obtain ⟨hqs, hqb⟩ := Finset.mem_filter.1 hq
    rw [Nat.dvd_div_iff_mul_dvd h4, ← hqb, ← key q hqs]
    exact (hs q hqs).2.2
  · intro τ hτ
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image b) (g := b)
      (fun p hp => Finset.mem_image_of_mem b hp)]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hps, hpb⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2, -⟩ := hs p hps
    have hdvd : x p ∣ L β := Finset.dvd_lcm hp
    rw [rankOneTheta_reduce p.1 p.2.1 p.2.2 h1 h2 ⟨L β, Nat.pos_of_ne_zero (hL0 β)⟩ hdvd hτ,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hβ : ((β : ℕ) : ℝ) = (sfPart p.2.2 : ℝ) := by rw [← hpb]
    rw [hβ]
    simp only [hn, hxdef]
    ring

/-! ## 4. Uniqueness of `q`-expansions -/

/-- A power series whose sum vanishes on the punctured unit disc is zero. -/
theorem coeffs_eq_zero_of_hasSum_zero (d : ℕ → ℂ)
    (h : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → HasSum (fun n => d n * q ^ n) 0) : d = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ d with hp
  have hrad : (((1 / 2 : NNReal)) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_tendsto (l := 0) ?_
    have := (h (1 / 2 : ℂ) (by norm_num) (by norm_num)).summable.tendsto_atTop_zero.norm
    simp only [norm_zero] at this
    refine this.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
    norm_num
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hF := p.hasFPowerSeriesOnBall hpos
  have hzero : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q hq0 hq1
    rw [FormalMultilinearSeries.sum]
    simp_rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    exact (h q hq0 hq1).tsum_eq
  have h0 : p.sum 0 = 0 := by
    have hc := hF.hasFPowerSeriesAt.continuousAt
    have h1 : Tendsto p.sum (𝓝[≠] 0) (𝓝 (p.sum 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto p.sum (𝓝[≠] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with q hq hq'
      rw [hzero q hq (by simpa using hq')]
    exact tendsto_nhds_unique h1 h2
  have hev : p.sum =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · rw [hq0, h0]; rfl
    · exact hzero q hq0 (by simpa using hq)
  have := (hF.hasFPowerSeriesAt.congr hev).eq_zero
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ)).1 this

/-- Every `q` in the punctured unit disc is `e^{2πiτ}` for some `τ ∈ ℍ`. -/
theorem exists_tau_of_norm_lt_one {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∃ τ : ℂ, 0 < τ.im ∧ cexp (2 * π * I * τ) = q := by
  refine ⟨((arg q / (2 * π) : ℝ) : ℂ) + ((-Real.log ‖q‖ / (2 * π) : ℝ) : ℂ) * I, ?_, ?_⟩
  · have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.2 hq0) hq1
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    apply div_pos (by linarith) (by positivity)
  · conv_rhs => rw [← Complex.exp_log hq0]
    congr 1
    rw [show Complex.log q = Real.log ‖q‖ + arg q * I from rfl]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    linear_combination (-(Real.log ‖q‖ : ℂ)) * I_sq

theorem gap_unique (c c' : ℕ → ℂ) (f : ℂ → ℂ)
    (hc : ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => c n * cexp (2 * Real.pi * I * n * τ)) (f τ))
    (hc' : ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => c' n * cexp (2 * Real.pi * I * n * τ)) (f τ)) :
    c = c' := by
  have := coeffs_eq_zero_of_hasSum_zero (c - c') fun q hq0 hq1 => by
    obtain ⟨τ, hτ, rfl⟩ := exists_tau_of_norm_lt_one hq0 hq1
    have := (hc τ hτ).sub (hc' τ hτ)
    rw [sub_self] at this
    refine this.congr_fun fun n => ?_
    have e : cexp (2 * Real.pi * I * n * τ) = cexp (2 * π * I * τ) ^ n := by
      rw [← Complex.exp_nat_mul]; ring_nf
    rw [Pi.sub_apply, e, sub_mul]
  exact sub_eq_zero.1 this

/-! ## 5. Euler's product as a power series -/

open Polynomial in
/-- `∏_{n<M} (1 - X^{n+1})` as a polynomial. -/
def eulerPoly (M : ℕ) : ℤ[X] := ∏ n ∈ range M, (1 - X ^ (n + 1))

open Polynomial in
/-- The majorant `∏_{n<M} (1 + X^{n+1})`. -/
def eulerMaj (M : ℕ) : ℕ[X] := ∏ n ∈ range M, (1 + X ^ (n + 1))

theorem coeff_eulerPoly_succ (M N : ℕ) : (eulerPoly (M + 1)).coeff N =
    (eulerPoly M).coeff N - if M + 1 ≤ N then (eulerPoly M).coeff (N - (M + 1)) else 0 := by
  rw [eulerPoly, prod_range_succ, ← eulerPoly, mul_sub, mul_one, Polynomial.coeff_sub,
    Polynomial.coeff_mul_X_pow']

theorem coeff_eulerMaj_succ (M N : ℕ) : (eulerMaj (M + 1)).coeff N =
    (eulerMaj M).coeff N + if M + 1 ≤ N then (eulerMaj M).coeff (N - (M + 1)) else 0 := by
  rw [eulerMaj, prod_range_succ, ← eulerMaj, mul_add, mul_one, Polynomial.coeff_add,
    Polynomial.coeff_mul_X_pow']

theorem coeff_eulerPoly_stable {N M : ℕ} (h : N ≤ M) :
    (eulerPoly M).coeff N = (eulerPoly N).coeff N := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => rw [coeff_eulerPoly_succ, if_neg (by omega), sub_zero, ih]

theorem coeff_eulerMaj_stable {N M : ℕ} (h : N ≤ M) :
    (eulerMaj M).coeff N = (eulerMaj N).coeff N := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => rw [coeff_eulerMaj_succ, if_neg (by omega), add_zero, ih]

theorem coeff_eulerMaj_le (M N : ℕ) : (eulerMaj M).coeff N ≤ (eulerMaj N).coeff N := by
  rcases le_total M N with h | h
  · have hmono : Monotone (fun M => (eulerMaj M).coeff N) :=
      monotone_nat_of_le_succ fun M => by
        rw [coeff_eulerMaj_succ]
        exact Nat.le_add_right _ _
    exact hmono h
  · rw [coeff_eulerMaj_stable h]

theorem abs_coeff_eulerPoly_le (M N : ℕ) :
    |(eulerPoly M).coeff N| ≤ ((eulerMaj M).coeff N : ℤ) := by
  induction M generalizing N with
  | zero =>
    simp only [eulerPoly, eulerMaj, range_zero, prod_empty, Polynomial.coeff_one]
    split_ifs <;> simp
  | succ M ih =>
    rw [coeff_eulerPoly_succ, coeff_eulerMaj_succ]
    split_ifs
    · push_cast
      exact (abs_sub _ _).trans (add_le_add (ih N) (ih _))
    · simpa using ih N

theorem coeff_eulerSeries_eq (N : ℕ) :
    PowerSeries.coeff N eulerSeries = (eulerPoly N).coeff N := by
  have : ((eulerPoly N : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ n ∈ range N, (1 - PowerSeries.X ^ (n + 1)) := by
    rw [eulerPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  rw [eulerSeries, PowerSeries.coeff_mk, ← Polynomial.coeff_coe, this]

theorem eval_eulerMaj (M : ℕ) (r : ℝ) :
    ((eulerMaj M).map (Nat.castRingHom ℝ)).eval r = ∏ n ∈ range M, (1 + r ^ (n + 1)) := by
  simp [eulerMaj, Polynomial.map_prod, Polynomial.eval_prod]

theorem eval_eulerPoly (M : ℕ) (q : ℂ) :
    ((eulerPoly M).map (Int.castRingHom ℂ)).eval q = ∏ n ∈ range M, (1 - q ^ (n + 1)) := by
  simp [eulerPoly, Polynomial.map_prod, Polynomial.eval_prod]

/-- The majorant coefficients `b_N = [X^N] ∏_{n<N} (1 + X^{n+1})` give a convergent series
on `[0, 1)`. -/
theorem summable_eulerMaj {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun N => ((eulerMaj N).coeff N : ℝ) * r ^ N) := by
  have hgeo := summable_geometric_of_lt_one hr0 hr1
  refine summable_of_sum_range_le (c := Real.exp (∑' n, r ^ n))
    (fun N => by positivity) fun L => ?_
  set P := (eulerMaj L).map (Nat.castRingHom ℝ)
  set K := max L (P.natDegree + 1)
  calc ∑ N ∈ range L, ((eulerMaj N).coeff N : ℝ) * r ^ N
      = ∑ N ∈ range L, P.coeff N * r ^ N := by
        refine Finset.sum_congr rfl fun N hN => ?_
        rw [Polynomial.coeff_map, coeff_eulerMaj_stable (Finset.mem_range.1 hN).le]
        rfl
    _ ≤ ∑ N ∈ range K, P.coeff N * r ^ N := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (le_max_left _ _)) fun N _ _ => ?_
        exact mul_nonneg (by simp [P, Polynomial.coeff_map]) (pow_nonneg hr0 _)
    _ = P.eval r := (Polynomial.eval_eq_sum_range' (by omega) r).symm
    _ = ∏ n ∈ range L, (1 + r ^ (n + 1)) := eval_eulerMaj L r
    _ ≤ ∏ n ∈ range L, Real.exp (r ^ (n + 1)) := by
        refine Finset.prod_le_prod (fun n _ => by positivity) fun n _ => ?_
        have := Real.add_one_le_exp (r ^ (n + 1))
        linarith
    _ = Real.exp (∑ n ∈ range L, r ^ (n + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n, r ^ n) := by
        refine Real.exp_le_exp.2 ?_
        calc ∑ n ∈ range L, r ^ (n + 1) ≤ ∑ n ∈ range (L + 1), r ^ n := by
              rw [Finset.sum_range_succ']
              simp
          _ ≤ ∑' n, r ^ n := hgeo.sum_le_tsum _ (fun n _ => by positivity)

theorem norm_eulerPoly_coeff_le (M N : ℕ) (q : ℂ) :
    ‖(((eulerPoly M).coeff N : ℤ) : ℂ) * q ^ N‖ ≤ ((eulerMaj N).coeff N : ℝ) * ‖q‖ ^ N := by
  rw [norm_mul, norm_pow, Complex.norm_intCast]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Int.cast_abs]
  have h1 := abs_coeff_eulerPoly_le M N
  have h2 := coeff_eulerMaj_le M N
  have : (|(eulerPoly M).coeff N| : ℤ) ≤ ((eulerMaj N).coeff N : ℤ) :=
    h1.trans (by exact_mod_cast h2)
  exact_mod_cast this

/-- **Euler's product expanded**: `∏ (1 - qⁿ⁺¹) = Σ eₙ qⁿ`, absolutely, on the unit disc. -/
theorem hasSum_eulerSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N => ((PowerSeries.coeff N eulerSeries : ℤ) : ℂ) * q ^ N)
        (∏' n, (1 - q ^ (n + 1))) ∧
      Summable (fun N => ‖((PowerSeries.coeff N eulerSeries : ℤ) : ℂ) * q ^ N‖) := by
  have hB := summable_eulerMaj (norm_nonneg q) hq
  have hnorm : Summable (fun N => ‖((PowerSeries.coeff N eulerSeries : ℤ) : ℂ) * q ^ N‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => by
      rw [coeff_eulerSeries_eq]; exact norm_eulerPoly_coeff_le N N q) hB
  refine ⟨?_, hnorm⟩
  have hfin : ∀ M, ∑' N, (((eulerPoly M).coeff N : ℤ) : ℂ) * q ^ N =
      ∏ n ∈ range M, (1 - q ^ (n + 1)) := by
    intro M
    set P := (eulerPoly M).map (Int.castRingHom ℂ)
    rw [← eval_eulerPoly, Polynomial.eval_eq_sum_range]
    rw [tsum_eq_sum (s := range (P.natDegree + 1))]
    · refine Finset.sum_congr rfl fun N _ => ?_
      rw [Polynomial.coeff_map]; rfl
    · intro N hN
      rw [Finset.mem_range, not_lt] at hN
      have : P.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [Polynomial.coeff_map] at this
      simp only [eq_intCast] at this
      rw [this, zero_mul]
  have hlim1 : Tendsto (fun M => ∑' N, (((eulerPoly M).coeff N : ℤ) : ℂ) * q ^ N) atTop
      (𝓝 (∑' N, ((PowerSeries.coeff N eulerSeries : ℤ) : ℂ) * q ^ N)) := by
    refine tendsto_tsum_of_dominated_convergence hB (fun N => ?_)
      (Eventually.of_forall fun M N => norm_eulerPoly_coeff_le M N q)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    rw [coeff_eulerSeries_eq, coeff_eulerPoly_stable hM]
  have hlim2 : Tendsto (fun M => ∑' N, (((eulerPoly M).coeff N : ℤ) : ℂ) * q ^ N) atTop
      (𝓝 (∏' n, (1 - q ^ (n + 1)))) := by
    simp_rw [hfin]
    exact (ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat
  rw [← tendsto_nhds_unique hlim1 hlim2]
  exact hnorm.of_norm.hasSum

/-! ## 6. `GapQExpansion.eta_mul` -/

/-- A `q`-series converging on all of `ℍ` converges absolutely there. -/
theorem summable_norm_qseries (c : ℕ → ℂ)
    (hc : ∀ τ : ℂ, 0 < τ.im → Summable (fun n : ℕ => c n * cexp (2 * π * I * n * τ)))
    {τ : ℂ} (hτ : 0 < τ.im) : Summable (fun n : ℕ => ‖c n * cexp (2 * π * I * n * τ)‖) := by
  set τ' : ℂ := τ - I * ((τ.im / 2 : ℝ) : ℂ)
  have hτ' : 0 < τ'.im := by simp [τ']; linarith
  set s : ℝ := Real.exp (-(π * τ.im))
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hs1 : s < 1 := Real.exp_lt_one_iff.2 (by have := Real.pi_pos; nlinarith)
  have hsplit : ∀ n : ℕ, cexp (2 * π * I * n * τ) = cexp (2 * π * I * n * τ') * (s : ℂ) ^ n := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [τ']
    push_cast
    ring_nf
    rw [I_sq]
    ring
  obtain ⟨C, hC⟩ := ((hc τ' hτ').tendsto_atTop_zero.norm).bddAbove_range
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one hs0 hs1).mul_left C)
  rw [hsplit, ← mul_assoc, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs0 _)
  exact hC ⟨n, rfl⟩

theorem gap_eta_mul (c : ℕ → ℂ) (g : ℂ → ℂ)
    (hg : ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => c n * cexp (2 * Real.pi * I * ((n : ℂ) - 1 / 24) * τ)) (g τ))
    (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => PowerSeries.coeff n
      (PowerSeries.map (Int.castRingHom ℂ) eulerSeries * PowerSeries.mk c) *
        cexp (2 * Real.pi * I * n * τ)) (ModularForm.eta τ * g τ) := by
  -- shift the `q^{-1/24}`
  have hshift : ∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ => c n * cexp (2 * π * I * n * τ))
      (g τ * cexp (2 * π * I * τ / 24)) := by
    intro τ hτ
    refine ((hg τ hτ).mul_right (cexp (2 * π * I * τ / 24))).congr_fun fun n => ?_
    rw [mul_assoc (c n) (cexp _) (cexp _), ← Complex.exp_add]
    congr 2
    ring
  set q := cexp (2 * π * I * τ) with hqdef
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hpow : ∀ n : ℕ, cexp (2 * π * I * n * τ) = q ^ n := by
    intro n; rw [hqdef, ← Complex.exp_nat_mul]; ring_nf
  obtain ⟨hE, hEn⟩ := hasSum_eulerSeries hq
  set e : ℕ → ℂ := fun N => ((PowerSeries.coeff N eulerSeries : ℤ) : ℂ) * q ^ N with he
  set a : ℕ → ℂ := fun n => c n * cexp (2 * π * I * n * τ) with ha
  have hA := hshift τ hτ
  have hAn : Summable (fun n => ‖a n‖) :=
    summable_norm_qseries c (fun τ hτ => (hshift τ hτ).summable) hτ
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hEn hAn
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hEn hAn).of_norm
  rw [hE.tsum_eq, hA.tsum_eq] at hprod
  have heta : ModularForm.eta τ * g τ = (∏' n, (1 - q ^ (n + 1))) *
      (g τ * cexp (2 * π * I * τ / 24)) := by
    rw [ModularForm.eta, Function.Periodic.qParam]
    simp_rw [ModularForm.eta_q_eq_pow]
    push_cast
    ring
  rw [heta, hprod]
  refine hsum.hasSum.congr_fun fun N => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  simp only [ha, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
  rw [hpow, hpow, ← hkl, pow_add]
  ring

/-! ## 7. The gaps, discharged -/

theorem gapQExpansion : GapQExpansion where
  unique := gap_unique
  eta_mul := gap_eta_mul
  theta := fun r _ j t ht τ hτ => gap_theta r j t ht τ hτ

end VOA.Classification.COne

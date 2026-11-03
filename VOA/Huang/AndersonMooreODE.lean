/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreQSeries
import VOA.Huang.FrobeniusUnique

/-!
# The solution space of a Serre-form linear ODE (Anderson–Moore)

Consider a linear ODE written with the iterated Serre derivatives `ϑ^m = amSerreIter m`,

  `B · ϑ^n y = Σ_{r<n} A_r · ϑ^r y`,

with `B, A_r` holomorphic on the upper half-plane.  If `g₀, …, g_{n−1}` are solutions whose
*Serre–Wronskian* `det [ϑ^m g_j (z₀)]` is nonzero at a point `z₀` with `B z₀ ≠ 0`, then every
holomorphic solution `y` is a constant linear combination of the `g_j` on the whole upper
half-plane (`exists_eq_sum_of_serreODE`).

Method.
* `exists_amSerreIter_expansion`: `ϑ^m f = Σ_{l ≤ m} e_{m,l} · f⁽ˡ⁾` with coefficients
  holomorphic on the upper half-plane and leading coefficient `(2πi)^{−m}`.
* Hence near `z₀` (where `B ≠ 0`) the Serre-form ODE is an ordinary linear ODE
  `F⁽ⁿ⁾ + Σ_{l<n} a_l F⁽ˡ⁾ = 0`; the Serre jet matrix factors as (coefficients) × (ordinary jet
  matrix), so the ordinary jet matrix is invertible and the jets of `y` can be matched.
* `VOA.Huang.FrobeniusLog.eqOn_zero_of_ode` kills the difference near `z₀`; the identity theorem
  propagates the vanishing to the connected upper half-plane.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

open Complex Filter Topology

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-- **Expansion of the iterated Serre derivative in ordinary derivatives**:
`ϑ^m f = Σ_{l ≤ m} e_l · f⁽ˡ⁾` on the upper half-plane, with `e_l` holomorphic there,
`e_l = 0` for `l > m`, and `e_m = (2πi)^{−m}`. -/
theorem exists_amSerreIter_expansion (m : ℕ) :
    ∃ e : ℕ → ℂ → ℂ, (∀ l, ∀ z ∈ imGT 0, AnalyticAt ℂ (e l) z) ∧
      (∀ l, m < l → e l = fun _ => 0) ∧
      (e m = fun _ => ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ m) ∧
      ∀ f : ℂ → ℂ, (∀ z ∈ imGT 0, AnalyticAt ℂ f z) → ∀ z ∈ imGT 0,
        amSerreIter m f z = ∑ l ∈ Finset.range (m + 1), e l z * iteratedDeriv l f z := by
  induction m with
  | zero =>
    refine ⟨fun l _ => if l = 0 then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro l z _; exact analyticAt_const
    · intro l hl; funext z; simp [show l ≠ 0 by omega]
    · funext z; simp
    · intro f _ z _; simp
  | succ m ih =>
    obtain ⟨e, he, hez, hem, hexp⟩ := ih
    set κ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hκ
    set c : ℂ := ((2 * (m : ℤ) : ℤ) : ℂ) * κ ^ 2 with hc
    refine ⟨fun l z => κ * (_root_.deriv (e l) z + (if l = 0 then 0 else e (l - 1) z))
        + c * (G2C z * e l z), ?_, ?_, ?_, ?_⟩
    · intro l z hz
      have hite : AnalyticAt ℂ (fun z => if l = 0 then (0 : ℂ) else e (l - 1) z) z := by
        by_cases hl : l = 0
        · simp only [hl, ↓reduceIte]; exact analyticAt_const
        · simp only [hl, ↓reduceIte]; exact he (l - 1) z hz
      exact (analyticAt_const.mul ((he l z hz).deriv.add hite)).add
        (analyticAt_const.mul ((analyticAt_G2C hz).mul (he l z hz)))
    · intro l hl
      funext z
      simp [hez l (by omega), hez (l - 1) (by omega), show l ≠ 0 by omega]
    · funext z
      simp [hez (m + 1) (by omega), hem, pow_succ]
      ring
    · intro f hf z hz
      have hU := isOpen_imGT 0
      have hfD : DifferentiableOn ℂ f (imGT 0) := fun w hw =>
        (hf w hw).differentiableAt.differentiableWithinAt
      set D : ℕ → ℂ → ℂ := fun l => iteratedDeriv l f with hD
      have hev : amSerreIter m f =ᶠ[𝓝 z]
          fun w => ∑ l ∈ Finset.range (m + 1), e l w * D l w :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => hexp f hf w hw
      have hder : HasDerivAt (fun w => ∑ l ∈ Finset.range (m + 1), e l w * D l w)
          (∑ l ∈ Finset.range (m + 1), (_root_.deriv (e l) z * D l z + e l z * D (l + 1) z)) z := by
        refine HasDerivAt.fun_sum fun l _ => ?_
        exact ((he l z hz).differentiableAt.hasDerivAt).mul
          (VOA.Huang.FrobeniusLog.hasDerivAt_iteratedDeriv hU hfD l hz)
      rw [amSerreIter_succ, serreDerivC_congr_of_eventuallyEq _ hev, serreDerivC, hder.deriv]
      change _ = ∑ l ∈ Finset.range (m + 1 + 1),
        (κ * (_root_.deriv (e l) z + (if l = 0 then 0 else e (l - 1) z))
          + c * (G2C z * e l z)) * D l z
      have hsplit : ∀ l ∈ Finset.range (m + 1 + 1),
          (κ * (_root_.deriv (e l) z + (if l = 0 then 0 else e (l - 1) z))
            + c * (G2C z * e l z)) * D l z
            = (κ * _root_.deriv (e l) z + c * (G2C z * e l z)) * D l z
              + κ * ((if l = 0 then 0 else e (l - 1) z) * D l z) := fun l _ => by ring
      have hR : ∑ l ∈ Finset.range (m + 1 + 1),
          (κ * (_root_.deriv (e l) z + (if l = 0 then 0 else e (l - 1) z))
            + c * (G2C z * e l z)) * D l z
          = ∑ l ∈ Finset.range (m + 1), ((κ * _root_.deriv (e l) z + c * (G2C z * e l z)) * D l z
            + κ * (e l z * D (l + 1) z)) := by
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
          Finset.sum_range_succ (fun l => (κ * _root_.deriv (e l) z + c * (G2C z * e l z)) * D l z),
          Finset.sum_range_succ' (fun l => κ * ((if l = 0 then 0 else e (l - 1) z) * D l z)),
          Finset.sum_add_distrib]
        simp [hez (m + 1) (by omega)]
      rw [hR, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hc, hκ]
      ring

/-- Extending the expansion sum by zero terms. -/
theorem sum_range_extend_of_zero {m N : ℕ} (hN : m + 1 ≤ N) (e : ℕ → ℂ → ℂ)
    (hez : ∀ l, m < l → e l = fun _ => 0) (D : ℕ → ℂ) (z : ℂ) :
    ∑ l ∈ Finset.range (m + 1), e l z * D l = ∑ l ∈ Finset.range N, e l z * D l := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun l hl hl' => ?_
  rw [Finset.mem_range] at hl hl'
  rw [hez l (by omega), zero_mul]

/-- **Anderson–Moore spanning**: if `n` solutions `g_j` of a Serre-form linear ODE
`B · ϑ^n y = Σ_{r<n} A_r · ϑ^r y` (holomorphic coefficients on the upper half-plane) have nonzero
Serre–Wronskian at a point `z₀` with `B z₀ ≠ 0`, every holomorphic solution is a constant linear
combination of them on the whole upper half-plane. -/
theorem exists_eq_sum_of_serreODE {n : ℕ} (B : ℂ → ℂ) (A : Fin n → ℂ → ℂ) (g : Fin n → ℂ → ℂ)
    (y : ℂ → ℂ)
    (hB : ∀ z ∈ imGT 0, AnalyticAt ℂ B z) (hA : ∀ r, ∀ z ∈ imGT 0, AnalyticAt ℂ (A r) z)
    (hg : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (g j) z) (hy : ∀ z ∈ imGT 0, AnalyticAt ℂ y z)
    (hgode : ∀ j, ∀ z ∈ imGT 0,
      B z * amSerreIter n (g j) z = ∑ r : Fin n, A r z * amSerreIter r (g j) z)
    (hyode : ∀ z ∈ imGT 0, B z * amSerreIter n y z = ∑ r : Fin n, A r z * amSerreIter r y z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) (hB₀ : B z₀ ≠ 0)
    (hW : (Matrix.of fun (m j : Fin n) => amSerreIter m (g j) z₀).det ≠ 0) :
    ∃ c : Fin n → ℂ, ∀ z ∈ imGT 0, y z = ∑ j, c j * g j z := by
  classical
  choose E hEan hEz hEtop hEexp using exists_amSerreIter_expansion
  set κ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := inv_ne_zero two_pi_I_ne_zero
  have hU := isOpen_imGT 0
  -- expansions truncated at `n`
  have hexpN : ∀ f : ℂ → ℂ, (∀ z ∈ imGT 0, AnalyticAt ℂ f z) → ∀ r : ℕ, r < n →
      ∀ z ∈ imGT 0, amSerreIter r f z
        = ∑ l ∈ Finset.range n, E r l z * iteratedDeriv l f z := by
    intro f hf r hr z hz
    rw [hEexp r f hf z hz]
    exact sum_range_extend_of_zero (by omega) (E r) (hEz r) (fun l => iteratedDeriv l f z) z
  have hexpTop : ∀ f : ℂ → ℂ, (∀ z ∈ imGT 0, AnalyticAt ℂ f z) → ∀ z ∈ imGT 0,
      amSerreIter n f z = ∑ l ∈ Finset.range n, E n l z * iteratedDeriv l f z
        + κ ^ n * iteratedDeriv n f z := by
    intro f hf z hz
    rw [hEexp n f hf z hz, Finset.sum_range_succ, hEtop n]
  -- the converted (ordinary) ODE, multiplied through by `B κ^n`
  set a' : ℕ → ℂ → ℂ := fun l z => B z * E n l z - ∑ r : Fin n, A r z * E r l z with ha'
  have ha'an : ∀ l, ∀ z ∈ imGT 0, AnalyticAt ℂ (a' l) z := by
    intro l z hz
    refine ((hB z hz).mul (hEan n l z hz)).sub ?_
    have := Finset.analyticAt_fun_sum (𝕜 := ℂ) (Finset.univ : Finset (Fin n))
      (f := fun (r : Fin n) w => A r w * E r l w) (c := z)
      (fun r _ => (hA r z hz).mul (hEan r l z hz))
    exact this
  have hconv : ∀ f : ℂ → ℂ, (∀ z ∈ imGT 0, AnalyticAt ℂ f z) →
      (∀ z ∈ imGT 0, B z * amSerreIter n f z = ∑ r : Fin n, A r z * amSerreIter r f z) →
      ∀ z ∈ imGT 0, B z * κ ^ n * iteratedDeriv n f z
        + ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l f z = 0 := by
    intro f hf hode z hz
    have h := hode z hz
    rw [hexpTop f hf z hz,
      Finset.sum_congr rfl (fun (r : Fin n) _ => by rw [hexpN f hf r r.isLt z hz])] at h
    have e1 : ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l f z
        = B z * ∑ l ∈ Finset.range n, E n l z * iteratedDeriv l f z
          - ∑ r : Fin n, A r z * ∑ l ∈ Finset.range n, E r l z * iteratedDeriv l f z := by
      simp only [ha', sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (s := Finset.range n)]
      congr 1
      · exact Finset.sum_congr rfl fun l _ => by ring
      · exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e1]
    linear_combination h
  -- the jet matrices
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun l j => iteratedDeriv l (g j) z₀ with hMdef
  set Lm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun m l => E m l z₀ with hLm
  have hWM : (Matrix.of fun (m j : Fin n) => amSerreIter m (g j) z₀) = Lm * M := by
    ext m j
    rw [Matrix.of_apply, Matrix.mul_apply, hexpN (g j) (hg j) m m.isLt z₀ hz₀,
      ← Fin.sum_univ_eq_sum_range (fun l => E m l z₀ * iteratedDeriv l (g j) z₀)]
    rfl
  have hM : M.det ≠ 0 := by
    intro h; apply hW; rw [hWM, Matrix.det_mul, h, mul_zero]
  set v : Fin n → ℂ := fun l => iteratedDeriv l y z₀ with hv
  set c : Fin n → ℂ := Matrix.mulVec M⁻¹ v with hcdef
  have hc : Matrix.mulVec M c = v := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  refine ⟨c, ?_⟩
  -- the difference
  set F : ℂ → ℂ := fun z => y z - ∑ j, c j * g j z with hF
  have hyD : DifferentiableOn ℂ y (imGT 0) := fun w hw =>
    (hy w hw).differentiableAt.differentiableWithinAt
  have hgD : ∀ j, DifferentiableOn ℂ (g j) (imGT 0) := fun j w hw =>
    (hg j w hw).differentiableAt.differentiableWithinAt
  have hsumD : DifferentiableOn ℂ (fun t => ∑ j, c j * g j t) (imGT 0) := by
    intro w hw
    exact (Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ
      (f := fun j t => c j * g j t) (c := w)
      (fun j _ => analyticAt_const.mul (hg j w hw))).differentiableAt.differentiableWithinAt
  have hFan : ∀ z ∈ imGT 0, AnalyticAt ℂ F z := fun z hz =>
    DifferentiableOn.analyticAt (hyD.sub hsumD) (hU.mem_nhds hz)
  have hDF : ∀ l, ∀ z ∈ imGT 0, iteratedDeriv l F z
      = iteratedDeriv l y z - ∑ j, c j * iteratedDeriv l (g j) z := by
    intro l z hz
    rw [hF, VOA.Huang.FrobeniusLog.iteratedDeriv_sub_on hU hyD hsumD l hz,
      VOA.Huang.FrobeniusLog.iteratedDeriv_sum_on hU Finset.univ c (fun j _ => hgD j) l hz]
  have hFode : ∀ z ∈ imGT 0, B z * κ ^ n * iteratedDeriv n F z
      + ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l F z = 0 := by
    intro z hz
    have hy0 := hconv y hy hyode z hz
    have hg0 : ∑ j, c j * (B z * κ ^ n * iteratedDeriv n (g j) z
        + ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l (g j) z) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hconv (g j) (hg j) (hgode j) z hz, mul_zero]
    have hsF : ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l F z
        = ∑ l ∈ Finset.range n,
          a' l z * (iteratedDeriv l y z - ∑ j, c j * iteratedDeriv l (g j) z) :=
      Finset.sum_congr rfl fun l _ => by rw [hDF l z hz]
    rw [hDF n z hz, hsF]
    have e1 : B z * κ ^ n * (iteratedDeriv n y z - ∑ j, c j * iteratedDeriv n (g j) z)
        = B z * κ ^ n * iteratedDeriv n y z
          - ∑ j, c j * (B z * κ ^ n * iteratedDeriv n (g j) z) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ l ∈ Finset.range n,
        a' l z * (iteratedDeriv l y z - ∑ j, c j * iteratedDeriv l (g j) z)
        = ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l y z
          - ∑ j, c j * ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l (g j) z := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.range n)]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    have hg0' : ∑ j, c j * (B z * κ ^ n * iteratedDeriv n (g j) z)
        + ∑ j, c j * ∑ l ∈ Finset.range n, a' l z * iteratedDeriv l (g j) z = 0 := by
      rw [← Finset.sum_add_distrib, ← hg0]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    linear_combination hy0 - hg0'
  -- a ball around `z₀` inside the half-plane on which `B ≠ 0`
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball z₀ r ⊆ {t | B t ≠ 0} ∩ imGT 0 :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem
      ((hB z₀ hz₀).continuousAt.eventually_ne hB₀) (hU.mem_nhds hz₀))
  have hBV : ∀ t ∈ Metric.ball z₀ r, B t * κ ^ n ≠ 0 := fun t ht =>
    mul_ne_zero (hball ht).1 (pow_ne_zero n hκ0)
  have hVU : Metric.ball z₀ r ⊆ imGT 0 := fun t ht => (hball ht).2
  set a : ℕ → ℂ → ℂ := fun l t => a' l t / (B t * κ ^ n) with ha
  have haD : ∀ i < n, DifferentiableOn ℂ (a i) (Metric.ball z₀ r) := by
    intro i _
    refine DifferentiableOn.div ?_ ?_ hBV
    · exact fun t ht => (ha'an i t (hVU ht)).differentiableAt.differentiableWithinAt
    · exact fun t ht =>
        ((hB t (hVU ht)).differentiableAt.mul_const _).differentiableWithinAt
  have hFV : DifferentiableOn ℂ F (Metric.ball z₀ r) := fun t ht =>
    (hFan t (hVU ht)).differentiableAt.differentiableWithinAt
  have hodeV : ∀ t ∈ Metric.ball z₀ r, iteratedDeriv n F t
      + ∑ i ∈ Finset.range n, a i t * iteratedDeriv i F t = 0 := by
    intro t ht
    have h := hFode t (hVU ht)
    have hne := hBV t ht
    have : iteratedDeriv n F t + ∑ i ∈ Finset.range n, a i t * iteratedDeriv i F t
        = (B t * κ ^ n)⁻¹ * (B t * κ ^ n * iteratedDeriv n F t
          + ∑ l ∈ Finset.range n, a' l t * iteratedDeriv l F t) := by
      rw [mul_add, Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; simp only; rw [div_eq_inv_mul]; ring
    rw [this, h, mul_zero]
  have hjet : ∀ i < n, iteratedDeriv i F z₀ = 0 := by
    intro i hi
    rw [hDF i z₀ hz₀]
    have h := congrFun hc ⟨i, hi⟩
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.of_apply, hv] at h
    rw [← h]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hzero := VOA.Huang.FrobeniusLog.eqOn_zero_of_ode Metric.isOpen_ball
    (convex_ball z₀ r).isPreconnected haD hFV hodeV (Metric.mem_ball_self hr) hjet
  have hloc : F =ᶠ[𝓝 z₀] 0 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hr) hzero
  have hFan' : AnalyticOnNhd ℂ F (imGT 0) := hFan
  have hall := hFan'.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_imGT 0)
    hz₀ hloc
  intro z hz
  have := hall hz
  simp only [hF, Pi.zero_apply, sub_eq_zero] at this
  exact this

end VOA.Huang.AndersonMoore

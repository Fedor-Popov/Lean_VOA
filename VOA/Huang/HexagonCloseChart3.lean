import VOA.Huang.HexagonCloseChart2

/-! # Hexagon closure: Möbius charts for Fuchsian equations (VOA-free), part 3

The transformed equation and the chart continuation (see `HexagonCloseChart2`).
-/

noncomputable section
namespace VOA.Huang.TensorCat.HexagonClose
open Polynomial Filter Topology
open VOA.Huang.FrobeniusLog (psEval logFun halfPlane LogGood LogFuchsianEq)
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.FuchsianODE
open scoped BigOperators

/-- The coefficients of the transformed equation:
`ĉⱼ = (1-v)^{-s} (P_{s,j} + Σ_{i<s} Cq_i P_{i,j})`. -/
def cHat (q : ℂ) (b : ℕ) (p : ℕ → ℂ[X]) (s j : ℕ) : PowerSeries ℂ :=
  geomA 1 ^ s * ((Pk s j : PowerSeries ℂ) +
    ∑ i ∈ Finset.range s, Cq q b p i * (Pk i j : PowerSeries ℂ))

theorem cHat_mem {q : ℂ} (hq1 : ‖1 - q‖ ≤ 1) (b : ℕ) (p : ℕ → ℂ[X]) (s j : ℕ) :
    cHat q b p s j ∈ SubexpPS := by
  unfold cHat
  refine SubexpPS.mul_mem (SubexpPS.pow_mem (geomA_mem (by simp)) s)
    (SubexpPS.add_mem (polynomial_mem_subexpPS _) (SubexpPS.sum_mem fun i _ => ?_))
  exact SubexpPS.mul_mem (Cq_mem b p hq1 i) (polynomial_mem_subexpPS _)

theorem psEval_cHat {q : ℂ} (hq1 : ‖1 - q‖ ≤ 1) (b : ℕ) (p : ℕ → ℂ[X]) (s j : ℕ) {v : ℂ}
    (hv : ‖v‖ < 1) :
    psEval (cHat q b p s j) v = ((1 - v) ^ s)⁻¹ * ((Pk s j).eval v +
      ∑ i ∈ Finset.range s, psEval (Cq q b p i) v * (Pk i j).eval v) := by
  have h1v' : ‖(1 : ℂ) * v‖ < 1 := by rwa [one_mul]
  have hsum : ∀ i ∈ Finset.range s, Cq q b p i * (Pk i j : PowerSeries ℂ) ∈ SubexpPS :=
    fun i _ => SubexpPS.mul_mem (Cq_mem b p hq1 i) (polynomial_mem_subexpPS _)
  unfold cHat
  rw [psEval_mul (SubexpPS.pow_mem (geomA_mem (by simp)) s)
      (SubexpPS.add_mem (polynomial_mem_subexpPS _) (SubexpPS.sum_mem hsum)) hv,
    psEval_pow (geomA_mem (by simp)) hv, psEval_geomA h1v', one_mul, inv_pow,
    psEval_add (polynomial_mem_subexpPS _) (SubexpPS.sum_mem hsum) hv, psEval_coe,
    psEval_sum _ hsum hv]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [psEval_mul (Cq_mem b p hq1 i) (polynomial_mem_subexpPS _) hv, psEval_coe]

/-- `logFun λ (G as constants) σ = e^{λσ} G(e^σ)`. -/
theorem logFun_const_eq (lam : ℂ) (G : PowerSeries ℂ) (σ : ℂ) :
    logFun lam (fun n => Polynomial.C (PowerSeries.coeff n G)) σ =
      Complex.exp (lam * σ) * psEval G (Complex.exp σ) := by
  rw [logFun, psEval, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [eval_C, ← Complex.exp_nat_mul, add_mul, Complex.exp_add]
  ring

/-- The radius of the comparison region: `M = log(2 + 2|q|)`. -/
def chartM (q : ℂ) : ℝ := Real.log (2 + 2 * ‖q‖)

theorem chartX_small {q τ : ℂ} (hτ : τ.re < -chartM q) :
    ‖Complex.exp τ‖ < 1 / 2 ∧ ‖chartX q (Complex.exp τ)‖ < 1 := by
  have hq : 0 ≤ ‖q‖ := norm_nonneg q
  have hv : ‖Complex.exp τ‖ < 1 / (2 + 2 * ‖q‖) := by
    rw [Complex.norm_exp]
    calc Real.exp τ.re < Real.exp (-chartM q) := Real.exp_lt_exp.2 hτ
      _ = 1 / (2 + 2 * ‖q‖) := by
        rw [chartM, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hv2 : ‖Complex.exp τ‖ < 1 / 2 := lt_of_lt_of_le hv (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  refine ⟨hv2, ?_⟩
  set v := Complex.exp τ
  have h1v : 1 / 2 < ‖1 - v‖ := by
    have := norm_sub_norm_le (1 : ℂ) v
    rw [norm_one] at this
    linarith
  rw [chartX, norm_div, norm_mul, norm_neg, div_lt_one (by linarith)]
  have : ‖q‖ * ‖v‖ ≤ ‖q‖ * (1 / (2 + 2 * ‖q‖)) := mul_le_mul_of_nonneg_left hv.le hq
  have h2 : ‖q‖ * (1 / (2 + 2 * ‖q‖)) < 1 / 2 := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]; linarith
  linarith

theorem sigmaQ_re_neg {q τ : ℂ} (hq0 : q ≠ 0) (hτ : τ.re < -chartM q) :
    (sigmaQ q τ).re < 0 := by
  have hM : 0 ≤ chartM q := Real.log_nonneg (by linarith [norm_nonneg q])
  have hτ0 : τ.re < 0 := by linarith
  have h := (chartX_small hτ).2
  rw [chartX, ← exp_sigmaQ hq0 hτ0, Complex.norm_exp] at h
  exact Real.exp_lt_one_iff.1 h

/-- **The transformed equation**: `H = g ∘ σ_q`, `g(σ) = e^{λσ} G(e^σ)`, satisfies
`H^{(s)} + Σ_{j<s} ĉⱼ(e^τ) H^{(j)} = 0` on `Re τ < -M`. -/
theorem tau_ode {lam : ℂ} {s b : ℕ} {c : ℕ → PowerSeries ℂ} {p : ℕ → ℂ[X]}
    (hcp : ∀ i < s, (1 - PowerSeries.X) ^ b * c i = (p i : PowerSeries ℂ)) {G : PowerSeries ℂ}
    (hG : FuchsianEq lam s c G) {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖1 - q‖ ≤ 1) :
    ∀ τ ∈ {τ : ℂ | τ.re < -chartM q},
      iteratedDeriv s (fun τ => logFun lam (fun n => Polynomial.C (PowerSeries.coeff n G))
          (sigmaQ q τ)) τ +
        ∑ j ∈ Finset.range s, psEval (cHat q b p s j) (Complex.exp τ) *
          iteratedDeriv j (fun τ => logFun lam (fun n => Polynomial.C (PowerSeries.coeff n G))
            (sigmaQ q τ)) τ = 0 := by
  intro τ hτ
  have hτ : τ.re < -chartM q := hτ
  have hM : 0 ≤ chartM q := Real.log_nonneg (by linarith [norm_nonneg q])
  have hc : ∀ i < s, c i ∈ SubexpPS := fun i hi =>
    mem_subexpPS_of_mul_eq' (a := 1) (by simp) (by simpa using hcp i hi)
  have hGsub : G ∈ SubexpPS := mem_subexpPS.2 (subexponential_of_fuchsianEq hc hG)
  have hGood := VOA.Huang.FrobeniusLog.logGood_const hGsub
  have hLF := VOA.Huang.AssocExpansion.logFuchsianEq_const_of_fuchsianEq hG
  set g := logFun lam (fun n => Polynomial.C (PowerSeries.coeff n G)) with hg
  set H : ℂ → ℂ := fun τ => g (sigmaQ q τ) with hH
  set U : Set ℂ := {τ : ℂ | τ.re < -chartM q} with hU
  have hUo : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUneg : ∀ t ∈ U, t.re < 0 := fun t ht => by have : t.re < -chartM q := ht; linarith
  have hUV : ∀ t ∈ U, sigmaQ q t ∈ halfPlane := fun t ht => sigmaQ_re_neg hq0 ht
  have hgd : DifferentiableOn ℂ g halfPlane :=
    VOA.Huang.FrobeniusLog.differentiableOn_logFun hGood lam
  have hHd : DifferentiableOn ℂ H U := fun t ht =>
    ((hgd.differentiableAt (VOA.Huang.FrobeniusLog.isOpen_halfPlane.mem_nhds (hUV t ht))).comp
      t ((hasDerivAt_sigmaQ q (hUneg t ht)).differentiableAt)).differentiableWithinAt
  -- the equation in `σ`
  have hode := VOA.Huang.FrobeniusLog.logFun_ode hc hGood hLF (hUV τ hτ)
  have hcomp := fun i => Lpow_comp hUo hUneg VOA.Huang.FrobeniusLog.isOpen_halfPlane hUV hgd i
    τ hτ
  have hexp := Lpow_eq hUo hHd
  set v := Complex.exp τ with hv
  set D : ℕ → ℂ := fun j => iteratedDeriv j H τ with hD
  have hsmall := chartX_small hτ
  have hv1 : ‖v‖ < 1 := by linarith [hsmall.1]
  have hxeq : Complex.exp (sigmaQ q τ) = chartX q v := by
    rw [exp_sigmaQ hq0 (hUneg τ hτ), chartX]
  have e_i : ∀ i, iteratedDeriv i g (sigmaQ q τ) =
      ∑ j ∈ Finset.range (i + 1), (Pk i j).eval v * D j := fun i => by
    rw [← hcomp i, hexp i τ hτ]
  have hode' : iteratedDeriv s g (sigmaQ q τ) + ∑ i ∈ Finset.range s,
      psEval (c i) (Complex.exp (sigmaQ q τ)) * iteratedDeriv i g (sigmaQ q τ) = 0 := hode
  simp_rw [e_i] at hode'
  rw [hxeq] at hode'
  clear hode
  rename_i hode0
  have hode := hode'
  clear hode'
  -- rewrite the coefficients
  have hC : ∀ i ∈ Finset.range s, psEval (c i) (chartX q v) = psEval (Cq q b p i) v :=
    fun i hi => (psEval_Cq b p hq1 (hcp i (Finset.mem_range.1 hi)) hv1 hsmall.2).symm
  -- extend the inner sums
  have hext : ∀ i ∈ Finset.range s, ∑ j ∈ Finset.range (i + 1), (Pk i j).eval v * D j =
      ∑ j ∈ Finset.range s, (Pk i j).eval v * D j := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_
    rw [Finset.mem_range] at hj hj'
    rw [Pk_eq_zero_of_lt (by omega), eval_zero, zero_mul]
  have hsum2 : ∑ i ∈ Finset.range s, psEval (c i) (chartX q v) *
      ∑ j ∈ Finset.range (i + 1), (Pk i j).eval v * D j =
      ∑ i ∈ Finset.range s, psEval (Cq q b p i) v *
        ∑ j ∈ Finset.range s, (Pk i j).eval v * D j :=
    Finset.sum_congr rfl fun i hi => by rw [hC i hi, hext i hi]
  have hfirst : ∑ j ∈ Finset.range (s + 1), (Pk s j).eval v * D j =
      ∑ j ∈ Finset.range s, (Pk s j).eval v * D j + (1 - v) ^ s * D s := by
    rw [Finset.sum_range_succ, Pk_self, eval_pow, eval_sub, eval_one, eval_X]
  rw [hsum2, hfirst] at hode
  have h1v : (1 - v) ^ s ≠ 0 := pow_ne_zero _ (by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hv1; simp at hv1)
  have key : (1 - v) ^ s * (D s + ∑ j ∈ Finset.range s, psEval (cHat q b p s j) v * D j) =
      ∑ j ∈ Finset.range s, (Pk s j).eval v * D j + (1 - v) ^ s * D s +
        ∑ i ∈ Finset.range s, psEval (Cq q b p i) v *
          ∑ j ∈ Finset.range s, (Pk i j).eval v * D j := by
    rw [mul_add, Finset.mul_sum]
    have e1 : ∀ j ∈ Finset.range s, (1 - v) ^ s * (psEval (cHat q b p s j) v * D j) =
        ((Pk s j).eval v + ∑ i ∈ Finset.range s, psEval (Cq q b p i) v * (Pk i j).eval v)
          * D j := by
      intro j _
      rw [psEval_cHat hq1 b p s j hv1, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h1v, one_mul]
    rw [Finset.sum_congr rfl e1]
    have e2 : ∑ j ∈ Finset.range s, ((Pk s j).eval v +
        ∑ i ∈ Finset.range s, psEval (Cq q b p i) v * (Pk i j).eval v) * D j =
        ∑ j ∈ Finset.range s, (Pk s j).eval v * D j +
          ∑ i ∈ Finset.range s, psEval (Cq q b p i) v *
            ∑ j ∈ Finset.range s, (Pk i j).eval v * D j := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    ring
  have hzero : (1 - v) ^ s * (D s + ∑ j ∈ Finset.range s, psEval (cHat q b p s j) v * D j) =
      0 := by rw [key]; exact hode
  exact (mul_eq_zero.1 hzero).resolve_left h1v

/-- **Chart continuation**: for a formal solution `G` of a Fuchsian equation with
coefficients rational with poles only at `x = 1`, and `q ≠ 0`, `|1 - q| ≤ 1`, the function
`τ ↦ G(-q e^τ/(1 - e^τ))` (defined for `Re τ ≪ 0`) continues holomorphically to `Re τ < 0`. -/
theorem chart_continuation {lam : ℂ} {s b : ℕ} {c : ℕ → PowerSeries ℂ} {p : ℕ → ℂ[X]}
    (hcp : ∀ i < s, (1 - PowerSeries.X) ^ b * c i = (p i : PowerSeries ℂ)) {G : PowerSeries ℂ}
    (hG : FuchsianEq lam s c G) {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖1 - q‖ ≤ 1) :
    ∃ Gh : ℂ → ℂ, DifferentiableOn ℂ Gh halfPlane ∧
      ∀ τ : ℂ, τ.re < -chartM q → Gh τ = psEval G (chartX q (Complex.exp τ)) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hG0 : G = 0 := by simpa [FuchsianEq] using hG
    refine ⟨fun _ => 0, differentiableOn_const 0, fun τ _ => ?_⟩
    rw [hG0]; simp [VOA.Huang.FrobeniusLog.psEval]
  have hc : ∀ i < s, c i ∈ SubexpPS := fun i hi =>
    mem_subexpPS_of_mul_eq' (a := 1) (by simp) (by simpa using hcp i hi)
  have hGsub : G ∈ SubexpPS := mem_subexpPS.2 (subexponential_of_fuchsianEq hc hG)
  have hGood := VOA.Huang.FrobeniusLog.logGood_const hGsub
  have hM : 0 ≤ chartM q := Real.log_nonneg (by linarith [norm_nonneg q])
  set g := logFun lam (fun n => Polynomial.C (PowerSeries.coeff n G)) with hg
  set U : Set ℂ := {τ : ℂ | τ.re < -chartM q} with hU
  have hUo : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUneg : ∀ t ∈ U, t.re < 0 := fun t ht => by have : t.re < -chartM q := ht; linarith
  have hgd : DifferentiableOn ℂ g halfPlane :=
    VOA.Huang.FrobeniusLog.differentiableOn_logFun hGood lam
  have hHd : DifferentiableOn ℂ (fun τ => g (sigmaQ q τ)) U := fun t ht =>
    ((hgd.differentiableAt (VOA.Huang.FrobeniusLog.isOpen_halfPlane.mem_nhds
      (sigmaQ_re_neg hq0 ht))).comp t
      ((hasDerivAt_sigmaQ q (hUneg t ht)).differentiableAt)).differentiableWithinAt
  have hUc : IsPreconnected U :=
    (convex_halfSpace_lt (f := fun z : ℂ => z.re) ⟨fun x y => by simp, fun a x => by simp⟩
      _).isPreconnected
  have hUH : U ⊆ halfPlane := fun t ht => hUneg t ht
  have hUne : U.Nonempty := ⟨(-chartM q - 1 : ℝ), by
    change ((-chartM q - 1 : ℝ) : ℂ).re < -chartM q; simp⟩
  obtain ⟨ι, hι, lam', p', a', -, hLF, -, hrep⟩ :=
    VOA.Huang.FrobeniusLog.fundamental_system hs (fun j _ => cHat_mem hq1 b p s j) hUo hUc hUH
      hUne hHd (tau_ode hcp hG hq0 hq1)
  have hgood' : ∀ j, LogGood (p' j) := fun j =>
    VOA.Huang.FrobeniusLog.logGood_of_logFuchsianEq hs (fun i _ => cHat_mem hq1 b p s i) (hLF j)
  refine ⟨fun τ => Complex.exp (-lam * sigmaQ q τ) *
    ∑ j, a' j * logFun (lam' j) (p' j) τ, ?_, fun τ hτ => ?_⟩
  · intro τ hτ
    have hτ : τ.re < 0 := hτ
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact ((hasDerivAt_sigmaQ q hτ).differentiableAt.const_mul _).cexp
    · refine DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_
      exact (VOA.Huang.FrobeniusLog.differentiableOn_logFun (hgood' j) _).differentiableAt
        (VOA.Huang.FrobeniusLog.isOpen_halfPlane.mem_nhds hτ)
  · have h := hrep τ hτ
    simp only at h
    dsimp only
    rw [← h, hg, logFun_const_eq, ← mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel,
      Complex.exp_zero, one_mul, exp_sigmaQ hq0 (hUneg τ hτ), chartX]

end VOA.Huang.TensorCat.HexagonClose

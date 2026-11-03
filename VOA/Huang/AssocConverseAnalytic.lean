import VOA.Huang.AssocConverseIsotypic

/-! # Uniqueness of product expansions on the real overlap

Coefficient uniqueness is applied after grouping coincident exponents by the
existing log-expansion uniqueness theorem. No distinct-weight assumption is used.
-/

namespace VOA.Huang.AssocConverse
open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff
open scoped BigOperators
open Filter Topology

/-- A real interval inside the left half-plane suffices for coefficient
uniqueness of a finite sum of convergent log-series. -/
theorem log_coeff_zero_of_real_interval {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (p : ι → ℕ → Polynomial ℂ) (hp : ∀ j, LogGood (p j))
    {a : ℝ} (ha : a < 0)
    (hz : ∀ t : ℝ, a < t → t < 0 → ∑ j, logFun (lam j) (p j) t = 0) :
    ∀ μ k, ∑ j, exCoeff (lam j) (p j) μ k = 0 := by
  let F : ℂ → ℂ := fun t => ∑ j, logFun (lam j) (p j) t
  have hF : AnalyticOnNhd ℂ F halfPlane := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_halfPlane
    have hh := DifferentiableOn.sum fun j (_ : j ∈ Finset.univ) =>
      differentiableOn_logFun (hp j) (lam j)
    exact hh.congr (fun t _ => by simp [F])
  let t : ℕ → ℝ := fun n => a / 2 + (-a / 4) * (1 / ((n : ℝ) + 1))
  have htpos (n : ℕ) : 0 < (-a / 4) * (1 / ((n : ℝ) + 1)) := by
    exact mul_pos (by linarith) (by positivity)
  have htle (n : ℕ) : (-a / 4) * (1 / ((n : ℝ) + 1)) ≤ -a / 4 := by
    have hh : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hlim : Tendsto (fun n => (t n : ℂ)) atTop (𝓝[≠] ((a / 2 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 : Tendsto t atTop (𝓝 (a / 2)) := by
        simpa only [mul_zero, add_zero] using
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-a / 4)).const_add (a / 2)
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp h0
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      have he' := Complex.ofReal_injective he
      change a / 2 + _ = a / 2 at he'
      linarith [htpos n]
  have hfreq : ∃ᶠ z in 𝓝[≠] ((a / 2 : ℝ) : ℂ), F z = (0 : ℂ → ℂ) z :=
    hlim.frequently (Frequently.of_forall fun n =>
      hz (t n) (by dsimp [t]; linarith [htpos n]) (by dsimp [t]; linarith [htle n]))
  have he := hF.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_halfPlane (show ((a / 2 : ℝ) : ℂ) ∈ halfPlane by
      change a / 2 < 0; linarith) hfreq
  exact coeff_eq_zero_of_eval_eq_zero Finset.univ lam p (fun j _ => hp j)
    (fun t ht => he ht)

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- The exponent coefficient of the canonical product expansion is its actual
matrix coefficient on the weight line, including modes outside the support. -/
theorem exCoeff_product_eq
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (p q : ℂ)
    (hpq : p + q = d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) :
    exCoeff (d.α₁ + Q.h - d.h₄)
      (fun k => Polynomial.C (prodCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₂ + d.α₃ - 1 - Q.h) + k)
        (d.α₂ + d.α₃ - 1 - Q.h - k))) (p + 1) 0 =
      prodCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃ p q := by
  classical
  by_cases h : ∃ k : ℕ, d.α₁ + Q.h - d.h₄ + k = p + 1
  · obtain ⟨k, hk⟩ := h
    rw [← hk, exCoeff_C]
    simp only [ite_true]
    congr 1
    · linear_combination hk
    · linear_combination -hk - hpq
  · rw [exCoeff_of_forall_ne (fun k hk => h ⟨k, hk⟩)]
    symm
    have hz : B.val q d.w₂ d.w₃ = 0 := by
      have hw := VOA.Huang.FusionTop.mem_weight B.property d.hw₂ d.hw₃ q
      by_contra hn
      have hb : Q.isMod.weight (d.α₂ + d.α₃ - q - 1) ≠ ⊥ := by
        intro he; rw [he, Submodule.mem_bot] at hw; exact hn hw
      obtain ⟨k, hk⟩ := Q.isLow _ hb
      exact h ⟨k, by linear_combination -hpq - hk⟩
    simp [prodCoeff, hz]

/-- On the real product region, the value is the log-series in the reciprocal
coordinate. This is an equality of the existing sums, with the canonical base. -/
theorem productValue_eq_logFun
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) :
    productValue A B d = logFun (d.α₁ + Q.h - d.h₄)
      (fun k => Polynomial.C (prodCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₂ + d.α₃ - 1 - Q.h) + k)
        (d.α₂ + d.α₃ - 1 - Q.h - k))) (-Complex.log (1 + (d.x : ℂ))) := by
  unfold productValue logFun
  apply tsum_congr
  intro k
  have hn : 1 + (d.x : ℂ) ≠ 0 := by
    have hr : 0 < 1 + d.x := by linarith [d.xpos]
    exact_mod_cast hr.ne'
  simp only [productTerm, Complex.one_cpow, mul_one, Polynomial.eval_C,
    Complex.cpow_def_of_ne_zero hn]
  rw [mul_comm]
  congr 2
  ring

/-- Analytic vanishing of a finite sum of product channels implies vanishing
of its matrix coefficients on every pair of modes. Channels may repeat. -/
theorem product_coefficients_zero_of_values_zero {ι : Type v} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W)
    (A : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod P₄.isMod)
    (B : ∀ j, IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (d : TestData P₁ P₂ P₃ P₄)
    (hz : ∀ (x : ℝ) (hx : 0 < x) (hx' : x < 1),
      ∑ j, productValue (A j) (B j) { d with x := x, xpos := hx, xlt := hx' } = 0)
    (p q : ℂ) : ∑ j, prodCoeff (A j).val (B j).val d.f d.w₁ d.w₂ d.w₃ p q = 0 := by
  classical
  by_cases hpq : p + q = d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2
  · let lam : ι → ℂ := fun j => d.α₁ + (R j).h - d.h₄
    let c : ι → ℕ → Polynomial ℂ := fun j k => Polynomial.C
      (prodCoeff (A j).val (B j).val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₂ + d.α₃ - 1 - (R j).h) + k)
        (d.α₂ + d.α₃ - 1 - (R j).h - k))
    have hc (j : ι) : LogGood (c j) := by
      have hh := logGood_const (prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄
        (A j).property (B j).property d.hw₁ d.hw₂ d.hw₃ d.hf)
      simpa only [coeff_prodSeries] using hh
    have he : ∀ μ k, ∑ j, exCoeff (lam j) (c j) μ k = 0 := by
      apply log_coeff_zero_of_real_interval lam c hc
        (a := -Real.log 2) (neg_neg_of_pos (Real.log_pos (by norm_num)))
      intro t ht ht0
      let x := Real.exp (-t) - 1
      have hx : 0 < x := by
        have hh := Real.one_lt_exp_iff.mpr (neg_pos.mpr ht0)
        dsimp [x]; linarith
      have hx' : x < 1 := by
        have hh : Real.exp (-t) < 2 := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_lt_exp]
          linarith
        dsimp [x]; linarith
      have hh := hz x hx hx'
      have hlog : -Complex.log (1 + (x : ℂ)) = (t : ℂ) := by
        have heq : 1 + (x : ℂ) = Complex.exp (- (t : ℂ)) := by
          rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
          dsimp [x]; push_cast; ring
        rw [heq, Complex.log_exp]
        · simp
        · simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]; linarith [Real.pi_pos]
        · simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]; exact Real.pi_pos.le
      simpa only [productValue_eq_logFun, hlog] using hh
    have hh := he (p + 1) 0
    simpa only [lam, c, exCoeff_product_eq _ _ d p q hpq] using hh
  · exact Finset.sum_eq_zero fun j _ => prodCoeff_eq_zero_of_ne
      (A j).property (B j).property d.hw₁ d.hw₂ d.hw₃ d.hf hpq

end VOA.Huang.AssocConverse

import VOA.Huang.TensorCatIrreducible

/-! # Uniqueness of finite sums of iterate coefficients

The existing log-series uniqueness theorem groups coincident exponents.
The real overlap interval therefore determines every coefficient, even when
several intermediate modules have the same lowest weight modulo integers.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open VOA.Huang.AssocConverse VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff
open VOA.Huang.PzTensorHatBridge VOA.Huang.PzTensorY3
open scoped BigOperators
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- The exponent coefficient of an iterate is its actual scalar mode coefficient. -/
theorem exCoeff_iterate_eq
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (p q : ℂ)
    (hpq : p + q = d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) :
    exCoeff (Q.h - d.α₁ - d.α₂)
      (fun k => Polynomial.C (iterCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ - 1 - Q.h - k)
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₁ + d.α₂ - 1 - Q.h) + k)))
      (-p - 1) 0 = iterCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃ p q := by
  classical
  by_cases h : ∃ k : ℕ, Q.h - d.α₁ - d.α₂ + k = -p - 1
  · obtain ⟨k, hk⟩ := h
    rw [← hk, exCoeff_C]
    simp only [ite_true]
    congr 1
    · linear_combination -hk
    · linear_combination hk - hpq
  · rw [exCoeff_of_forall_ne (fun k hk => h ⟨k, hk⟩)]
    symm
    have hz : B.val p d.w₁ d.w₂ = 0 := by
      have hw := VOA.Huang.FusionTop.mem_weight B.property d.hw₁ d.hw₂ p
      by_contra hn
      have hb : Q.isMod.weight (d.α₁ + d.α₂ - p - 1) ≠ ⊥ := by
        intro he; rw [he, Submodule.mem_bot] at hw; exact hn hw
      obtain ⟨k, hk⟩ := Q.isLow _ hb
      exact h ⟨k, by linear_combination -hk⟩
    simp [iterCoeff, hz]

/-- The iterate value is a convergent log-free series at log of its coordinate. -/
theorem iterateValue_eq_logFun
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) :
    iterateValue A B d = logFun (Q.h - d.α₁ - d.α₂)
      (fun k => Polynomial.C (iterCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ - 1 - Q.h - k)
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₁ + d.α₂ - 1 - Q.h) + k)))
      (Complex.log (d.x : ℂ)) := by
  unfold iterateValue logFun
  apply tsum_congr
  intro k
  have hn : (d.x : ℂ) ≠ 0 := by exact_mod_cast d.xpos.ne'
  simp only [iterateTerm, Complex.one_cpow, mul_one, Polynomial.eval_C,
    Complex.cpow_def_of_ne_zero hn]
  rw [mul_comm]
  congr 2
  ring

/-- Scalar uniqueness for any finite family of iterate channels. -/
theorem iterate_coefficients_zero_of_values_zero {ι : Type v} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W)
    (A : ∀ j, IntertwiningOperator (R j).isMod P₃.isMod P₄.isMod)
    (B : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod)
    (d : TestData P₁ P₂ P₃ P₄)
    (hz : ∀ (x : ℝ) (hx : 0 < x) (hx' : x < 1),
      ∑ j, iterateValue (A j) (B j) { d with x := x, xpos := hx, xlt := hx' } = 0)
    (p q : ℂ) : ∑ j, iterCoeff (A j).val (B j).val d.f d.w₁ d.w₂ d.w₃ p q = 0 := by
  classical
  by_cases hpq : p + q = d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2
  · let lam : ι → ℂ := fun j => (R j).h - d.α₁ - d.α₂
    let c : ι → ℕ → Polynomial ℂ := fun j k => Polynomial.C
      (iterCoeff (A j).val (B j).val d.f d.w₁ d.w₂ d.w₃
        (d.α₁ + d.α₂ - 1 - (R j).h - k)
        (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2 - (d.α₁ + d.α₂ - 1 - (R j).h) + k))
    have hc (j : ι) : LogGood (c j) := by
      have hh := logGood_const (VOA.Huang.AssocCoeffReduction.iterSeries_mem_subexpPS hV i₁ i₂ i₃ i₄
        (A j).property (B j).property d.hw₁ d.hw₂ d.hw₃ d.hf)
      simpa only [coeff_iterSeries] using hh
    have he : ∀ μ k, ∑ j, exCoeff (lam j) (c j) μ k = 0 := by
      apply log_coeff_zero_of_real_interval lam c hc (a := -1) (by norm_num)
      intro t _ ht0
      have hx : 0 < Real.exp t := Real.exp_pos t
      have hx' : Real.exp t < 1 := Real.exp_lt_one_iff.mpr ht0
      have hh := hz (Real.exp t) hx hx'
      have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
        rw [Complex.ofReal_exp, Complex.log_exp]
        · simp only [Complex.ofReal_im]; linarith [Real.pi_pos]
        · simp only [Complex.ofReal_im]; exact Real.pi_pos.le
      simpa only [iterateValue_eq_logFun, hlog] using hh
    have hh := he (-p - 1) 0
    simpa only [lam, c, exCoeff_iterate_eq _ _ d p q hpq] using hh
  · exact Finset.sum_eq_zero fun j _ => iterCoeff_eq_zero_of_ne
      (A j).property (B j).property d.hw₁ d.hw₂ d.hw₃ d.hf hpq

/-- All vector-valued iterate coefficients are determined by the scalar tests. -/
theorem formal_iterates_zero_of_values_zero {ι : Type v} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W)
    (A : ∀ j, IntertwiningOperator (R j).isMod P₃.isMod P₄.isMod)
    (B : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod)
    (hv : ∀ d : TestData P₁ P₂ P₃ P₄, ∑ j, iterateValue (A j) (B j) d = 0)
    (p q : ℂ) (x : P₁.carrier) (y : P₂.carrier) (z : P₃.carrier) :
    ∑ j, (A j).val q ((B j).val p x y) z = 0 := by
  classical
  let G : P₁.carrier → P₂.carrier → P₃.carrier → P₄.carrier :=
    fun x y z => ∑ j, (A j).val q ((B j).val p x y) z
  have h1 : ∀ x x' y z, G (x + x') y z = G x y z + G x' y z := by
    intros; simp [G, map_add, Finset.sum_add_distrib]
  have h2 : ∀ x y y' z, G x (y + y') z = G x y z + G x y' z := by
    intros; simp [G, map_add, Finset.sum_add_distrib]
  have h3 : ∀ x y z z', G x y (z + z') = G x y z + G x y z' := by
    intros; simp [G, map_add, Finset.sum_add_distrib]
  have hhom (α₁ α₂ α₃ : ℂ) (x : P₁.carrier) (y : P₂.carrier) (z : P₃.carrier)
      (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
      (hz : z ∈ P₃.isMod.weight α₃) : G x y z = 0 := by
    apply eq_zero_of_supported
    intro h₄ f hf
    let d : TestData P₁ P₂ P₃ P₄ :=
      ⟨α₁, α₂, α₃, h₄, x, y, z, f, hx, hy, hz, hf, 1 / 2, by norm_num, by norm_num⟩
    have hh := iterate_coefficients_zero_of_values_zero hV i₁ i₂ i₃ i₄ R A B d
      (fun s hs hs' => hv { d with x := s, xpos := hs, xlt := hs' }) p q
    simpa only [G, map_sum, iterCoeff, d] using hh
  have hxy (α : ℂ) (z : P₃.carrier) (hz : z ∈ P₃.isMod.weight α) :
      ∀ x y, G x y z = 0 :=
    eq_zero_of_homog (fun x y => G x y z) (fun x x' y => h1 x x' y z)
      (fun x y y' => h2 x y y' z) (fun a b x y hx hy => hhom a b α x y z hx hy hz)
  change G x y z = 0
  refine Submodule.iSup_induction P₃.isMod.weight (motive := fun z => G x y z = 0)
    (mem_iSup_weight P₃ z) ?_ ?_ ?_
  · intro α z hz; exact hxy α z hz x y
  · simp [G]
  · intro z z' hz hz'; rw [h3, hz, hz', add_zero]

end VOA.Huang.TensorCat

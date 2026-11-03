import VOA.DeligneAudit.D4CharLeviHilb

/-! Polynomial representatives and their elementary type-A total counts. -/

namespace VOA.DeligneAudit.D4Char

open Polynomial VOA.DeligneGaussian
open scoped BigOperators

noncomputable section

/-- Polynomial representative of the GL4 coefficient function. -/
def gl4Poly (l₁ l₂ l₃ l₄ : ℕ) : ℚ[X] :=
  ∑ m₁ ∈ Finset.Icc l₂ l₁, ∑ m₂ ∈ Finset.Icc l₃ l₂,
    ∑ m₃ ∈ Finset.Icc l₄ l₃,
      qbinom X (l₁ - l₂) (l₁ - m₁) * qbinom X (l₂ - l₃) (l₂ - m₂) *
        qbinom X (l₃ - l₄) (l₃ - m₃) * A2.gl3Poly m₁ m₂ m₃

theorem coeff_gl4Poly (l₁ l₂ l₃ l₄ N : ℕ) :
    (gl4Poly l₁ l₂ l₃ l₄).coeff N = (gl4Hilb l₁ l₂ l₃ l₄ N : ℚ) := by
  simp only [gl4Poly, gl4Hilb, finsetSum_coeff, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
    Finset.sum_congr rfl fun m₃ _ => ?_
  exact A2.coeff_mul_eq_convQ
    (fun M => A2.coeff_mul_eq_convQ
      (fun L => A2.coeff_mul_eq_convQ
        (A2.coeff_qbinom_X _ _) (A2.coeff_qbinom_X _ _) L)
      (A2.coeff_qbinom_X _ _) M)
    (A2.coeff_gl3Poly _ _ _) N

/-- Binomial theorem with the interval indexing used by GT branching. -/
theorem interval_binomial (lo hi : ℕ) (h : lo ≤ hi) (x y : ℚ) :
    (∑ i ∈ Finset.Icc lo hi,
      ((hi - lo).choose (hi - i) : ℚ) * x ^ (hi - i) * y ^ (i - lo)) =
      (x + y) ^ (hi - lo) := by
  rw [A2.sum_Icc_eq_sum_range lo hi h, add_pow]
  refine Finset.sum_congr rfl fun i hi' => ?_
  have hi' := Finset.mem_range.mp hi'
  rw [show hi - (hi - i) = i by omega,
    show hi - i - lo = hi - lo - i by omega]
  ring

/-- All GL3 highest weights, not only the diagonal weight used by the A2 endpoint. -/
theorem gl3Poly_eval_one (l₁ l₂ l₃ : ℕ) (h₁ : l₂ ≤ l₁) (h₂ : l₃ ≤ l₂) :
    (A2.gl3Poly l₁ l₂ l₃).eval 1 = 3 ^ (l₁ - l₃) := by
  rw [A2.gl3Poly, eval_finsetSum]
  simp only [eval_finsetSum, eval_mul, A2.eval_one_qbinom]
  have ht : ∀ m₁ ∈ Finset.Icc l₂ l₁, ∀ m₂ ∈ Finset.Icc l₃ l₂,
      ((l₁ - l₂).choose (l₁ - m₁) : ℚ) *
        ((l₂ - l₃).choose (l₂ - m₂) : ℚ) * (A2.gl2Poly m₁ m₂).eval 1 =
      (((l₁ - l₂).choose (l₁ - m₁) : ℚ) * 1 ^ (l₁ - m₁) *
        2 ^ (m₁ - l₂)) *
      (((l₂ - l₃).choose (l₂ - m₂) : ℚ) * 2 ^ (l₂ - m₂) *
        1 ^ (m₂ - l₃)) := by
    intro m₁ hm₁ m₂ hm₂
    have hm₁ := Finset.mem_Icc.mp hm₁
    have hm₂ := Finset.mem_Icc.mp hm₂
    rw [A2.gl2Poly_eval_one _ _ (by omega),
      show m₁ - m₂ = (m₁ - l₂) + (l₂ - m₂) by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl fun m₁ hm₁ =>
    Finset.sum_congr rfl fun m₂ hm₂ => ht m₁ hm₁ m₂ hm₂]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [interval_binomial l₂ l₁ h₁, interval_binomial l₃ l₂ h₂]
  norm_num
  rw [← pow_add, show l₁ - l₂ + (l₂ - l₃) = l₁ - l₃ by omega]

/-- The elementary GL4 total count at every dominant natural highest weight. -/
theorem gl4Poly_eval_one (l₁ l₂ l₃ l₄ : ℕ)
    (h₁ : l₂ ≤ l₁) (h₂ : l₃ ≤ l₂) (h₃ : l₄ ≤ l₃) :
    (gl4Poly l₁ l₂ l₃ l₄).eval 1 =
      4 ^ (l₁ - l₂) * 6 ^ (l₂ - l₃) * 4 ^ (l₃ - l₄) := by
  simp only [gl4Poly, eval_finsetSum, eval_mul, A2.eval_one_qbinom]
  have ht : ∀ m₁ ∈ Finset.Icc l₂ l₁, ∀ m₂ ∈ Finset.Icc l₃ l₂,
      ∀ m₃ ∈ Finset.Icc l₄ l₃,
      ((l₁ - l₂).choose (l₁ - m₁) : ℚ) *
        ((l₂ - l₃).choose (l₂ - m₂) : ℚ) *
        ((l₃ - l₄).choose (l₃ - m₃) : ℚ) * (A2.gl3Poly m₁ m₂ m₃).eval 1 =
      ((((l₁ - l₂).choose (l₁ - m₁) : ℚ) * 1 ^ (l₁ - m₁) *
        3 ^ (m₁ - l₂)) *
      (((l₂ - l₃).choose (l₂ - m₂) : ℚ) * 3 ^ (l₂ - m₂) *
        3 ^ (m₂ - l₃))) *
      (((l₃ - l₄).choose (l₃ - m₃) : ℚ) * 3 ^ (l₃ - m₃) *
        1 ^ (m₃ - l₄)) := by
    intro m₁ hm₁ m₂ hm₂ m₃ hm₃
    have hm₁ := Finset.mem_Icc.mp hm₁
    have hm₂ := Finset.mem_Icc.mp hm₂
    have hm₃ := Finset.mem_Icc.mp hm₃
    rw [gl3Poly_eval_one _ _ _ (by omega) (by omega),
      show m₁ - m₃ = (m₁ - l₂) + (l₂ - m₂) + (m₂ - l₃) + (l₃ - m₃) by omega]
    simp only [pow_add, one_pow]
    ring
  rw [Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ =>
    Finset.sum_congr rfl fun m₃ hm₃ => ht m₁ hm₁ m₂ hm₂ m₃ hm₃]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [interval_binomial l₂ l₁ h₁, interval_binomial l₃ l₂ h₂,
    interval_binomial l₄ l₃ h₃]
  norm_num

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.coeff_gl4Poly
#print axioms VOA.DeligneAudit.D4Char.interval_binomial
#print axioms VOA.DeligneAudit.D4Char.gl3Poly_eval_one
#print axioms VOA.DeligneAudit.D4Char.gl4Poly_eval_one

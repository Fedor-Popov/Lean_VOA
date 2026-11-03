import VOA.Huang.LogAssocFivePointDual
import VOA.Huang.HuangODEThreeSepRing

/-!
# Coefficients of ring elements times normalized three-intertwiner series

For the total-level-normalized series `Q = normalizedSeries …` (on a uniform base, so that
both negative strips vanish) and the three binomial line series
`ιx (x B_k)`, `ιy (y B_k)`, `ιxy (xy B_k)` (`B_k = Σ C(i,k) tⁱ = t^k (1-t)^{-k-1}`), the
`(m,n)` coefficient of the product is a finite sum of normalized coefficients at shifted
complex indices. These are the bookkeeping lemmas for the three insertion moves.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid PowerSeries
open VOA.Huang.LogHuangODEProduct
open VOA.Huang.FivePointSep
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : C2Rigid.GWModule W M₀} {A₁ : C2Rigid.GWModule W M₁}
  {A₂ : C2Rigid.GWModule W M₂} {A₃ : C2Rigid.GWModule W M₃} {A₄ : C2Rigid.GWModule W M₄}
  {A₅ : C2Rigid.GWModule W M₅} {A₆ : C2Rigid.GWModule W M₆}
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

theorem coeff_X_mul_binom (k i : ℕ) :
    coeff (i + 1) ((X : PowerSeries ℂ) * HuangODEAlgebra.binomSeries 1 k) = (i.choose k : ℂ) := by
  rw [coeff_succ_X_mul]; simp [HuangODEAlgebra.binomSeries]

theorem coeff_zero_X_mul_binom (k : ℕ) :
    coeff 0 ((X : PowerSeries ℂ) * HuangODEAlgebra.binomSeries 1 k) = 0 := by
  simp

theorem c2_normalizedSeries (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (w₄ : M₄) (N₀ s m n : ℕ) :
    c2 (normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n :=
  coeff_normalizedSeries _ _ _ _ _ _ _ _ _ _ _ _

section Uniform

variable {h₂ h₃ h₄ ν μ : ℂ} (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
  {N₂ N₃ N₄ s : ℕ} (hs : N₂ + N₃ + N₄ ≤ s)
  {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
  (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃))
  (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
  (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (N₀ : ℕ)
include hB hs hw₂ hw₃ hw₄

/-- Vanishing at negative integer offsets, in complex form. -/
theorem normalizedCoeff_neg' (a b : ℤ) (h : a < 0 ∨ b < 0) {x y : ℂ}
    (hx : x = (a : ℂ)) (hy : y = (b : ℂ)) :
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s x y = 0 := by
  subst hx hy
  exact normalizedCoeff_eq_zero_of_negative hB hs hw₂ hw₃ hw₄ c f w₁ N₀ a b h

theorem c2_monomial_normalizedSeries (a b m n : ℕ) :
    c2 (X ^ a * PowerSeries.C (X ^ b) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ((m : ℂ) - a) ((n : ℂ) - b) :=
  coeff_monomial_normalizedSeries hB hs hw₂ hw₃ hw₄ c f w₁ N₀ a b m n

/-- The diagonal binomial line `xy · Σ C(i,k) (xy)ⁱ`. -/
theorem c2_ιxy_binom_normalized (k m n I : ℕ) (hI : m ≤ I) :
    c2 (ιxy (X * HuangODEAlgebra.binomSeries 1 k) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) *
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ((m : ℂ) - 1 - i) ((n : ℂ) - 1 - i) := by
  rw [c2_ιxy_mul, Finset.sum_range_succ']
  simp only [Nat.zero_le, ite_true, coeff_zero_X_mul_binom, zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hI]
  rw [Finset.sum_eq_zero (s := Finset.Ico m I) (fun i hi => by
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [normalizedCoeff_neg' hB hs hw₂ hw₃ hw₄ c f w₁ N₀ ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - i)
      (Or.inl (by omega)) (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  split_ifs with hin
  · rw [coeff_X_mul_binom, c2_normalizedSeries]
    congr 2
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
    · rw [Nat.cast_sub hin]; push_cast; ring
  · rw [normalizedCoeff_neg' hB hs hw₂ hw₃ hw₄ c f w₁ N₀ ((m : ℤ) - 1 - i) ((n : ℤ) - 1 - i)
      (Or.inr (by omega)) (by push_cast; ring) (by push_cast; ring), mul_zero]

/-- The inner binomial line `y · Σ C(j,k) yʲ`. -/
theorem c2_ιy_binom_normalized (k m n J : ℕ) (hJ : n ≤ J) :
    c2 (ιy (X * HuangODEAlgebra.binomSeries 1 k) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s) m n =
    ∑ j ∈ Finset.range J, (j.choose k : ℂ) *
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s (m : ℂ) ((n : ℂ) - 1 - j) := by
  rw [c2_ιy_mul, Finset.sum_range_succ']
  simp only [coeff_zero_X_mul_binom, zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  rw [Finset.sum_eq_zero (s := Finset.Ico n J) (fun j hj => by
    have hj' := (Finset.mem_Ico.mp hj).1
    rw [normalizedCoeff_neg' hB hs hw₂ hw₃ hw₄ c f w₁ N₀ (m : ℤ) ((n : ℤ) - 1 - j)
      (Or.inr (by omega)) (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn := Finset.mem_range.mp hj
  rw [coeff_X_mul_binom, c2_normalizedSeries]
  congr 2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The outer binomial line `x · Σ C(i,k) xⁱ`, times `y^b`. -/
theorem c2_ιx_binom_normalized (k b m n I : ℕ) (hI : m ≤ I) :
    c2 (ιx (X * HuangODEAlgebra.binomSeries 1 k) * (X ^ 0 * PowerSeries.C (X ^ b) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s)) m n =
    ∑ i ∈ Finset.range I, (i.choose k : ℂ) *
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s ((m : ℂ) - 1 - i) ((n : ℂ) - b) := by
  rw [c2_ιx_mul, Finset.sum_range_succ']
  simp only [coeff_zero_X_mul_binom, zero_mul, add_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hI]
  rw [Finset.sum_eq_zero (s := Finset.Ico m I) (fun i hi => by
    have hi' := (Finset.mem_Ico.mp hi).1
    rw [normalizedCoeff_neg' hB hs hw₂ hw₃ hw₄ c f w₁ N₀ ((m : ℤ) - 1 - i) ((n : ℤ) - b)
      (Or.inl (by omega)) (by push_cast; ring) (by push_cast; ring), mul_zero]), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  rw [coeff_X_mul_binom, c2_monomial_normalizedSeries hB hs hw₂ hw₃ hw₄]
  congr 2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

end Uniform

end VOA.Huang.LogAssocFivePointGraded

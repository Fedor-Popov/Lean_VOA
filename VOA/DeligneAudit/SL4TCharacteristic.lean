import VOA.DeligneAudit.SL4TGrassmannianFinite
import Mathlib.Algebra.Polynomial.Reverse

/-! # Characteristic polynomials of complementary Grassmannian alphabets -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The finite coefficient series of a sequence. -/
def coefficientPoly {R : Type*} [Semiring R] (f : ℕ → R) (d : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (d + 1), monomial i (f i)

theorem coefficientPoly_coeff {R : Type*} [Semiring R] (f : ℕ → R) (d j : ℕ) :
    (coefficientPoly f d).coeff j = if j ≤ d then f j else 0 := by
  simp [coefficientPoly, coeff_monomial, Finset.mem_range, eq_comm]

theorem coefficientPoly_coeff_of_tail {R : Type*} [Semiring R]
    (f : ℕ → R) (d : ℕ) (hf : ∀ j, d < j → f j = 0) (j : ℕ) :
    (coefficientPoly f d).coeff j = f j := by
  rw [coefficientPoly_coeff]
  split_ifs with h
  · rfl
  · exact (hf j (by omega)).symm

theorem coefficientPoly_degree {R : Type*} [Semiring R] (f : ℕ → R) (d : ℕ) :
    (coefficientPoly f d).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coefficientPoly_coeff, if_neg (by omega)]

/-- A descending polynomial; reflection keeps the convolution proof short. -/
def descendingPoly {R : Type*} [Semiring R] (f : ℕ → R) (d : ℕ) : R[X] :=
  (coefficientPoly f d).reflect d

theorem descendingPoly_eq_sum {R : Type*} [Semiring R] (f : ℕ → R) (d : ℕ) :
    descendingPoly f d = ∑ i ∈ Finset.range (d + 1), Polynomial.C (f i) * X ^ (d - i) := by
  have hs (s : Finset ℕ) :
      reflect d (∑ i ∈ s, monomial i (f i)) =
        ∑ i ∈ s, reflect d (monomial i (f i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, ih]
  unfold descendingPoly coefficientPoly
  rw [hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow,
    revAt_le (by have := Finset.mem_range.mp hi; omega)]

theorem descendingPoly_constant {R : Type*} [Semiring R] (f : ℕ → R) (d : ℕ) :
    (descendingPoly f d).coeff 0 = f d := by
  simp [descendingPoly, coefficientPoly_coeff]

/-- The characteristic polynomial of the elementary alphabet. -/
def grassP (d T : ℕ) : (GrassRing d T)[X] :=
  descendingPoly (fun i => (-1) ^ i * eClass d T i) d

/-- The characteristic polynomial of the complementary alphabet. -/
def grassPbar (d T : ℕ) : (GrassRing d T)[X] :=
  descendingPoly (hClass d T) T

theorem grassP_eq_sum (d T : ℕ) :
    grassP d T = ∑ i ∈ Finset.range (d + 1),
      Polynomial.C ((-1) ^ i * eClass d T i) * X ^ (d - i) := descendingPoly_eq_sum _ _

theorem grassPbar_eq_sum (d T : ℕ) :
    grassPbar d T = ∑ i ∈ Finset.range (T + 1),
      Polynomial.C (hClass d T i) * X ^ (T - i) := descendingPoly_eq_sum _ _

theorem grassP_constant (d T : ℕ) :
    (grassP d T).coeff 0 = (-1) ^ d * eClass d T d := descendingPoly_constant _ _

theorem grassPbar_constant (d T : ℕ) :
    (grassPbar d T).coeff 0 = hClass d T T := descendingPoly_constant _ _

/-- The inverse-series relation survives truncation because both discarded tails vanish. -/
theorem grass_coefficient_product (d T : ℕ) :
    coefficientPoly (fun i => (-1) ^ i * eClass d T i) d *
      coefficientPoly (hClass d T) T = 1 := by
  have he := coefficientPoly_coeff_of_tail (fun i => (-1) ^ i * eClass d T i) d
    (fun j hj => by dsimp; rw [eClass_eq_zero d T j hj, mul_zero])
  have hh := coefficientPoly_coeff_of_tail (hClass d T) T
    (fun j hj => hClass_eq_zero d T j hj)
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [he, hh]
  by_cases hn : n = 0
  · subst n
    simp [eClass, hClass]
  · rw [grass_convolution d T n (by omega), coeff_one, if_neg hn]

/-- The all-rectangle factorization, including either zero side. -/
theorem grass_characteristic_product (d T : ℕ) :
    grassP d T * grassPbar d T = X ^ (d + T) := by
  unfold grassP grassPbar descendingPoly
  rw [← reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _),
    grass_coefficient_product]
  simp

/-- The requested identity in the original Grassmannian coordinates. -/
theorem H_characteristic_product (d M : ℕ) (hdM : d ≤ M) :
    grassP d (M - d) * grassPbar d (M - d) = X ^ M := by
  simpa only [Nat.add_sub_of_le hdM] using grass_characteristic_product d (M - d)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.grass_coefficient_product
#print axioms VOA.DeligneAudit.SL4T.grass_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.H_characteristic_product

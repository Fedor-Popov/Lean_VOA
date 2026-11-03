import VOA.Huang.NgSchauenburgTwistOrder
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # The integer determinant step in a Vafa argument

An invertible integer exponent matrix forces solutions of its multiplicative
relations to be torsion. Constructing such relations from categorical braid
diagrams, and proving the required full rank, remain separate obligations.
The modular-group relation alone is not supplied as a substitute for them.
-/

noncomputable section
namespace VOA.Huang.NgSchauenburg

/-- Apply a matrix of integer exponents to a tuple in a commutative group. -/
def monomialAction {ι : Type*} [Fintype ι] {G : Type*} [CommGroup G]
    (A : Matrix ι ι ℤ) (t : ι → G) : ι → G :=
  fun i => ∏ j, t j ^ A i j

private theorem zpow_sum' {ι : Type*} {G : Type*} [CommGroup G]
    (t : G) (s : Finset ι) (e : ι → ℤ) : t ^ (∑ i ∈ s, e i) = ∏ i ∈ s, t ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem monomialAction_mul {ι : Type*} [Fintype ι] {G : Type*} [CommGroup G]
    (A B : Matrix ι ι ℤ) (t : ι → G) :
    monomialAction (A * B) t = monomialAction A (monomialAction B t) := by
  ext i
  simp only [monomialAction, Matrix.mul_apply, zpow_sum', ← Finset.prod_zpow, zpow_mul]
  rw [Finset.prod_comm]
  congr 1
  funext j
  apply Finset.prod_congr rfl
  intro k _
  rw [← zpow_mul, ← zpow_mul, mul_comm]

/-- Every coordinate is killed by the determinant, even when it is zero. -/
theorem zpow_det_eq_one_of_monomial_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (A : Matrix ι ι ℤ) (t : ι → G)
    (h : monomialAction A t = 1) (i : ι) : t i ^ A.det = 1 := by
  have he := congrFun (monomialAction_mul A.adjugate A t) i
  rw [Matrix.adjugate_mul, h] at he
  simpa [monomialAction, Matrix.one_apply] using he

/-- The finite-dimensional arithmetic step: full rank of the integer exponent
matrix and its multiplicative relations imply root-of-unity coordinates. -/
theorem finite_order_of_monomial_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (A : Matrix ι ι ℤ) (t : ι → G)
    (hdet : A.det ≠ 0) (h : monomialAction A t = 1) :
    ∀ i, IsOfFinOrder (t i) := by
  intro i
  exact isOfFinOrder_iff_zpow_eq_one.mpr
    ⟨A.det, hdet, zpow_det_eq_one_of_monomial_relations A t h i⟩

/-- A rational matrix model used only to audit the proposed modular-relation
shortcut. These matrices are not asserted to be categorical modular data. -/
def relationTestS : Matrix (Fin 2) (Fin 2) ℚ := !![2 / 3, 1; -13 / 9, -2 / 3]
def relationTestT : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 1 / 2]

theorem relationTestS_sq : relationTestS ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [relationTestS, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem relationTestST_cube : (relationTestS * relationTestT) ^ 3 = relationTestS ^ 2 := by
  rw [relationTestS_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [relationTestS, relationTestT, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem relationTestT_infinite_order : ¬ IsOfFinOrder relationTestT := by
  have hd : relationTestT = Matrix.diagonal ![(2 : ℚ), 1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  intro h
  obtain ⟨n, hn, hp⟩ := h.exists_pow_eq_one
  have he := congrFun (congrFun hp 0) 0
  rw [hd, Matrix.diagonal_pow] at he
  have he' : (2 : ℚ) ^ n = 1 := by simpa using he
  have hlt : (1 : ℚ) < 2 ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  exact (ne_of_gt hlt) he'

end VOA.Huang.NgSchauenburg

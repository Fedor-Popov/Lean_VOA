import VOA.Huang.DLNSchur2Roots

/-! # Weyl matrices and the square characters -/

namespace VOA.Huang.DLNSchur

open scoped commutatorElement

variable {R : Type*} [CommRing R]

@[simp] theorem upperRoot_neg (t : R) : upperRoot (-t) = (upperRoot t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← upperRoot_add]; simp

@[simp] theorem lowerRoot_neg (t : R) : lowerRoot (-t) = (lowerRoot t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← lowerRoot_add]; simp

@[simp] theorem torus_one : torus (1 : Rˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus]

@[simp] theorem torus_mul (u v : Rˣ) : torus (u * v) = torus u * torus v := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem torus_commute (u v : Rˣ) : Commute (torus u) (torus v) := by
  change torus u * torus v = torus v * torus u
  rw [← torus_mul, ← torus_mul, mul_comm]

theorem torus_upper_commutator (u : Rˣ) (t : R) :
    ⁅torus u, upperRoot t⁆ = upperRoot (((u : R) ^ 2 - 1) * t) := by
  rw [commutatorElement_def, torus_upper_conj, ← upperRoot_neg, ← upperRoot_add]
  congr 1; ring

theorem torus_lower_commutator (u : Rˣ) (t : R) :
    ⁅torus u, lowerRoot t⁆ = lowerRoot (((↑u⁻¹ : R) ^ 2 - 1) * t) := by
  rw [commutatorElement_def, torus_lower_conj, ← lowerRoot_neg, ← lowerRoot_add]
  congr 1; ring

/-- The Weyl matrix with parameter a unit. -/
def weyl (u : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, (u : R); -(↑u⁻¹ : R), 0], by simp [Matrix.det_fin_two_of]⟩

theorem weyl_eq_roots (u : Rˣ) :
    weyl u = upperRoot (u : R) * lowerRoot (-(↑u⁻¹ : R)) * upperRoot (u : R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [weyl, upperRoot, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_upper_conj (u : Rˣ) (t : R) :
    weyl u * upperRoot t * (weyl u)⁻¹ = lowerRoot (-((↑u⁻¹ : R) ^ 2 * t)) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [weyl, upperRoot, lowerRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      pow_two, mul_assoc, mul_comm, mul_left_comm]

theorem weyl_lower_conj (u : Rˣ) (t : R) :
    weyl u * lowerRoot t * (weyl u)⁻¹ = upperRoot (-((u : R) ^ 2 * t)) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [weyl, upperRoot, lowerRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      pow_two, mul_assoc, mul_comm, mul_left_comm]

theorem weyl_torus_conj (u v : Rˣ) :
    weyl u * torus v * (weyl u)⁻¹ = torus v⁻¹ := by
  have huv : (u : R) * ((v : R) * (↑u⁻¹ : R)) = v := by
    rw [mul_left_comm (u : R) (v : R), Units.mul_inv, mul_one]
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [weyl, torus, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      mul_assoc, mul_comm, huv]

theorem weyl_mul_weyl_one_inv (u : Rˣ) :
    weyl u * (weyl (1 : Rˣ))⁻¹ = torus u := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [weyl, torus, Matrix.mul_apply, Fin.sum_univ_two]

end VOA.Huang.DLNSchur

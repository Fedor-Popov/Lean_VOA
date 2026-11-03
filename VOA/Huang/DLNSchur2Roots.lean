import VOA.Huang.DLNSchurCriterion

/-! # Root matrices and elementary generation over `ZMod`

Generation is transported from the verified integral reduction theorem. It does not
require a local-ring argument, and holds for every positive modulus.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

variable {R : Type*} [CommRing R]

/-- Upper root matrix. -/
def upperRoot (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- Lower root matrix. -/
def lowerRoot (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem upperRoot_zero : upperRoot (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperRoot]

@[simp] theorem lowerRoot_zero : lowerRoot (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerRoot]

@[simp] theorem upperRoot_add (s t : R) : upperRoot (s + t) = upperRoot s * upperRoot t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp] theorem lowerRoot_add (s t : R) : lowerRoot (s + t) = lowerRoot s * lowerRoot t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem upperRoot_pow (t : R) (n : ℕ) : upperRoot t ^ n = upperRoot (n * t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← upperRoot_add]; congr 1; push_cast; ring

@[simp] theorem lowerRoot_pow (t : R) (n : ℕ) : lowerRoot t ^ n = lowerRoot (n * t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← lowerRoot_add]; congr 1; push_cast; ring

/-- Two elementary matrices generate `SL₂(ZMod n)` for every positive `n`. -/
theorem root_generators (n : ℕ) [NeZero n] :
    Subgroup.closure {upperRoot (1 : ZMod n), lowerRoot (1 : ZMod n)} = ⊤ := by
  let K := Subgroup.closure {upperRoot (1 : ZMod n), lowerRoot (1 : ZMod n)}
  have hu : upperRoot (1 : ZMod n) ∈ K := Subgroup.subset_closure (by simp)
  have hl : lowerRoot (1 : ZMod n) ∈ K := Subgroup.subset_closure (by simp)
  have hu_neg : upperRoot (-1 : ZMod n) = (upperRoot (1 : ZMod n))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← upperRoot_add]; simp
  have hT : VOA.Huang.DLN.reduction n ModularGroup.T ∈ K := by
    have heq : VOA.Huang.DLN.reduction n ModularGroup.T = upperRoot (1 : ZMod n) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [VOA.Huang.DLN.reduction, ModularGroup.T, upperRoot]
    exact heq ▸ hu
  have hS : VOA.Huang.DLN.reduction n ModularGroup.S ∈ K := by
    have heq : VOA.Huang.DLN.reduction n ModularGroup.S =
        upperRoot (-1 : ZMod n) * lowerRoot 1 * upperRoot (-1) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [VOA.Huang.DLN.reduction, ModularGroup.S, upperRoot, lowerRoot,
          Matrix.mul_apply, Fin.sum_univ_two]
    rw [heq, hu_neg]
    exact K.mul_mem (K.mul_mem (K.inv_mem hu) hl) (K.inv_mem hu)
  have hpre : K.comap (VOA.Huang.DLN.reduction n) = ⊤ := by
    apply top_unique
    rw [← SpecialLinearGroup.SL2Z_generators]
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  apply top_unique
  intro g _
  obtain ⟨γ, rfl⟩ := reduction_surjective n g
  exact (show γ ∈ K.comap (VOA.Huang.DLN.reduction n) by rw [hpre]; trivial)

/-- Diagonal torus matrix. -/
def torus (u : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![(u : R), 0; 0, (↑u⁻¹ : R)], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem torus_inv (u : Rˣ) : (torus u)⁻¹ = torus u⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus]

/-- The square character on the upper root. -/
theorem torus_upper_conj (u : Rˣ) (t : R) :
    torus u * upperRoot t * (torus u)⁻¹ = upperRoot ((u : R) ^ 2 * t) := by
  rw [torus_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, upperRoot, Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc,
      mul_comm, mul_left_comm]

/-- The inverse square character on the lower root. -/
theorem torus_lower_conj (u : Rˣ) (t : R) :
    torus u * lowerRoot t * (torus u)⁻¹ = lowerRoot ((↑u⁻¹ : R) ^ 2 * t) := by
  rw [torus_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc,
      mul_comm, mul_left_comm]

end VOA.Huang.DLNSchur

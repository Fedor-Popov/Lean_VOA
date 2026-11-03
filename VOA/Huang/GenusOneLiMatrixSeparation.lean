import VOA.Huang.GenusOneBimoduleTrace
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # All rectangular blocks separate a bimodule

For a product of matrix algebras, maps into rectangular matrix blocks separate
points of every unital bimodule, even an infinite-dimensional one. Unlike
trace realization, this uses all ordered pairs of simple blocks.
-/
namespace VOA.Huang.GenusOne.BimoduleTrace
open scoped BigOperators

section Matrices
variable {ι : Type*} (d : ι → ℕ)
  {E : Type*} [AddCommGroup E] [Module ℂ E]

noncomputable def blockUnit (i : ι) (p q : Fin (d i)) :
    ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ := by
  classical
  exact Pi.single i (Matrix.single p q 1)

theorem blockUnit_mul (i : ι) (p q : Fin (d i))
    (a : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    blockUnit d i p q * a = ∑ r, a i q r • blockUnit d i p r := by
  classical
  ext j s t
  by_cases h : j = i
  · subst j
    simp only [blockUnit, Pi.mul_apply, Pi.single_eq_same, Finset.sum_apply, Matrix.sum_apply,
      Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hs : s = p
    · subst s
      simp [Matrix.single_mul_apply_same, Matrix.single_apply]
    · simp [Matrix.single_mul_apply_of_ne, hs, Ne.symm hs]
  · simp [blockUnit, Pi.single_eq_of_ne h]

theorem mul_blockUnit (i : ι) (p q : Fin (d i))
    (a : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    a * blockUnit d i p q = ∑ r, a i r p • blockUnit d i r q := by
  classical
  ext j s t
  by_cases h : j = i
  · subst j
    simp only [blockUnit, Pi.mul_apply, Pi.single_eq_same, Finset.sum_apply, Matrix.sum_apply,
      Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases ht : t = q
    · subst t
      simp [Matrix.mul_single_apply_same, Matrix.single_apply]
    · simp [Matrix.mul_single_apply_of_ne, ht, Ne.symm ht]
  · simp [blockUnit, Pi.single_eq_of_ne h]

theorem sum_blockUnit [Fintype ι] : (∑ i, ∑ p, blockUnit d i p p) = 1 := by
  classical
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [Finset.sum_apply, blockUnit, Pi.single_eq_same]
    exact Matrix.sum_single_one
  · intro i _ hi
    simp [blockUnit, Pi.single_eq_of_ne (Ne.symm hi)]
  · simp

/-- Matrix coefficients of a functional after applying the two matrix units. -/
noncomputable def blockMap
    (B : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E)
    (f : Module.Dual ℂ E) (i j : ι) (p : Fin (d j)) (q : Fin (d i)) :
    E →ₗ[ℂ] Matrix (Fin (d j)) (Fin (d i)) ℂ :=
  LinearMap.pi fun a => LinearMap.pi fun b =>
    (f.comp (B.left (blockUnit d j p a))).comp (B.right (blockUnit d i b q))

theorem blockMap_left
    (B : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E)
    (f : Module.Dual ℂ E) (i j : ι) (p : Fin (d j)) (q : Fin (d i))
    (a : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) (x : E) :
    blockMap d B f i j p q (B.left a x) = a j * blockMap d B f i j p q x := by
  ext s t
  change f (B.left (blockUnit d j p s) (B.right (blockUnit d i t q) (B.left a x))) = _
  rw [← B.commute, ← B.left_mul, blockUnit_mul]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply]
  rfl

theorem blockMap_right
    (B : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E)
    (f : Module.Dual ℂ E) (i j : ι) (p : Fin (d j)) (q : Fin (d i))
    (a : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) (x : E) :
    blockMap d B f i j p q (B.right a x) = blockMap d B f i j p q x * a i := by
  ext s t
  change f (B.left (blockUnit d j p s) (B.right (blockUnit d i t q) (B.right a x))) = _
  rw [← B.right_mul, mul_blockUnit]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- Rectangular matrix-valued bimodule maps separate arbitrary bimodules. -/
theorem eq_zero_of_matrix_bimodule_maps [Finite ι]
    (B : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E) (x : E)
    (hx : ∀ (i j : ι) (T : E →ₗ[ℂ] Matrix (Fin (d j)) (Fin (d i)) ℂ),
      (∀ a y, T (B.left a y) = a j * T y) →
      (∀ a y, T (B.right a y) = T y * a i) → T x = 0) : x = 0 := by
  classical
  letI := Fintype.ofFinite ι
  apply (Module.forall_dual_apply_eq_zero_iff ℂ x).mp
  intro f
  have hz (i j : ι) (p : Fin (d j)) (q : Fin (d i)) :
      f (B.left (blockUnit d j p p) (B.right (blockUnit d i q q) x)) = 0 := by
    have ht := hx i j (blockMap d B f i j p q)
      (blockMap_left d B f i j p q) (blockMap_right d B f i j p q)
    exact congrArg (fun t => t p q) ht
  calc
    f x = f (B.left 1 (B.right 1 x)) := by rw [B.left_one, B.right_one]
    _ = 0 := by
      rw [← sum_blockUnit d]
      simp only [map_sum, LinearMap.sum_apply]
      simp only [hz, Finset.sum_const_zero]

end Matrices
section Endomorphisms
variable {ι : Type*} [Finite ι] (U : ι → Type*)
  [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  [∀ i, FiniteDimensional ℂ (U i)]
  {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Basis-free form: maps to all `Hom(U i, U j)` separate points. -/
theorem eq_zero_of_end_bimodule_maps
    (B : Actions (∀ i, Module.End ℂ (U i)) E) (x : E)
    (hx : ∀ (i j : ι) (T : E →ₗ[ℂ] (U i →ₗ[ℂ] U j)),
      (∀ a y, T (B.left a y) = (a j).comp (T y)) →
      (∀ a y, T (B.right a y) = (T y).comp (a i)) → T x = 0) : x = 0 := by
  classical
  let b := fun i => Module.finBasis ℂ (U i)
  let d := fun i => Module.finrank ℂ (U i)
  let e : (∀ i, Module.End ℂ (U i)) ≃ₐ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
    AlgEquiv.piCongrRight fun i => LinearMap.toMatrixAlgEquiv (b i)
  let B' : Actions (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) E := {
    left := B.left.comp e.symm.toLinearMap
    right := B.right.comp e.symm.toLinearMap
    left_one := fun y => by simp [B.left_one]
    right_one := fun y => by simp [B.right_one]
    left_mul := fun a c y => by simp [B.left_mul]
    right_mul := fun a c y => by simp [B.right_mul]
    commute := fun a c y => B.commute _ _ y }
  apply eq_zero_of_matrix_bimodule_maps d B' x
  intro i j T hL hR
  let T' := (Matrix.toLin (b i) (b j)).toLinearMap.comp T
  have hT (y : E) : LinearMap.toMatrix (b i) (b j) (T' y) = T y :=
    (LinearMap.toMatrix (b i) (b j)).apply_symm_apply (T y)
  have hL' (a : ∀ i, Module.End ℂ (U i)) (y : E) :
      T' (B.left a y) = (a j).comp (T' y) := by
    apply (LinearMap.toMatrix (b i) (b j)).injective
    rw [hT, LinearMap.toMatrix_comp (b i) (b j) (b j), hT]
    have h := hL (e a) y
    change T (B.left (e.symm (e a)) y) = (e a) j * T y at h
    rw [e.symm_apply_apply] at h
    exact h
  have hR' (a : ∀ i, Module.End ℂ (U i)) (y : E) :
      T' (B.right a y) = (T' y).comp (a i) := by
    apply (LinearMap.toMatrix (b i) (b j)).injective
    rw [hT, LinearMap.toMatrix_comp (b i) (b i) (b j), hT]
    have h := hR (e a) y
    change T (B.right (e.symm (e a)) y) = T y * (e a) i at h
    rw [e.symm_apply_apply] at h
    exact h
  have hz := congrArg (LinearMap.toMatrix (b i) (b j)) (hx i j T' hL' hR')
  simpa only [hT, map_zero] using hz

end Endomorphisms
end VOA.Huang.GenusOne.BimoduleTrace

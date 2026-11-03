import VOA.Examples.AffineSl2FirstNullDimension
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Kernel dimension bounded by the order of a determinant root

An adapted constant basis puts a basis of the specialized kernel into selected
columns. Each selected column is divisible by the linear root factor, so their
number bounds the root multiplicity of the actual polynomial determinant.
-/
namespace VOA.PolynomialMatrix
open Polynomial Matrix Module
open scoped BigOperators
noncomputable section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem pow_card_dvd_det_of_eval_columns (M : Matrix ι ι K[X]) (z : K)
    (S : Finset ι) (hS : ∀ j ∈ S, ∀ i, (M i j).eval z = 0) :
    (X-Polynomial.C z)^S.card ∣ M.det := by
  classical
  let v : ι → K[X] := fun j => if j ∈ S then X-Polynomial.C z else 1
  have hv : ∀ i j, ∃ q : K[X], M i j = v j * q := by
    intro i j
    by_cases hj : j ∈ S
    · obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr (hS j hj i)
      exact ⟨q, by simpa only [v,if_pos hj] using hq⟩
    · exact ⟨M i j, by simp [v,hj]⟩
  choose Q hQ using hv
  have hM : M = Matrix.of (fun i j => v j * Q i j) := by funext i j; exact hQ i j
  rw [hM,det_mul_row]
  have hprod : ∏ j : ι, v j = (X-Polynomial.C z)^S.card := by
    simp only [v]
    rw [Finset.prod_ite_mem]
    simp
  rw [hprod]
  exact dvd_mul_right _ _

/-- A nonzero polynomial determinant has root order at least the dimension
of the actual specialized kernel. -/
theorem finrank_ker_le_rootMultiplicity (M : Matrix ι ι K[X]) (z : K)
    (hdet : M.det ≠ 0) :
    Module.finrank K (evaluate M z).mulVecLin.ker ≤ M.det.rootMultiplicity z := by
  classical
  let U := (evaluate M z).mulVecLin.ker
  obtain ⟨Q,hQ⟩ := U.exists_isCompl
  let bU := Module.finBasis K U
  let bQ := Module.finBasis K Q
  let B := (bU.prod bQ).map (U.prodEquivOfIsCompl Q hQ)
  let J := Fin (Module.finrank K U) ⊕ Fin (Module.finrank K Q)
  have hcard : Fintype.card J = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi]
  let e : J ≃ ι := Fintype.equivOfCardEq hcard
  let b := B.reindex e
  let P : Matrix ι ι K := (Pi.basisFun K ι).toMatrix b
  have hP : IsUnit P.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := b.toMatrix (Pi.basisFun K ι))
    simp only [P, Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
  let S : Finset ι := Finset.univ.image (fun i : Fin (Module.finrank K U) => e (Sum.inl i))
  have hS : S.card = Module.finrank K U := by
    dsimp only [S]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j h
      exact Sum.inl_injective (e.injective h)
  let T := M * Polynomial.C.mapMatrix P
  have hcols : ∀ j ∈ S, ∀ i, (T i j).eval z = 0 := by
    intro j hj i
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
    have hb : b (e (Sum.inl a)) = (bU a : ι → K) := by
      simp [b, B, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Basis.prod_apply,
        Basis.coe_reindex]
    have hu := (bU a).property
    change (evaluate M z).mulVec (bU a) = 0 at hu
    have he : (T i (e (Sum.inl a))).eval z =
        ((evaluate M z).mulVec (b (e (Sum.inl a)))) i := by
      simp [T, Matrix.mul_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        P, Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.mulVec, dotProduct,
        evaluate, RingHom.mapMatrix_apply]
    rw [he,hb,hu]
    rfl
  have hdvd := pow_card_dvd_det_of_eval_columns T z S hcols
  have hT : T.det = M.det * Polynomial.C P.det := by
    dsimp only [T]
    rw [det_mul,← RingHom.map_det]
  rw [hS,hT] at hdvd
  have hu : IsUnit (Polynomial.C P.det) := hP.map Polynomial.C
  exact (le_rootMultiplicity_iff hdet).mpr ((hu.dvd_mul_right).mp hdvd)

end
end VOA.PolynomialMatrix

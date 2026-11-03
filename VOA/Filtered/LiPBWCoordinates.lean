import VOA.Filtered.ClassicalFreeness
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Coordinate functionals for a genuine filtered PBW basis

A basis whose depth tails equal the actual Li filtration supplies explicit coordinate
functionals on the Li associated graded. Its exact-depth homogeneous classes are
therefore linearly independent; no associated-graded independence is assumed.
-/
namespace VOA
open scoped BigOperators DirectSum
noncomputable section
variable {V ι : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (B : Module.Basis ι ℂ V) (depth : ι → ℕ)
    (hF : ∀ p, liFiltration W p = Submodule.span ℂ (B '' {i | p ≤ depth i}))
include hF
attribute [local instance] Classical.propDecidable

/-- A basis coordinate below the filtration threshold vanishes on the actual filtration. -/
theorem liBasisCoordinate_vanish (p : ℕ) {x : V} (hx : x ∈ liFiltration W p)
    (i : ι) (hi : depth i < p) : B.repr x i = 0 := by
  classical
  rw [hF p] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,hj,rfl⟩ := hx
      rw [B.repr_self, Finsupp.single_apply]
      exact if_neg (fun h => by subst j; exact (not_lt_of_ge hj) hi)
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, Finsupp.smul_apply, hx, smul_zero]

/-- An exact-depth coordinate descends through every conformal Li-layer quotient. -/
def liBasisCoordinateLayer (i : ι) (p N : ℕ) : liWeightLayer W p N →ₗ[ℂ] ℂ := by
  classical
  let f : liWeightPiece W p N →ₗ[ℂ] ℂ :=
    (Finsupp.lapply i).comp (B.repr.toLinearMap.comp (liWeightPiece W p N).subtype)
  exact if hp : depth i = p then
    ((liWeightPiece W (p+1) N).comap (liWeightPiece W p N).subtype).liftQ f
      (fun x hx => by
        change B.repr x.1 i = 0
        exact liBasisCoordinate_vanish W B depth hF (p+1) hx.1 i (by omega))
    else 0

/-- The coordinate extends over the external direct sum of all Li bidegrees. -/
def liBasisCoordinate (i : ι) : liAssociatedGraded W →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ (ℕ × ℕ) ℂ (fun d => liBasisCoordinateLayer W B depth hF i d.1 d.2)

theorem liBasisCoordinate_class (i : ι) (p N : ℕ) (x : liWeightPiece W p N) :
    liBasisCoordinate W B depth hF i (liHomogeneousClass W p N x) =
      if depth i = p then B.repr x.1 i else 0 := by
  classical
  simp only [liHomogeneousClass, liHomogeneousClassLinear, LinearMap.comp_apply,
    liBasisCoordinate, DirectSum.toModule_lof]
  unfold liBasisCoordinateLayer
  dsimp only
  split_ifs <;> rfl

/-- Actual homogeneous PBW classes have the Kronecker coordinate pairing. -/
theorem liBasisCoordinate_basisClass (weight : ι → ℕ)
    (hB : ∀ i, B i ∈ liWeightPiece W (depth i) (weight i)) (i j : ι) :
    liBasisCoordinate W B depth hF i
      (liHomogeneousClass W (depth j) (weight j) ⟨B j,hB j⟩) = if j=i then 1 else 0 := by
  classical
  rw [liBasisCoordinate_class, B.repr_self, Finsupp.single_apply]
  by_cases h : j=i
  · subst j; simp
  · simp [h]

/-- An actual filtered PBW basis remains linearly independent in the Li associated graded. -/
theorem liBasisClass_linearIndependent (weight : ι → ℕ)
    (hB : ∀ i, B i ∈ liWeightPiece W (depth i) (weight i)) :
    LinearIndependent ℂ (fun i => liHomogeneousClass W (depth i) (weight i) ⟨B i,hB i⟩) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  have h := congrArg (liBasisCoordinate W B depth hF i) hc
  simp only [map_sum,map_smul,map_zero,liBasisCoordinate_basisClass] at h
  simpa [smul_eq_mul,mul_ite,hi] using h

end
end VOA

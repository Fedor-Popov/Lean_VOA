import VOA.Huang.GenusOneQEquationSepPairSystem
import VOA.Huang.GenusTwoPointSepDescent

/-!
# The collected two-point Ward identities feed the evaluated q-system

This connects the pre-existing exact Ward predicates to the C₂ reduction used
by the evaluated finite-system route. Neither Ward identity is weakened or
claimed for an actual trace by this algebraic implication.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation
open scoped BigOperators
universe u
variable {V E F : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  {W : VertexOperatorAlgebra V}
  {R G : Type*} [CommRing R] [Algebra ℂ R]
  [AddCommGroup G] [Module ℂ G] [Module R G] [IsScalarTower ℂ R G]

omit [Algebra ℂ R] [IsScalarTower ℂ R G] in
/-- Both exact collected minus-two identities imply the two-slot lowering
condition needed by the C₂ induction. The Eisenstein and elliptic coefficients
and the mode cutoffs are retained in the hypotheses. -/
theorem c2Reduction_of_collected (A : WeakModule W E) (B : WeakModule W F)
    (c : Kernels R) (S : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (hL : CollectedLeftWard A B c S) (hR : CollectedRightWard A B c S) :
    C2Reduction (R := R) A B S := by
  constructor
  · intro a x y
    obtain ⟨K, _, h⟩ := hL a x y
    have heq : S (mode (A.YM a) (-2) x) y =
        -(∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
          S (mode (A.YM a) (2 * (k + 1)) x) y) -
        ∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pleft m) •
          S x (mode (B.YM a) m y) := by
      apply eq_sub_iff_add_eq.mpr
      apply eq_neg_of_add_eq_zero_left
      rwa [add_right_comm]
    rw [heq]
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro k _
      apply Submodule.smul_mem
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨2 * (k + 1), by push_cast; rfl⟩)
    · apply Submodule.sum_mem
      intro m _
      apply Submodule.smul_mem
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨m, rfl⟩)
  · intro a x y
    obtain ⟨K, _, h⟩ := hR a x y
    have heq : S x (mode (B.YM a) (-2) y) =
        -(∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : R) * c.G k) •
          S x (mode (B.YM a) (2 * (k + 1)) y)) -
        ∑ m ∈ Finset.range K, ((-1 : R) ^ m * (m + 1) * c.Pright m) •
          S (mode (A.YM a) m x) y := by
      apply eq_sub_iff_add_eq.mpr
      apply eq_neg_of_add_eq_zero_left
      rwa [add_right_comm]
    rw [heq]
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro k _
      apply Submodule.smul_mem
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨2 * (k + 1), by push_cast; rfl⟩)
    · apply Submodule.sum_mem
      intro m _
      apply Submodule.smul_mem
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨m, rfl⟩)

/-- The original trace-descent input is sufficient for this part of the new
route; a separate diagonal intermediate-level equation is unnecessary. -/
theorem c2Reduction_of_traceDescent (A : WeakModule W E) (B : WeakModule W F)
    (c : Kernels R) (S : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (h : TraceDescent A B c (tensorTrace S)) : C2Reduction (R := R) A B S := by
  obtain ⟨hL, hR⟩ := (traceDescent_iff_collected A B c S).mp h
  exact c2Reduction_of_collected A B c S hL hR

end VOA.Huang.GenusTwoPoint.Separate

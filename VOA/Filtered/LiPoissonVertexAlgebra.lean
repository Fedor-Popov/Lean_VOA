import VOA.Commutative.PoissonVertexAlgebra
import VOA.Filtered.LiGradedModeSkew

/-!
# The genuine Poisson vertex algebra of the Li associated graded

All structure laws are proved for the independently constructed graded modes and
translation. No Hilbert-series equality or classical-freeness hypothesis is used.
-/

namespace VOA
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Li translation as a derivation of its commutative graded algebra. -/
noncomputable def liAssociatedGradedDerivation (W : VertexOperatorAlgebra V) :
    Derivation ℂ (liAssociatedGraded W) (liAssociatedGraded W) where
  toLinearMap := liAssociatedGradedTranslation W
  map_one_eq_zero' := by
    have h := liAssociatedGradedTranslation_leibniz W 1 1
    simp only [mul_one, one_mul] at h
    have heq : liAssociatedGradedTranslation W 1 + liAssociatedGradedTranslation W 1 =
        liAssociatedGradedTranslation W 1 + 0 := by simpa only [add_zero] using h.symm
    exact add_left_cancel heq
  leibniz' x y := by
    simpa only [smul_eq_mul, mul_comm, add_comm] using liAssociatedGradedTranslation_leibniz W x y

/-- Rewrite the coefficient sign from the field-index convention into mode convention. -/
theorem sgn_negative_mode_index (n j : ℕ) :
    sgn (-(n : ℤ) - 1 - j) = (-1 : ℂ) ^ (n + j + 1) := by
  have heq : -(n : ℤ) - 1 - j = -((n + j + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq]
  have hs : ∀ k : ℤ, sgn (-k) = sgn k := by
    intro k
    simp [sgn]
  rw [hs, sgn_natCast]

/-- The Li associated graded of every VOA carries its canonical Poisson vertex algebra. -/
noncomputable def liPoissonVertexAlgebra (W : VertexOperatorAlgebra V) :
    PoissonVertexAlgebra (liAssociatedGraded W) where
  translation := liAssociatedGradedDerivation W
  mode := liAssociatedGradedMode W
  locality := liAssociatedGradedMode_eventually_zero W
  translation_left_zero := liAssociatedGradedMode_translation_zero W
  translation_left_succ := liAssociatedGradedMode_translation_succ W
  translation_mode := liAssociatedGradedTranslation_mode W
  leibniz := liAssociatedGradedMode_leibniz W
  skew n x y := by
    have h := liAssociatedGradedMode_skew W n x y
    simpa only [liSkewTerm, sgn_negative_mode_index] using h
  jacobi := liAssociatedGradedMode_jacobi W

end VOA

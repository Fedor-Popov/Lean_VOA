import VOA.Huang.GenusOneCovarianceReduction
import VOA.Modularity.SqModeWeight

/-! # Square modes on modules, linear in the state

This is the module version of `VOA.sqMode`. Ordinary weights enter only
in the definition on a summand; square homogeneity is proved separately.
-/
namespace VOA.Huang.GenusOne.SquareModule
open VOA
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
variable (A : OrdVModule W M)

@[simp] theorem sqAct_zero_left (k : ℕ) (j : ℤ) : sqAct A (0 : V) k j = 0 := by
  have h := sqAct_smul_left A (0 : ℂ) (0 : V) k j
  simpa using h

/-- The square mode on one ordinary-weight summand, valued in endomorphisms. -/
noncomputable def sqModeFamily (j : ℤ) (k : ℤ) :
    W.grading k →ₗ[ℂ] Module.End ℂ M where
  toFun a := sqAct A (a : V) k.toNat j
  map_add' a b := by
    exact sqAct_add_left A (a : V) (b : V) k.toNat j
  map_smul' c a := by
    exact sqAct_smul_left A c (a : V) k.toNat j

/-- Zhu's square-bracket mode `a[j]`, extended linearly over the ordinary grading of `a`. -/
noncomputable def sqMode (j : ℤ) : V →ₗ[ℂ] Module.End ℂ M :=
  by
    classical
    exact (DFinsupp.lsum ℂ (sqModeFamily A j)).comp
      (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

@[simp] theorem sqMode_apply (j : ℤ) (a : V) (v : M) :
    sqMode A j a v =
      (by
        classical
        exact ((DirectSum.decompose W.grading a).sum fun k ak =>
          sqAct A (ak : V) k.toNat j) v) := by
  classical
  change ((DFinsupp.lsum ℂ (sqModeFamily A j))
    (DirectSum.decompose W.grading a)) v = _
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  rfl

/-- On an ordinary-homogeneous vector the linear extension is the original `vSqZ`. -/
theorem sqMode_of_mem_grading {k : ℤ} {a : V} (ha : a ∈ W.grading k) (j : ℤ) :
    sqMode A j a = sqAct A a k.toNat j := by
  classical
  have hdec : DirectSum.decompose W.grading a =
      DirectSum.of (fun i => (W.grading i : Submodule ℂ V)) k ⟨a, ha⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ V)) ⟨a, ha⟩
  change (DFinsupp.lsum ℂ (sqModeFamily A j))
    (DirectSum.decompose W.grading a) = _
  rw [hdec]
  change (DFinsupp.lsum ℂ (sqModeFamily A j))
    (DFinsupp.single k ⟨a, ha⟩) = _
  rw [DFinsupp.lsum_single]
  rfl


end VOA.Huang.GenusOne.SquareModule

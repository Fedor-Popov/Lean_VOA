import VOA.Core.WeightOneCohomology
import VOA.Examples.NonzeroDeformation

/-!
# Gauge normalization of the current bracket

Centrelessness and adjoint second-cohomology vanishing supply an actual
vacuum-preserving graded gauge correction to any graded deformation.
This packages the normalization construction independently of any model's
large concrete carrier or later rigidity obstruction.
-/
namespace VOA.Deform
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The weight-one cocycle primitive extends by zero on other grades.
Subtracting its VOA coboundary yields an actual graded deformation with
zero corrected current bracket. No regularity or rigidity is assumed. -/
theorem exists_normalized_of_weightOne (W : VertexOperatorAlgebra V)
    (hZ : W.CentrelessWeightOne) (hH : W.WeightOneH2Vanishes)
    (D : FirstOrderDeformation W) (hD : D.IsGraded) :
    ∃ (φ : V →ₗ[ℂ] V) (E : FirstOrderDeformation W),
      φ W.vacuum=0 ∧ GradePreserving W φ ∧ E.IsGraded ∧ E.InPoleForm ∧
      E.Y1=D.Y1-NonzeroDeform.deltaCochain W φ := by
  classical
  haveI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition W.grading
  obtain ⟨ψ,hψ⟩ := hH
    (weightOneCochain D hD hZ) (weightOneCochain_mem_twoCocycle D hD hZ)
  let φ := VertexOperatorAlgebra.extendWeightOne W ψ
  have hv : φ W.vacuum=0 := VertexOperatorAlgebra.extendWeightOne_vacuum ψ
  have hg : GradePreserving W φ := VertexOperatorAlgebra.gradePreserving_extendWeightOne ψ
  have hcob := NonzeroDeform.isCoboundary_deltaCochain W hv hg
  have hc : D.Y1-NonzeroDeform.deltaCochain W φ ∈ cocycles W :=
    Submodule.sub_mem _ (Y1_mem_cocycles D) (NonzeroDeform.deltaCochain_mem_cocycles W hv)
  let E := ofCocycle (D.Y1-NonzeroDeform.deltaCochain W φ) hc
  have hE : E.Y1=D.Y1-NonzeroDeform.deltaCochain W φ := rfl
  have hEg : E.IsGraded := by
    rw [isGraded_iff_Y1_mem_gradedCochains,hE]
    exact Submodule.sub_mem _ ((isGraded_iff_Y1_mem_gradedCochains D).mp hD)
      (coboundaries_le_gradedCochains W hcob)
  refine ⟨φ,E,hv,hg,hEg,?_,hE⟩
  intro a ha b hb
  have he := VertexOperatorAlgebra.coboundary_weightOne_eq_d₁₂ (W:=W) ψ ⟨a,ha⟩ ⟨b,hb⟩
  rw [hψ,weightOneCochain_coe] at he
  change D.smul₁ a 0 b-(W.smul (φ a) 0 b-φ (W.smul a 0 b)+W.smul a 0 (φ b))=0
  rw [he,sub_self]

end
end VOA.Deform

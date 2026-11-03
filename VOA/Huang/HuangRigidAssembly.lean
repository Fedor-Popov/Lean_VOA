import VOA.Huang.HuangRigidTwistDual

/-!
# Rigidity and modularity: assembly of `HuangRepInput`

Proved here (on top of `huangRigidityInput_holds` and `ribbonDualInput_of_nice`):

* `modelPivotal M` — the twist pivotal structure of a structural model with any right duals
  (`twistPivotal` for the actual transported conformal twist), and
  `modelPivotal_twistInput : M.PivotalTwistInput (modelPivotal M)`;
* `pivotal_eq_modelPivotal` — it is the ONLY pivotal structure satisfying `PivotalTwistInput`;
* `ribbonNumericalInput_iff` — `RibbonNumericalInput` is EQUIVALENT to the three numerical
  statements (S-matrix, dimensions, dimension multiplicativity) for `modelPivotal M`;
* `huangRibbonNumericalInput_iff : HuangRibbonNumericalInput ↔ HuangModularityInput`
  and `huangRepInput_of_modularity : HuangModularityInput → HuangRepInput`.

`HuangModularityInput` is the single remaining input: Huang's modularity theorem in the form
"the categorical `S̃` of the twist pivotal structure is Zhu's `S` up to `S₀₀` (one of the two
orientations), the twist-pivotal dimensions are the `d_a = S_{a0}/S_{00}`, and they are
multiplicative on pairs of simples". By `huangRibbonNumericalInput_iff` it is exactly as strong as
the previous residual `HuangRibbonNumericalInput` (no weakening, no strengthening).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangRigid

open CategoryTheory CategoryTheory.MonoidalCategory VOA VOA.Classification.COne
  VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.RepPackaging
  VOA.Huang.Tannakian

universe u

section Model

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (M : StructuralModel W) [RightRigidCategory M.C]

/-- The twist pivotal structure of a structural model (any right duals). -/
def modelPivotal : PivotalStructure M.C :=
  twistPivotal (θ := fun X => modelTwist M.E X) (fun f => modelTwist_naturality M.E f)

/-- The twist pivotal structure satisfies the genuine evaluation coherence. -/
theorem modelPivotal_twistInput : M.PivotalTwistInput (modelPivotal M) := fun X =>
  twistPiv_evaluation (fun X => modelTwist M.E X) X

/-- Uniqueness: `PivotalTwistInput` determines the pivotal structure. -/
theorem pivotal_eq_modelPivotal (P : PivotalStructure M.C) (hP : M.PivotalTwistInput P) :
    P = modelPivotal M :=
  twistPivotal_unique (θ := fun X => modelTwist M.E X) (fun f => modelTwist_naturality M.E f) P hP

variable (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)

/-- **`RibbonNumericalInput` is exactly the numerical content for the twist pivotal
structure.** -/
theorem ribbonNumericalInput_iff (hdual : M.RibbonDualInput) :
    M.RibbonNumericalInput D hD ↔
      (M.SMatchInput D hD (M.ribbon (modelPivotal M) hdual) ∧
        M.QDimMatchInput D (modelPivotal M) ∧ M.QDimTensorInput D (modelPivotal M)) := by
  constructor
  · rintro ⟨P, hd, hp, hS, hq, ht⟩
    obtain rfl := pivotal_eq_modelPivotal M P hp
    exact ⟨hS, hq, ht⟩
  · rintro ⟨hS, hq, ht⟩
    exact ⟨modelPivotal M, hdual, modelPivotal_twistInput M, hS, hq, ht⟩

end Model

/-- **Huang's modularity theorem, the single remaining input** (Huang 2008, *Rigidity and
modularity of vertex tensor categories*, CCM 10 (2008): `S̃_{ab} = S_{ab}/S_{00}`,
`dim M_a = S_{a0}/S_{00}`), stated for the canonical small model, EVERY choice of right duals,
and the (unique) twist pivotal structure. -/
def HuangModularityInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (r : RightRigidCategory (canonicalModel hW D hD).C),
    letI := r
    (canonicalModel hW D hD).SMatchInput D hD
        ((canonicalModel hW D hD).ribbon (modelPivotal (canonicalModel hW D hD))
          (ribbonDualInput_of_nice hW (canonicalModel hW D hD) D hD)) ∧
      (canonicalModel hW D hD).QDimMatchInput D (modelPivotal (canonicalModel hW D hD)) ∧
      (canonicalModel hW D hD).QDimTensorInput D (modelPivotal (canonicalModel hW D hD))

/-- **The ribbon residual is exactly Huang's modularity input.** -/
theorem huangRibbonNumericalInput_iff :
    HuangRibbonNumericalInput.{u} ↔ HuangModularityInput.{u} := by
  constructor
  · intro h V _ _ W hW D hD r
    letI := r
    exact ((ribbonNumericalInput_iff (canonicalModel hW D hD) D hD
      (ribbonDualInput_of_nice hW (canonicalModel hW D hD) D hD)).mp (h V W hW D hD r))
  · intro h V _ _ W hW D hD r
    letI := r
    exact ((ribbonNumericalInput_iff (canonicalModel hW D hD) D hD
      (ribbonDualInput_of_nice hW (canonicalModel hW D hD) D hD)).mpr (h V W hW D hD r))

/-- **`HuangRepInput` from Huang's modularity input alone**: rigidity
(`huangRigidityInput_holds`), the pivotal structure, its evaluation coherence, and `θ_{X'} = θ_X'`
are all proved. -/
theorem huangRepInput_of_modularity (h : HuangModularityInput.{u}) : HuangRepInput.{u} :=
  huangRepInput_of_inputs huangRigidityInput_holds (huangRibbonNumericalInput_iff.mpr h)

end VOA.Huang.HuangRigid

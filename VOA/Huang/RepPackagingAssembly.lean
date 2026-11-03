import VOA.Huang.RepPackagingFrame
import VOA.Huang.RepPackagingSimples

/-! Exact remaining ribbon inputs and assembly of the pinned Huang realization.

No residual below asks for limits, semisimplicity, smallness, linearity, a monoidal
structure, braiding, twist naturality, balancing, or the twist eigenvalues.
The existential pivotal structure in `RibbonNumericalInput` must satisfy all numerical
predicates and the pivotal evaluation coherence simultaneously; no arbitrary pivotal
structure is assumed canonical.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
noncomputable section
namespace VOA.Huang.TensorCat.RepPackaging
open VOA VOA.Classification.COne CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.Tannakian
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Huang rigidity, on the fixed proved small model. -/
def RigidityInput (M : StructuralModel W) : Prop := Nonempty (RightRigidCategory M.C)

namespace StructuralModel
variable (M : StructuralModel W) [RightRigidCategory M.C]

/-- Dual compatibility for the actual conformal twist, with the chosen right duals. -/
def RibbonDualInput : Prop :=
  ∀ X : M.C, (modelTwist M.E Xᘁ).hom = ((modelTwist M.E X).hom)ᘁ

/-- Evaluation compatibility of the pivotal structure with braiding and the actual twist.
This is the genuine ribbon coherence missing from the library's weak `PivotalStructure`.
It is an equality of evaluation morphisms, not a numerical dimension assumption. -/
def PivotalTwistInput (P : PivotalStructure M.C) : Prop :=
  ∀ X : M.C, ((P.piv X).hom ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ =
    ((modelTwist M.E X).hom ▷ Xᘁ) ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- Turaev's comparison at trivial twist is formal from genuine pivotal coherence. -/
theorem symDim_eq_of_pivotalTwist (P : PivotalStructure M.C) (hP : M.PivotalTwistInput P)
    (X : M.C) (hX : (modelTwist M.E X).hom = 𝟙 X) : symDim X = P.qdim X := by
  unfold PivotalStructure.qdim PivotalStructure.trL symDim
  simp only [id_whiskerRight, Category.id_comp]
  rw [hP X, hX]
  simp only [id_whiskerRight, Category.id_comp]

/-- Assemble the ribbon structure from a pivotal structure and twist-dual compatibility. -/
def ribbon (P : PivotalStructure M.C) (hdual : M.RibbonDualInput) : RibbonStructure M.C where
  toPivotalStructure := P
  twist := modelTwist M.E
  twist_naturality := modelTwist_naturality M.E
  balance := M.balance
  twist_dual := hdual

variable (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)

/-- The categorical double-braiding trace equals the pinned modular S matrix,
allowing exactly the two orientation conventions of the consumer. -/
def SMatchInput (R : RibbonStructure M.C) : Prop :=
  letI := M.fusion D hD
  ∀ a b : D.ι, D.S a b = (D.S00 : ℂ) * R.sTilde a b ∨
    D.S a b = (D.S00 : ℂ) * star (R.sTilde a b)

/-- Pivotal dimensions agree with the given positive numerical dimensions. -/
def QDimMatchInput (P : PivotalStructure M.C) : Prop :=
  ∀ a : D.ι, P.qdim (modelSimple M.E D a) = (D.d a : ℂ)

/-- Multiplicativity of the chosen pivotal dimension on pairs of labelled simples. -/
def QDimTensorInput (P : PivotalStructure M.C) : Prop :=
  ∀ a b : D.ι, P.qdim (modelSimple M.E D a ⊗ modelSimple M.E D b) =
    (D.d a : ℂ) * (D.d b : ℂ)

/-- Turaev's comparison at trivial twist; needed by the library's weak pivotal interface. -/
def SymDimInput (R : RibbonStructure M.C) : Prop :=
  letI := M.fusion D hD
  ∀ a : D.ι, R.T a = 1 → symDim (modelSimple M.E D a) = R.qdim (modelSimple M.E D a)

/-- The consumer's `symDim_eq` field is proved from pivotal compatibility. -/
theorem symDimInput_of_pivotalTwist (P : PivotalStructure M.C)
    (hdual : M.RibbonDualInput) (hP : M.PivotalTwistInput P) :
    M.SymDimInput D hD (M.ribbon P hdual) := by
  letI := M.fusion D hD
  intro a ha
  have ht := (M.ribbon P hdual).T_spec a
  rw [ha, one_smul] at ht
  exact M.symDim_eq_of_pivotalTwist P hP _ ht.symm

/-- The remaining pivotal, dual, and numerical assertions on one and the same structure.
The symmetric-dimension comparison is derived, not assumed. -/
def RibbonNumericalInput : Prop :=
  ∃ (P : PivotalStructure M.C) (hdual : M.RibbonDualInput),
    M.PivotalTwistInput P ∧ M.SMatchInput D hD (M.ribbon P hdual) ∧
      M.QDimMatchInput D P ∧ M.QDimTensorInput D P

/-- The twist eigenvalue is structural and is not a remaining analytic input. -/
theorem ribbon_T (P : PivotalStructure M.C) (hdual : M.RibbonDualInput) (a : D.ι) :
    letI := M.fusion D hD
    (M.ribbon P hdual).T a = Complex.exp (2 * Real.pi * Complex.I * (D.h a : ℂ)) := by
  letI := M.fusion D hD
  letI := modelSimple_isSimple M.E D hD a
  apply smul_left_injective ℂ (id_nonzero (modelSimple M.E D a))
  exact ((M.ribbon P hdual).T_spec a).trans (modelTwist_simple M.E D hD a)

/-- The precise consumer structure, with no categorical residual hypotheses. -/
def realization (P : PivotalStructure M.C) (hdual : M.RibbonDualInput)
    (hS : M.SMatchInput D hD (M.ribbon P hdual)) (hqdim : M.QDimMatchInput D P)
    (htensor : M.QDimTensorInput D P) (hsym : M.SymDimInput D hD (M.ribbon P hdual)) :
    HuangRibbonRealization.{u, 0, 0} W D :=
  letI := M.fusion D hD
  { C := M.C
    R := M.ribbon P hdual
    lab := Equiv.refl D.ι
    lab_unit := rfl
    T_eq := M.ribbon_T D hD P hdual
    S_eq := hS
    qdim_eq := hqdim
    qdim_tensor := htensor
    symDim_eq := hsym }

/-- The assembled realization is pinned to actual ordinary modules, including braiding,
twist, and every simple label. -/
theorem realization_isRep (P : PivotalStructure M.C) (hdual : M.RibbonDualInput)
    (hS : M.SMatchInput D hD (M.ribbon P hdual)) (hqdim : M.QDimMatchInput D P)
    (htensor : M.QDimTensorInput D P) (hsym : M.SymDimInput D hD (M.ribbon P hdual)) :
    IsRepRealization (M.realization D hD P hdual hS hqdim htensor hsym) := by
  refine ⟨M.F, M.stronglyRational, ?_⟩
  letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
  refine ⟨M.E.functor, inferInstance, M.additive, M.linearFunctor, M.monoidalFunctor, ?_, ?_, ?_⟩
  · exact M.braiding_eq
  · exact map_modelTwist M.E
  · exact fun a => ⟨modelSimpleIso M.E D a⟩

/-- Local assembly from rigidity and only the remaining ribbon assertions. -/
theorem exists_realization (h : M.RibbonNumericalInput D hD) :
    ∃ H : HuangRibbonRealization.{u, 0, 0} W D, IsRepRealization H := by
  obtain ⟨P, hd, hp, hS, hq, ht⟩ := h
  have hs := M.symDimInput_of_pivotalTwist D hD P hd hp
  exact ⟨M.realization D hD P hd hS hq ht hs, M.realization_isRep D hD P hd hS hq ht hs⟩

end StructuralModel

/-- Fix the structural model uniformly; all choices here are proved. -/
def canonicalModel (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    StructuralModel W :=
  structuralModel (fusionChoice_pbw hW.1) hW.1 D hD

/-- Rigidity is the only remaining requirement for right duals on the fixed small categories. -/
def HuangRigidityInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData),
    RigidityInput (canonicalModel hW D hD)

/-- With any chosen right duals, there exists a single compatible pivotal structure with
all the required numerical identifications. This does not quantify over arbitrary pivotals. -/
def HuangRibbonNumericalInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
    (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (r : RightRigidCategory (canonicalModel hW D hD).C),
    letI := r
    (canonicalModel hW D hD).RibbonNumericalInput D hD

/-- Huang's pinned realization is reduced to rigidity and the explicit ribbon/numerical fields. -/
theorem huangRepInput_of_inputs (hR : HuangRigidityInput.{u})
    (hN : HuangRibbonNumericalInput.{u}) : HuangRepInput.{u} := by
  intro V _ _ W hW D hD
  obtain ⟨r⟩ := hR V W hW D hD
  letI := r
  exact (canonicalModel hW D hD).exists_realization D hD (hN V W hW D hD r)

end VOA.Huang.TensorCat.RepPackaging

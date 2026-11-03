import VOA.Huang.NSSMove5RightTrace
import VOA.Huang.NSSMove5Powers

/-! # Direct adjoint calculation for inverse central rotation -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The adjoint of the first bend, with the pivotal cup retained. -/
def leftBendAdjoint (P : Pivotal C) {A X Y : C} (g : X ⊗ Y ⟶ A) :
    Y ⟶ Xᘁ ⊗ A :=
  (λ_ Y).inv ≫ P.cup X ▷ Y ≫ (α_ Xᘁ X Y).hom ≫ Xᘁ ◁ g

/-- The trace pairing through the left Hom adjunction. -/
theorem scalarTrace_leftBend (F : SphericalFusion C) {A X Y : C}
    (f : A ⟶ X ⊗ Y) (g : X ⊗ Y ⟶ A) :
    F.scalarTrace A (f ≫ g) =
      F.scalarTrace Y (leftBendAdjoint F.toPivotal g ≫ (leftDuality A X Y).symm f) := by
  rw [F.scalarTrace_comp_comm, ← F.scalarTrace_partialTraceLeft]
  congr 1
  dsimp [leftBendAdjoint, Pivotal.partialTraceLeft, leftDuality, tensorLeftHomEquiv]
  monoidal

/-- Right partial trace factors through the actual right Hom adjunction. -/
theorem partialTraceRight_comp (P : Pivotal C) {A X Y : C}
    (g : Y ⊗ X ⟶ A) (f : A ⟶ Y ⊗ X) :
    partialTraceRight P X (g ≫ f) =
      rightDuality Y X A g ≫
        (rightDuality A Xᘁ Y).symm (f ≫ Y ◁ (P.j X).hom) := by
  dsimp [partialTraceRight, pivotalCap, rightDuality, tensorRightHomEquiv]
  monoidal

/-- The trace pairing through the right Hom adjunction. -/
theorem scalarTrace_rightBend (F : SphericalFusion C) {A X Y : C}
    (f : A ⟶ Y ⊗ X) (d : Y ⟶ A ⊗ Xᘁ) :
    F.scalarTrace A (f ≫ (rightDuality Y X A).symm d) =
      F.scalarTrace Y
        (d ≫ (rightDuality A Xᘁ Y).symm (f ≫ Y ◁ (F.j X).hom)) := by
  rw [F.scalarTrace_comp_comm, ← scalarTrace_partialTraceRight, partialTraceRight_comp,
    LinearEquiv.apply_symm_apply]

/-- The forward half-braiding slides through the evaluation cap. -/
theorem halfBraiding_evaluation (A : Center C) (X : C) :
    (α_ Xᘁ A.1 X).hom ≫ Xᘁ ◁ (A.2.β X).hom ≫
      (α_ Xᘁ X A.1).inv ≫ ε_ X Xᘁ ▷ A.1 ≫ (λ_ A.1).hom =
    (A.2.β Xᘁ).inv ▷ X ≫ (α_ A.1 Xᘁ X).hom ≫
      A.1 ◁ ε_ X Xᘁ ≫ (ρ_ A.1).hom := by
  apply (cancel_epi ((A.2.β Xᘁ).hom ▷ X)).mp
  have h := A.2.naturality (ε_ X Xᘁ)
  rw [A.2.monoidal, halfBraiding_unit] at h
  simpa only [Category.assoc, ← comp_whiskerRight_assoc,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc] using
    congrArg (fun f => (α_ A.1 Xᘁ X).hom ≫ f ≫ (λ_ A.1).hom) h.symm

/-- The explicit forward partial trace is the reverse-map bend of the cap slide. -/
theorem forwardPartialTrace_eq_bend (P : Pivotal C) (A : Center C) (X Y : C)
    (g : X ⊗ Y ⟶ A.1) :
    P.partialTraceLeft X
      ((α_ X Y X).inv ≫ g ▷ X ≫ (A.2.β X).hom) =
      (rightDuality Y X A.1).symm
        (leftBendAdjoint P g ≫ (A.2.β Xᘁ).inv) := by
  calc
    _ = leftBendAdjoint P g ▷ X ≫ (α_ Xᘁ A.1 X).hom ≫
        Xᘁ ◁ (A.2.β X).hom ≫ (α_ Xᘁ X A.1).inv ≫
        ε_ X Xᘁ ▷ A.1 ≫ (λ_ A.1).hom := by
      dsimp [Pivotal.partialTraceLeft, leftBendAdjoint]
      monoidal
    _ = _ := by
      rw [halfBraiding_evaluation]
      dsimp [rightDuality, tensorRightHomEquiv]
      monoidal

/-- Direct adjoint formula for inverse rotation, with no inversion of a partial trace. -/
theorem centerRotation_symm_trace_pair (F : SphericalFusion C) (A : Center C)
    (X Y : C) (f : A.1 ⟶ Y ⊗ X) (g : X ⊗ Y ⟶ A.1) :
    F.scalarTrace A.1 ((centerRotation F.toPivotal A X Y).symm f ≫ g) =
      F.scalarTrace A.1 (f ≫ F.toPivotal.partialTraceLeft X
        ((α_ X Y X).inv ≫ g ▷ X ≫ (A.2.β X).hom)) := by
  rw [scalarTrace_leftBend, forwardPartialTrace_eq_bend, scalarTrace_rightBend]
  have hb : (leftDuality A.1 X Y).symm
      ((centerRotation F.toPivotal A X Y).symm f) =
      (A.2.β Xᘁ).inv ≫
        (rightDuality A.1 Xᘁ Y).symm (f ≫ Y ◁ (F.j X).hom) := by
    simp [centerRotation, homCongr]
  rw [hb, Category.assoc]

/-- The single forward operator is the trace adjoint of the inverse rotation. -/
theorem forwardBlockOperator_single_pair (F : SphericalFusion C) (A : Center C)
    (V : C) (k : ℕ) (f : A.1 ⟶ tensorPower V (k + 1))
    (g : tensorPower V (k + 1) ⟶ A.1) :
    F.scalarTrace A.1 ((generalizedRotation F.toPivotal A V k).symm f ≫ g) =
      F.scalarTrace A.1 (f ≫ forwardBlockOperator F.toPivotal A V
        (tensorPower V (k + 1)) (blockReassociation V 0 k).hom g) := by
  have hr : (blockReassociation V 0 k).hom = (appendPower V k).inv := by
    apply (cancel_mono (appendPower V k).hom).mp
    rw [← blockReassociation_right_zero, blockReassociation_swap, Iso.inv_hom_id,
      blockReassociation_right_zero, Iso.inv_hom_id]
  rw [hr]
  cases k with
  | zero =>
    have h := centerRotation_symm_trace_pair F A V (𝟙_ C)
      (f ≫ (λ_ V).inv) ((ρ_ V).hom ≫ g)
    have he : (λ_ V).inv ≫ F.toPivotal.partialTraceLeft V
        ((α_ V (𝟙_ C) V).inv ≫ ((ρ_ V).hom ≫ g) ▷ V ≫ (A.2.β V).hom) =
        F.toPivotal.partialTraceLeft V (g ▷ V ≫ (A.2.β V).hom) := by
      rw [← F.toPivotal.partialTraceLeft_precomp]
      congr 1
      monoidal
    simpa only [generalizedRotation, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.symm_symm, homCongr, LinearEquiv.symm_mk, LinearEquiv.coe_mk,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, Iso.symm_inv, Category.assoc,
      he, forwardBlockOperator, Pivotal.partialTraceLeftLinear,
      LinearMap.coe_mk, AddHom.coe_mk, tensorPower, appendPower, Category.id_comp]
      using h
  | succ k =>
    have h := centerRotation_symm_trace_pair F A V (tensorPower V (k + 1))
      (f ≫ (appendPower V k).inv) g
    have he : (appendPower V k).inv ≫ F.toPivotal.partialTraceLeft V
        ((α_ V (tensorPower V (k + 1)) V).inv ≫ g ▷ V ≫ (A.2.β V).hom) =
        F.toPivotal.partialTraceLeft V
          ((appendPower V (k + 1)).inv ≫ g ▷ V ≫ (A.2.β V).hom) := by
      rw [← F.toPivotal.partialTraceLeft_precomp]
      simp only [appendPower, Iso.trans_inv, whiskerLeftIso_inv, Category.assoc]
    simpa only [generalizedRotation, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      homCongr, LinearEquiv.symm_mk, LinearEquiv.coe_mk, Iso.refl_hom,
      Category.id_comp, Category.assoc, he, forwardBlockOperator,
      Pivotal.partialTraceLeftLinear, LinearMap.coe_mk, AddHom.coe_mk] using h

end VOA.Huang.NSCongruence

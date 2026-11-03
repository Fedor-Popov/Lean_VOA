import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Spherical fusion categories for the Ng–Schauenburg route

This file has no VOA imports. Unlike the earlier `TensorCat.PivotalStructure`,
`Pivotal` includes monoidality. The dual tensor comparison is pinned by its
evaluation equation, so it cannot be chosen independently of the rigid structure.
The unit comparison is pinned in the same way. These comparisons are supplied
as data because Mathlib does not yet construct the dual of a tensor product.

References: Ng–Schauenburg, arXiv:math/0601012, §2; arXiv:0806.2493, §1.
-/

noncomputable section
set_option linter.unusedSectionVars false

universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits

-- Use the category's chosen duals uniformly, including on the tensor unit.
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The evaluation for the reversed tensor product of two chosen right duals. -/
def tensorDualEvaluation (X Y : C) : (Yᘁ ⊗ Xᘁ) ⊗ (X ⊗ Y) ⟶ 𝟙_ C :=
  (α_ _ _ _).hom ≫ Yᘁ ◁ (α_ _ _ _).inv ≫
    Yᘁ ◁ (ε_ X Xᘁ ▷ Y) ≫ Yᘁ ◁ (λ_ Y).hom ≫ ε_ Y Yᘁ

/-- A natural **monoidal** pivotal isomorphism for the chosen right duals.
The evaluation equations characterize the canonical dual comparisons uniquely.
No rotation identity or indicator theorem is assumed here. -/
structure Pivotal where
  dualTensor : ∀ X Y : C, Yᘁ ⊗ Xᘁ ≅ (X ⊗ Y)ᘁ
  dualTensor_eval : ∀ X Y : C,
    (dualTensor X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (X ⊗ Y)ᘁ =
      tensorDualEvaluation C X Y
  dualUnit : 𝟙_ C ≅ (𝟙_ C)ᘁ
  dualUnit_eval : dualUnit.hom ▷ (𝟙_ C) ≫ ε_ (𝟙_ C) (𝟙_ C)ᘁ = (λ_ (𝟙_ C)).hom
  j : ∀ X : C, X ≅ (Xᘁ)ᘁ
  naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (j Y).hom = (j X).hom ≫ (fᘁ)ᘁ
  monoidal : ∀ X Y : C,
    (j (X ⊗ Y)).hom = ((j X).hom ⊗ₘ (j Y).hom) ≫
      (dualTensor Yᘁ Xᘁ).hom ≫ ((dualTensor X Y).inv)ᘁ
  unit : (j (𝟙_ C)).hom = dualUnit.hom ≫ (dualUnit.inv)ᘁ

namespace Pivotal

variable {C} (P : Pivotal C)

/-- Right pivotal trace, valued in endomorphisms of the tensor unit. -/
def traceRight {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (P.j X).hom ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ

/-- Left pivotal trace. -/
def traceLeft {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ ((P.j X).inv ≫ f) ≫ ε_ X Xᘁ

def IsSpherical : Prop := ∀ (X : C) (f : X ⟶ X), P.traceLeft f = P.traceRight f

end Pivotal

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- A complex spherical fusion category, with an explicit finite semisimple
decomposition and the scalar identification of the endomorphisms of its unit.
Rigidity and linear monoidal structure are ambient typeclasses. Right rigidity
together with the pivotal isomorphism also supplies left duals. -/
structure SphericalFusion extends Pivotal C where
  Label : Type
  [labelsFinite : Fintype Label]
  simple : Label → C
  simple_isSimple : ∀ i, Simple (simple i)
  unitLabel : Label
  unitIso : simple unitLabel ≅ 𝟙_ C
  distinct : ∀ i j, Nonempty (simple i ≅ simple j) → i = j
  decomposition : ∀ X : C, ∃ (n : ℕ) (a : Fin n → Label),
    Nonempty (X ≅ ⨁ fun k => simple (a k))
  homFinite : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)
  unitScalar : ℂ ≃ₗ[ℂ] (𝟙_ C ⟶ 𝟙_ C)
  unitScalar_apply : ∀ z : ℂ, unitScalar z = z • 𝟙 (𝟙_ C)
  spherical : toPivotal.IsSpherical

attribute [instance] SphericalFusion.labelsFinite

namespace SphericalFusion

variable {C} (F : SphericalFusion C)

def dimension (X : C) : ℂ := F.unitScalar.symm (F.traceRight (𝟙 X))

/-- Global dimension, conventionally denoted `D²`; no square-root choice. -/
def globalDimension : ℂ := ∑ i : F.Label, F.dimension (F.simple i) ^ 2

/-- Multiplicity of an arbitrary object as the target of a fusion product.
For a simple target this is the usual fusion coefficient. -/
def fusionMultiplicity (i j : F.Label) (V : C) : ℕ :=
  Module.finrank ℂ (V ⟶ F.simple i ⊗ F.simple j)

include F in
theorem finrank_end_unit : Module.finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1 := by
  rw [← F.unitScalar.finrank_eq]
  exact Module.finrank_self ℂ

include F in
theorem simple_unit : Simple (𝟙_ C) := by
  letI := F.simple_isSimple F.unitLabel
  exact Simple.of_iso F.unitIso.symm

end SphericalFusion

end VOA.Huang.NgSchauenburg

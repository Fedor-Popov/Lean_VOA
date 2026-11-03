import VOA.Huang.NSSMove2Diagrams

/-! # Complete simple-channel matrix tests for the mixed exchange

The tests include every pair of multiplicity indices in every simple block.
Their equivalence to the open-morphism exchange is proved; the matrix
identities themselves remain a categorical obligation.
-/
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

/-- The mixed half-braiding is the ordinary braiding after inverse monodromy
on its second factor. This is an equality of open morphisms. -/
theorem mixedCenter_halfBraiding_inverseMonodromy (X Y U : C) :
    ((mixedCenter X Y).2.β U).hom =
      (α_ X Y U).hom ≫ X ◁ ((β_ U Y).inv ≫ (β_ Y U).inv) ≫
        (α_ X Y U).inv ≫ (β_ (X ⊗ Y) U).hom := by
  rw [mixedCenter_halfBraiding, BraidedCategory.braiding_tensor_left_hom]
  simp

/-- A matrix coefficient between two multiplicity bases in the same simple block. -/
def channelMatrixEntry (F : SphericalFusion C) (X Y : C) (t : F.Label)
    (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) : (X ⟶ Y) →ₗ[ℂ] ℂ where
  toFun f := (F.simpleHomBasis Y t).repr (F.simpleHomBasis X t α ≫ f) β
  map_add' := by intros; simp [Preadditive.comp_add]
  map_smul' := by intros; simp

/-- Each coefficient is the normalized categorical trace of its matrix unit. -/
theorem channelMatrixEntry_eq_trace (F : SphericalFusion C) (X Y : C) (t : F.Label)
    (α : Fin (Module.finrank ℂ (F.simple t ⟶ X)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ Y))) (f : X ⟶ Y) :
    channelMatrixEntry F X Y t α β f =
      F.scalarTrace (F.simple t)
        (F.simpleHomBasis X t α ≫ f ≫ F.compositionDual (F.simpleHomBasis Y t) β) /
        F.dimension (F.simple t) := by
  apply (eq_div_iff (F.dimension_simple_ne_zero t)).mpr
  have h := congrArg (F.scalarTrace (F.simple t))
    (F.comp_compositionDual (F.simpleHomBasis Y t) β (F.simpleHomBasis X t α ≫ f))
  simpa only [channelMatrixEntry, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
    F.scalarTrace_id, smul_eq_mul, Category.assoc] using h.symm

/-- Semisimplicity makes the full set of matrix coefficients faithful. -/
theorem hom_eq_iff_channelMatrixEntry (F : SphericalFusion C) (X Y : C)
    (f g : X ⟶ Y) :
    f = g ↔ ∀ t α β, channelMatrixEntry F X Y t α β f =
      channelMatrixEntry F X Y t α β g := by
  constructor
  · intro h; subst g; intros; rfl
  · intro h
    apply F.hom_ext_from_simples
    intro t q
    rw [← (F.simpleHomBasis X t).sum_repr q]
    simp only [Preadditive.sum_comp, Linear.smul_comp]
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    apply (F.simpleHomBasis Y t).repr.injective
    ext β
    exact h t α β

/-- Every multiplicity matrix coefficient of the exchange, not just its trace. -/
def MixedMugerMatrixElements (F : SphericalFusion C) : Prop :=
  ∀ (a b i j t : F.Label)
    (α : Fin (Module.finrank ℂ (F.simple t ⟶ F.simple i ⊗ F.simple j)))
    (β : Fin (Module.finrank ℂ (F.simple t ⟶ F.simple j ⊗ F.simple i))),
    channelMatrixEntry F _ _ t α β
        (inverseChannelCrossing F (mixedCenter (F.simple a) (F.simple b)) i j) =
      ∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q *
        channelMatrixEntry F _ _ t α β
          (forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j)

/-- The finite matrix test is exactly equivalent to the local open-morphism exchange. -/
theorem mixedMugerExchange_iff_matrixElements (F : SphericalFusion C) :
    MixedMugerExchange F ↔ MixedMugerMatrixElements F := by
  constructor
  · intro h a b i j t α β
    rw [h a b i j]
    simp
  · intro h a b i j
    apply (hom_eq_iff_channelMatrixEntry F _ _ _ _).mpr
    intro t α β
    simpa using h a b i j t α β

end VOA.Huang.NSCongruence

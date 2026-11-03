import VOA.Huang.NgSchauenburgAveraging

/-! # Partial trace calculus for the half-braiding average

The closed tensor factor can be moved through an arbitrary morphism, resolved
into simple channels, and traced in stages. These are identities for the actual
pivotal partial trace, without a braiding on the base category.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

namespace Pivotal

/-- The cup-cap partial trace is linear in its open diagram. -/
def partialTraceLeftLinear (P : Pivotal C) (U X Y : C) :
    (U ⊗ X ⟶ U ⊗ Y) →ₗ[ℂ] (X ⟶ Y) where
  toFun := P.partialTraceLeft U
  map_add' := by
    intros
    simp [partialTraceLeft, MonoidalPreadditive.whiskerLeft_add,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul' := by intros; simp [partialTraceLeft]

/-- A right-hand spectator strand may be kept outside the partial trace. -/
theorem partialTraceLeft_whisker (P : Pivotal C) (U : C) {X Y : C}
    (f : U ⊗ X ⟶ U ⊗ Y) (V : C) :
    P.partialTraceLeft U
      ((α_ U X V).inv ≫ f ▷ V ≫ (α_ U Y V).hom) =
        P.partialTraceLeft U f ▷ V := by
  dsimp [partialTraceLeft]
  monoidal

end Pivotal

variable [HasKernels C] [HasFiniteBiproducts C]
namespace SphericalFusion
variable (F : SphericalFusion C)

/-- The perfect categorical trace pairing detects equality of morphisms. -/
theorem hom_ext_trace {X Y : C} {f g : X ⟶ Y}
    (h : ∀ q : Y ⟶ X, F.scalarTrace X (f ≫ q) = F.scalarTrace X (g ≫ q)) :
    f = g := by
  apply F.tracePairing_injective Y X
  apply LinearMap.ext
  intro q
  simpa only [tracePairing_apply, F.scalarTrace_comp_comm q] using h q

/-- Dinaturality in the closed strand, including noninvertible morphisms. -/
theorem partialTraceLeft_dinatural {U V X Y : C} (a : U ⟶ V)
    (f : V ⊗ X ⟶ U ⊗ Y) :
    F.toPivotal.partialTraceLeft U (a ▷ X ≫ f) =
      F.toPivotal.partialTraceLeft V (f ≫ a ▷ Y) := by
  apply F.hom_ext_trace
  intro g
  rw [← F.toPivotal.partialTraceLeft_postcomp,
    ← F.toPivotal.partialTraceLeft_postcomp,
    F.scalarTrace_partialTraceLeft, F.scalarTrace_partialTraceLeft]
  rw [Category.assoc, F.scalarTrace_comp_comm (a ▷ X)]
  congr 1
  rw [Category.assoc, whisker_exchange]
  simp only [Category.assoc]

/-- Conjugating the closed strand by an isomorphism does not change its trace. -/
theorem partialTraceLeft_iso {U V X Y : C} (e : U ≅ V)
    (f : V ⊗ X ⟶ V ⊗ Y) :
    F.toPivotal.partialTraceLeft U (e.hom ▷ X ≫ f ≫ e.inv ▷ Y) =
      F.toPivotal.partialTraceLeft V f := by
  rw [F.partialTraceLeft_dinatural e.hom]
  simp

/-- Fubini for the actual spherical partial trace, with associators explicit. -/
theorem partialTraceLeft_tensor (U V : C) {X Y : C}
    (f : (U ⊗ V) ⊗ X ⟶ (U ⊗ V) ⊗ Y) :
    F.toPivotal.partialTraceLeft (U ⊗ V) f =
      F.toPivotal.partialTraceLeft V (F.toPivotal.partialTraceLeft U
        ((α_ U V X).inv ≫ f ≫ (α_ U V Y).hom)) := by
  apply F.hom_ext_trace
  intro g
  rw [← F.toPivotal.partialTraceLeft_postcomp,
    ← F.toPivotal.partialTraceLeft_postcomp,
    ← F.toPivotal.partialTraceLeft_postcomp,
    F.scalarTrace_partialTraceLeft, F.scalarTrace_partialTraceLeft,
    F.scalarTrace_partialTraceLeft]
  simp only [Category.assoc]
  rw [F.scalarTrace_comp_comm (α_ U V X).inv]
  congr 1
  monoidal

/-- Resolve the closed strand by composition-dual simple channels. -/
theorem partialTraceLeft_eq_sum_channels (U : C) {X Y : C}
    (f : U ⊗ X ⟶ U ⊗ Y) :
    F.toPivotal.partialTraceLeft U f = ∑ i, ∑ a,
      F.toPivotal.partialTraceLeft (F.simple i)
        (F.simpleHomBasis U i a ▷ X ≫ f ≫
          F.compositionDual (F.simpleHomBasis U i) a ▷ Y) := by
  calc
    _ = F.toPivotal.partialTraceLeft U
        ((∑ i, ∑ a, F.compositionDual (F.simpleHomBasis U i) a ≫
          F.simpleHomBasis U i a) ▷ X ≫ f) := by
      rw [F.sum_compositionDual_comp, id_whiskerRight, Category.id_comp]
    _ = _ := by
      simp only [sum_whiskerRight, Preadditive.sum_comp,
        comp_whiskerRight, Category.assoc]
      change F.toPivotal.partialTraceLeftLinear U X Y _ = _
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      simpa only [Pivotal.partialTraceLeftLinear, LinearMap.coe_mk,
        AddHom.coe_mk, Category.assoc] using
        F.partialTraceLeft_dinatural (F.compositionDual (F.simpleHomBasis U i) a)
          (F.simpleHomBasis U i a ▷ X ≫ f)

end SphericalFusion
end VOA.Huang.NgSchauenburg

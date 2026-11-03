import VOA.Huang.NgSchauenburgIndicators
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Modular categories and the Bantay formula target

Ribbon compatibility is pinned to the Drinfeld morphism, not just to balancing.
`BantayFormula` is a named theorem target, **not a proved theorem or an axiom**.
All structures and statements concern abstract categories only.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Drinfeld morphism `u_X : X → X**`, with the inverse-braiding convention
of Ng–Schauenburg, math/0601012 §2. -/
def drinfeldMorphism (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (λ_ X).inv ≫ η_ Xᘁ (Xᘁ)ᘁ ▷ X ≫ (α_ _ _ _).hom ≫
    Xᘁ ◁ (β_ X (Xᘁ)ᘁ).inv ≫ (α_ _ _ _).inv ≫
    ε_ X Xᘁ ▷ (Xᘁ)ᘁ ≫ (λ_ _).hom

/-- The twist is compatible with the specified pivotal structure: `j = u θ`.
This condition rules out choosing an unrelated pivotal structure and twist. -/
structure Ribbon (P : Pivotal C) where
  twist : ∀ X : C, X ≅ X
  naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (twist Y).hom = (twist X).hom ≫ f
  balance : ∀ X Y : C, (twist (X ⊗ Y)).hom =
    ((twist X).hom ⊗ₘ (twist Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom
  unit : (twist (𝟙_ C)).hom = 𝟙 (𝟙_ C)
  dual : ∀ X : C, (twist Xᘁ).hom = ((twist X).hom)ᘁ
  pivotal : ∀ X : C, (P.j X).hom = (twist X).hom ≫ drinfeldMorphism X

/-- Unnormalized categorical S in the NS (1.6) convention: the spherical
trace of double braiding of `X_i*` with `X_j`. The dual on the first index
is essential for pairing this S with the positive twist T. -/
def categoricalS (F : SphericalFusion C) : Matrix F.Label F.Label ℂ :=
  fun i j => F.unitScalar.symm (F.traceRight
    ((β_ (F.simple i)ᘁ (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)ᘁ).hom))

open Classical in
/-- Nondegeneracy of the actual categorical S-matrix. -/
def NondegenerateS (F : SphericalFusion C) : Prop := (categoricalS F).det ≠ 0

/-- A modular structure on the given spherical fusion category. -/
structure Modular (F : SphericalFusion C) extends Ribbon F.toPivotal where
  nondegenerate : NondegenerateS F

namespace Ribbon

variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- Twist eigenvalue of a chosen simple; existence follows from Schur's lemma. -/
def twistScalar (i : F.Label) : ℂ := by
  letI := F.simple_isSimple i
  letI := F.homFinite (F.simple i) (F.simple i)
  exact (endomorphism_simple_eq_smul_id ℂ (R.twist (F.simple i)).hom).choose

theorem twistScalar_smul_id (i : F.Label) :
    R.twistScalar i • 𝟙 (F.simple i) = (R.twist (F.simple i)).hom := by
  letI := F.simple_isSimple i
  letI := F.homFinite (F.simple i) (F.simple i)
  exact (endomorphism_simple_eq_smul_id ℂ (R.twist (F.simple i)).hom).choose_spec

theorem twistScalar_ne_zero (i : F.Label) : R.twistScalar i ≠ 0 := by
  letI := F.simple_isSimple i
  intro h
  have he := R.twistScalar_smul_id i
  rw [h, zero_smul] at he
  exact (isIso_iff_nonzero (R.twist (F.simple i)).hom).mp inferInstance he.symm

end Ribbon

/-- Ng–Schauenburg math/0601012 Theorem 7.5, extended to arbitrary objects
by additivity. The denominator is global dimension (`D²`), not its square.
This is an unproved, non-numerical categorical target. -/
def BantayFormula (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ (V : C) (n : ℕ), 0 < n →
    indicator F.toPivotal V n = (F.globalDimension)⁻¹ *
      ∑ i : F.Label, ∑ j : F.Label,
        (F.fusionMultiplicity i j V : ℂ) * F.dimension (F.simple i) *
          F.dimension (F.simple j) * (M.twistScalar i / M.twistScalar j) ^ n

/-- The FS exponent is finite and equals the order of the twist of a modular
category (math/0601012 Theorem 7.7). `orderOf = 0` denotes infinite order. -/
def ModularExponentTheorem (F : SphericalFusion C) (M : Modular F) : Prop :=
  0 < fsExponent F ∧
    fsExponent F = orderOf (fun i : F.Label => M.twistScalar i)

end VOA.Huang.NgSchauenburg

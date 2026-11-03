import VOA.Huang.NgSchauenburgModular
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Integer-indexed generalized indicators and the equivariance contract

For positive `m`, use the integer powers of the single rotation on `Hom(X,V^m)`.
For `m = 0`, use the closed half-braiding diagram explicitly. For negative `m`,
use spherical duality `ν^X_{-m,-l}(V) = ν^X_{m,l}(V*)`.
Thus the negative-index convention is only offered for a spherical category.
Agreement with the all-integer block diagram of NS Definition 2.1 is an open
comparison theorem; the positive rotation and zero-index diagram are explicit.

The full equivariance theorem is **only stated**, under a pinned canonical
center representation. No arbitrary representation or arbitrary indicator family
is substituted for the categorical objects.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Tensor powers with the signed-power convention of NS §2. -/
def signedTensorPower (V : C) (m : ℤ) : C :=
  if 0 ≤ m then tensorPower V m.toNat else tensorPower Vᘁ m.natAbs

/-- Close a half-braiding around a morphism `X → 1`, using a strand `W`.
This is `E^{(0,l)}` when `W = V^l`, including the negative-power convention. -/
def closedRotation (P : Pivotal C) (X : Center C) (W : C) :
    Module.End ℂ (X.1 ⟶ 𝟙_ C) where
  toFun f := (ρ_ X.1).inv ≫ X.1 ◁ η_ Wᘁ (Wᘁ)ᘁ ≫
    X.1 ◁ (Wᘁ ◁ (P.j W).inv) ≫ (α_ _ _ _).inv ≫
    (X.2.β Wᘁ).hom ▷ W ≫ (α_ _ _ _).hom ≫
    Wᘁ ◁ (f ▷ W) ≫ Wᘁ ◁ (λ_ W).hom ≫ ε_ W Wᘁ
  map_add' f g := by
    simp [MonoidalPreadditive.add_whiskerRight, MonoidalPreadditive.whiskerLeft_add,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul' z f := by simp

/-- Positive first index and arbitrary integer second index. -/
def generalizedIndicatorInt (P : Pivotal C) (X : Center C) (V : C) (n : ℕ) (l : ℤ) : ℂ :=
  LinearMap.trace ℂ (X.1 ⟶ tensorPower V (n + 1))
    ((generalizedRotation P X V n) ^ l).toLinearMap

/-- All integer indices, extended by spherical duality for negative first index.
No modular representation occurs in this definition. -/
def generalizedIndicatorAll (F : SphericalFusion C) (X : Center C) (V : C)
    (m l : ℤ) : ℂ :=
  if 0 < m then generalizedIndicatorInt F.toPivotal X V (m.toNat - 1) l
  else if m = 0 then
    LinearMap.trace ℂ (X.1 ⟶ 𝟙_ C) (closedRotation F.toPivotal X (signedTensorPower V l))
  else generalizedIndicatorInt F.toPivotal X Vᘁ (m.natAbs - 1) (-l)

theorem generalizedIndicatorInt_zero (F : SphericalFusion C) (X : Center C) (V : C)
    (n : ℕ) : generalizedIndicatorInt F.toPivotal X V n 0 =
      (Module.finrank ℂ (X.1 ⟶ tensorPower V (n + 1)) : ℂ) := by
  letI := F.homFinite X.1 (tensorPower V (n + 1))
  simp [generalizedIndicatorInt, LinearMap.trace_id]

theorem generalizedIndicatorAll_positive (F : SphericalFusion C) (X : Center C) (V : C)
    (n : ℕ) (l : ℤ) : generalizedIndicatorAll F X V (n + 1) l =
      generalizedIndicatorInt F.toPivotal X V n l := by
  simp [generalizedIndicatorAll]

/-- Linear extension on the specified finite family of center simples. -/
def equivariantIndicator (F : SphericalFusion C) {ι : Type*} [Fintype ι]
    (X : ι → Center C) (V : C) (m l : ℤ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ i, z i * generalizedIndicatorAll F (X i) V m l
  map_add' z w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.mul_sum, mul_assoc]

theorem equivariantIndicator_basis (F : SphericalFusion C) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (X : ι → Center C) (V : C) (m l : ℤ) (i : ι) :
    equivariantIndicator F X V m l (Pi.single i 1) = generalizedIndicatorAll F (X i) V m l := by
  simp [equivariantIndicator, Pi.single_apply]

/-- The outer involution `γ ↦ diag(1,-1) γ diag(1,-1)` from NS (5.2). -/
def modularInvolution (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two]
    change γ 0 0 * γ 1 1 - (-γ 0 1) * (-γ 1 0) = 1
    rw [neg_mul_neg]
    have h := γ.property
    rw [Matrix.det_fin_two] at h
    exact h⟩

theorem modularInvolution_involutive (γ : SL(2, ℤ)) :
    modularInvolution (modularInvolution γ) = γ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularInvolution]

theorem modularInvolution_mul (γ δ : SL(2, ℤ)) :
    modularInvolution (γ * δ) = modularInvolution γ * modularInvolution δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularInvolution, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The outer involution as an honest group automorphism. -/
def modularOuterAutomorphism : SL(2, ℤ) ≃* SL(2, ℤ) where
  toFun := modularInvolution
  invFun := modularInvolution
  left_inv := modularInvolution_involutive
  right_inv := modularInvolution_involutive
  map_mul' := modularInvolution_mul

/-- Right action on the integer row `(m,l)`. -/
def rowAction (m l : ℤ) (γ : SL(2, ℤ)) : ℤ × ℤ :=
  (m * γ 0 0 + l * γ 1 0, m * γ 0 1 + l * γ 1 1)

theorem modularInvolution_S : modularInvolution ModularGroup.S = ModularGroup.S⁻¹ := by
  decide

theorem modularInvolution_T : modularInvolution ModularGroup.T = ModularGroup.T⁻¹ := by
  decide

/-- Drinfeld morphism on the underlying object of a central object. -/
def centralDrinfeldMorphism (X : Center C) : X.1 ⟶ (X.1ᘁ)ᘁ :=
  (λ_ X.1).inv ≫ η_ X.1ᘁ (X.1ᘁ)ᘁ ▷ X.1 ≫ (α_ _ _ _).hom ≫
    X.1ᘁ ◁ (X.2.β (X.1ᘁ)ᘁ).inv ≫ (α_ _ _ _).inv ≫
    ε_ X.1 X.1ᘁ ▷ (X.1ᘁ)ᘁ ≫ (λ_ _).hom

section CenterRepresentation

-- These structures on the center must still be constructed from `F`.
variable [RightRigidCategory (Center C)] [Preadditive (Center C)] [Linear ℂ (Center C)]
  [MonoidalPreadditive (Center C)] [MonoidalLinear ℂ (Center C)]
  [HasKernels (Center C)] [HasFiniteBiproducts (Center C)]

/-- Pin the pivotal traces of the center to those of the underlying category. -/
def CenterTraceCompatible (F : SphericalFusion C) (Z : SphericalFusion (Center C)) : Prop :=
  ∀ (X : Center C) (f : X ⟶ X),
    Z.unitScalar.symm (Z.traceRight f) = F.unitScalar.symm (F.traceRight f.f)

/-- The canonical center representation, with the *specific* normalization
`S/dim(C)` and raw categorical twist `T`, as in NS (5.1). -/
def CanonicalCenterRepresentation (F : SphericalFusion C) (Z : SphericalFusion (Center C))
    (M : Modular Z) (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ))) : Prop :=
  CenterTraceCompatible F Z ∧
    (∀ i, (F.j (Z.simple i).1).hom =
      M.twistScalar i • centralDrinfeldMorphism (Z.simple i)) ∧
    (∀ z i, ρ ModularGroup.S z i =
      (F.globalDimension)⁻¹ * ∑ j, categoricalS Z i j * z j) ∧
    (∀ z i, ρ ModularGroup.T z i = M.twistScalar i * z i)

/-- NS Theorem 5.4, with integer row action and its necessary outer involution.
This is a named true theorem target, not a proof of equivariance. -/
def GeneralizedIndicatorEquivariance (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z) : Prop :=
  ∀ (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ))),
    CanonicalCenterRepresentation F Z M ρ → ∀ (V : C) (m l : ℤ) (γ : SL(2, ℤ)) (z : Z.Label → ℂ),
      equivariantIndicator F Z.simple V (rowAction m l γ).1 (rowAction m l γ).2 z =
        equivariantIndicator F Z.simple V m l (ρ (modularInvolution γ) z)

end CenterRepresentation

end VOA.Huang.NgSchauenburg

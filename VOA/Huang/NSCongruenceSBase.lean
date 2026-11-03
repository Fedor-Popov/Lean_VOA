/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceSMoveSplit

/-!
# The base row of the `S` move

`MixedBaseSMove` is reduced to the ρ-free value of the zero-degree (closed-rotation) mixed
indicator, `MixedZeroIndicatorValue`: on `X_ij = X_i ⊠ X_j` with probe `X_a`,
`ν_{0,-1} = [i = j*] · S_{a j} / d_j`.  The `S²` action of the mixed representation is computed
(`mixedRepresentation_S_sq_apply`: charge conjugation on both labels).
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- Charge conjugation as an invertible matrix. -/
def chargeConjugationUnit (F : SphericalFusion C) : (Matrix F.Label F.Label ℂ)ˣ :=
  ⟨chargeConjugation F, chargeConjugation F, chargeConjugation_sq F, chargeConjugation_sq F⟩

open Classical in
/-- `S²` acts in the mixed representation by charge conjugation on both labels. -/
theorem mixedRepresentation_S_sq_apply (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (z : F.Label × F.Label → ℂ) (k l : F.Label) :
    mixedRepresentation ρ (ModularGroup.S ^ 2) z (k, l) = z (F.dualLabel k, F.dualLabel l) := by
  have hmat : mixedS F M * mixedS F M = matrixDouble (chargeConjugationUnit F) := by
    change matrixDouble (categoricalSUnit F M) * matrixDouble (categoricalSUnit F M) = _
    rw [← map_mul]
    apply matrixDouble_eq_of_smul _ _ F.globalDimension_ne_zero
    change categoricalS F * categoricalS F = _
    rw [categoricalS_sq F M]
    rfl
  rw [pow_two, map_mul, LinearEquiv.mul_apply, mixedRepresentation_S F M ρ hr,
    mixedRepresentation_S F M ρ hr, Matrix.mulVec_mulVec, hmat]
  change (Matrix.kronecker (chargeConjugation F)
    (chargeConjugation F).transpose).mulVec z (k, l) = _
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, chargeConjugation, mul_ite, ite_mul,
    one_mul, mul_one, zero_mul, mul_zero]
  have hinv : ∀ n : F.Label, (l = F.dualLabel n) ↔ (n = F.dualLabel l) := by
    intro n
    constructor
    · rintro rfl; exact (F.dualLabel_involutive n).symm
    · rintro rfl; exact (F.dualLabel_involutive l).symm
  simp only [hinv, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Classical in
/-- **Sub-residual (zero-degree mixed indicator value).**  The closed-rotation indicator
`ν_{0,-1}` of `X_i ⊠ X_j` with probe `X_a` is `[i = j*] · S_{a j} / d_j`.  A ρ-free categorical
identity (a meridian loop of the probe around the evaluation arc); not proved here. -/
def MixedZeroIndicatorValue (F : SphericalFusion C) : Prop :=
  ∀ i j a : F.Label,
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) 0 (-1) =
      if i = F.dualLabel j then categoricalS F a j / F.dimension (F.simple j) else 0

open Classical in
/-- **The base row of the `S` move from the zero-degree indicator value.** -/
theorem baseSMove_of_zeroValue (F : SphericalFusion C) (M : Modular F)
    (hv : MixedZeroIndicatorValue F) : MixedBaseSMove F M := by
  intro ρ hr a z
  have g : (ModularGroup.S⁻¹ : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S ^ 2 := by decide
  rw [g, map_mul, LinearEquiv.mul_apply]
  simp only [mixedRow]
  rw [equivariantIndicator_mixed_one_zero_S F M ρ hr a]
  simp only [mixedRepresentation_S_sq_apply F M ρ hr, F.dualLabel_involutive _]
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type]
  dsimp only [mixedFamily]
  unfold MixedZeroIndicatorValue at hv
  simp only [hv, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end VOA.Huang.NSCongruence

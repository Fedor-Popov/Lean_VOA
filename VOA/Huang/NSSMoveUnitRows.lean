import VOA.Huang.NSSMoveReduction

/-! # Unconditional S moves at the four nonzero unit rows

The rows `(±1, ±1)` follow from the established base S move, T equivariance,
and base charge symmetry. These results do not assert the whole `m = 1` case.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

section Abstract
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A base S move at `(m,0)` gives the diagonal S move at `(m,m)`. -/
theorem diagonalSMove_of_base
    (σ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (I : ℤ → ℤ → W → ℂ)
    (hT : ∀ m l z, I m (l + m) z = I m l (σ ModularGroup.T⁻¹ z))
    (m : ℤ) (hB : ∀ z, I 0 (-m) z = I m 0 (σ ModularGroup.S⁻¹ z)) (z : W) :
    I m (-m) z = I m m (σ ModularGroup.S⁻¹ z) := by
  have hc (g h : SL(2, ℤ)) (w : W) : σ g (σ h w) = σ (g * h) w := by
    rw [map_mul, LinearEquiv.mul_apply]
  have hzero (w : W) : I 0 (-m) (σ ModularGroup.T w) = I 0 (-m) w := by
    have h := hT 0 (-m) (σ ModularGroup.T w)
    simpa only [add_zero, hc, inv_mul_cancel, map_one, le_one_apply] using h
  have hminus := rowT_zpow σ I hT m 0 (-1) z
  have hplus := hT m 0 (σ ModularGroup.S⁻¹ z)
  simp only [zero_add, neg_neg, zpow_one, neg_one_mul] at hminus hplus
  rw [hminus, hplus, hc]
  symm
  have hg : (ModularGroup.T⁻¹ * ModularGroup.S⁻¹ : SL(2, ℤ)) =
      ModularGroup.S⁻¹ * (ModularGroup.T * (ModularGroup.S * ModularGroup.T)) := by decide
  calc
    _ = I 0 (-m) (σ ModularGroup.T (σ ModularGroup.S (σ ModularGroup.T z))) := by
      rw [hB, hc, hc, hc, hg]
      rw [mul_assoc, mul_assoc]
    _ = I 0 (-m) (σ ModularGroup.S (σ ModularGroup.T z)) := hzero _
    _ = _ := by rw [hB, hc, inv_mul_cancel, map_one]; rfl

end Abstract

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- Charge symmetry on the entire first-index-one row follows by T shifts. -/
theorem mixedCharge_one (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label) (l : ℤ)
    (z : F.Label × F.Label → ℂ) :
    mixedRow F a (-1) (-l) z =
      mixedRow F a 1 l (mixedRepresentation ρ (ModularGroup.S ^ 2) z) := by
  have hneg := rowT_zpow (mixedRepresentation ρ) (fun m l z => mixedRow F a m l z)
    (mixedTMove_holds F M ρ hr a) (-1) 0 l z
  have hpos := rowT_zpow (mixedRepresentation ρ) (fun m l z => mixedRow F a m l z)
    (mixedTMove_holds F M ρ hr a) 1 0 l (mixedRepresentation ρ (ModularGroup.S ^ 2) z)
  simp only [zero_add, mul_neg_one, mul_one] at hneg hpos
  rw [hneg, hpos, chargeSymmetry_one_zero F M ρ hr a]
  simp only [← LinearEquiv.mul_apply, ← map_mul]
  have h : Commute (ModularGroup.S ^ 2) ModularGroup.T := by
    change ModularGroup.S ^ 2 * ModularGroup.T = ModularGroup.T * ModularGroup.S ^ 2
    decide
  rw [(h.zpow_right (-l)).eq]

open Classical in
/-- The S step at the first genuinely nonzero row. -/
theorem mixedSMove_one_one (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label)
    (z : F.Label × F.Label → ℂ) :
    mixedRow F a 1 (-1) z = mixedRow F a 1 1 (mixedRepresentation ρ ModularGroup.S⁻¹ z) :=
  diagonalSMove_of_base (mixedRepresentation ρ) (fun m l z => mixedRow F a m l z)
    (mixedTMove_holds F M ρ hr a) 1 (mixedBaseSMove_holds F M ρ hr a) z

open Classical in
/-- The complete S step restricted to both coordinates being integer units. -/
def MixedUnitSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ), IsUnit m → IsUnit l →
      ∀ z : F.Label × F.Label → ℂ,
        mixedRow F a l (-m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- Unconditional nonzero S moves at `(1,1)`, `(1,-1)`, `(-1,1)`, and `(-1,-1)`. -/
theorem mixedUnitSMove_holds (F : SphericalFusion C) (M : Modular F) :
    MixedUnitSMove F M := by
  intro ρ hr a m l hm hl z
  have hc (g h : SL(2, ℤ)) (w : F.Label × F.Label → ℂ) :
      mixedRepresentation ρ g (mixedRepresentation ρ h w) = mixedRepresentation ρ (g * h) w := by
    rw [map_mul, LinearEquiv.mul_apply]
  have hss : (ModularGroup.S⁻¹ * ModularGroup.S⁻¹ : SL(2, ℤ)) = ModularGroup.S ^ 2 := by decide
  have hcomm : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 : SL(2, ℤ)) =
      ModularGroup.S ^ 2 * ModularGroup.S⁻¹ := by decide
  have h11 := mixedSMove_one_one F M ρ hr a
  have hneg (k : ℤ) (w : F.Label × F.Label → ℂ) := mixedCharge_one F M ρ hr a k w
  rcases Int.isUnit_iff.mp hm with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hl with rfl | rfl
  · exact h11 z
  · have he := h11 (mixedRepresentation ρ ModularGroup.S⁻¹ z)
    rw [hc, hss] at he
    exact (hneg 1 z).trans he.symm
  · simp only [neg_neg]
    have he := hneg (-1) (mixedRepresentation ρ ModularGroup.S⁻¹ z)
    simp only [neg_neg] at he
    rw [he, h11, hc, hc]
    have hg : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 * ModularGroup.S⁻¹ : SL(2, ℤ)) = 1 :=
      by decide
    rw [hg, map_one]; rfl
  · simp only [neg_neg]
    have he := hneg (-1) z
    simp only [neg_neg] at he
    rw [he, h11, hneg 1, hc, hc, hcomm]

end VOA.Huang.NSCongruence

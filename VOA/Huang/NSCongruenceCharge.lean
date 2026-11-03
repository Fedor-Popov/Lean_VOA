/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceZeroValue

/-!
# Charge symmetry at the degenerate rows, and the nonzero-row split

Equivariance at `S²` is proved at the two rows actually needed for the degenerate orbit rows:
`(1,0)` (fusion multiplicities, `chargeSymmetry_one_zero`) and `(0,-1)` (closed rotations,
`chargeSymmetry_zero_neg_one`).  With the proved base row (`mixedBaseSMove_holds`) this reduces
the `S` move along the orbit to the rows with both entries nonzero (`MixedNonzeroSMove`).
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

theorem mixed_one_zero_value (F : SphericalFusion C) (i j a : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) 1 0 =
      (F.fusionMultiplicity i j (F.simple a) : ℂ) := by
  rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 by norm_num, generalizedIndicatorAll_positive,
    generalizedIndicatorInt_zero]
  change (Module.finrank ℂ (F.simple i ⊗ F.simple j ⟶ F.simple a) : ℂ) = _
  rw [F.finrank_hom_symm]
  rfl

theorem mixed_neg_one_zero_value (F : SphericalFusion C) (i j a : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) (-1) 0 =
      (F.fusionMultiplicity i j (F.simple (F.dualLabel a)) : ℂ) := by
  simp only [generalizedIndicatorAll, show ¬ (0 : ℤ) < -1 by norm_num, if_false,
    show (-1 : ℤ) ≠ 0 by norm_num, neg_zero]
  rw [show ((-1 : ℤ).natAbs - 1) = 0 by norm_num, generalizedIndicatorInt_zero]
  change (Module.finrank ℂ (F.simple i ⊗ F.simple j ⟶ (F.simple a)ᘁ) : ℂ) = _
  rw [(homCongr (Iso.refl _) (F.dualLabelIso a)).finrank_eq, F.finrank_hom_symm]
  rfl

theorem signedTensorPower_one (V : C) : signedTensorPower V 1 = V := by
  simp [signedTensorPower]
  rfl

theorem simple_dual_dual (F : SphericalFusion C) (a : F.Label) :
    F.simple (F.dualLabel (F.dualLabel a)) = F.simple a :=
  congrArg F.simple (F.dualLabel_involutive a)

open Classical in
theorem mixed_zero_one_value (F : SphericalFusion C) (i j a : F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j)) (F.simple a) 0 1 =
      if i = F.dualLabel j then
        categoricalS F (F.dualLabel a) j / F.dimension (F.simple j) else 0 := by
  simp only [generalizedIndicatorAll, lt_irrefl, if_false, if_true]
  rw [signedTensorPower_one]
  have e : (F.simple (F.dualLabel a))ᘁ ≅ F.simple a :=
    F.dualLabelIso (F.dualLabel a) ≪≫ eqToIso (simple_dual_dual F a)
  have hW : monodromyLoop F.toPivotal (F.simple a) (F.simple j) =
      (categoricalS F (F.dualLabel a) j / F.dimension (F.simple j)) • 𝟙 (F.simple j) := by
    rw [← monodromyLoop_iso F e, monodromyLoop_simple]
  exact trace_closedRotation_mixed F i j _ _ hW

/-- Reindex a pair sum by duality on both labels. -/
theorem sum_pair_dual (F : SphericalFusion C) (g : F.Label × F.Label → ℂ) :
    (∑ p : F.Label × F.Label, g (F.dualLabel p.1, F.dualLabel p.2)) = ∑ p, g p := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← (F.dualLabelEquiv).sum_comp (fun x => ∑ y, g (x, y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (F.dualLabelEquiv).sum_comp (fun y => g (F.dualLabel x, y))

open Classical in
/-- **Charge symmetry at the row `(1,0)`.** -/
theorem chargeSymmetry_one_zero (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label) (z : F.Label × F.Label → ℂ) :
    mixedRow F a (-1) 0 z = mixedRow F a 1 0 (mixedRepresentation ρ (ModularGroup.S ^ 2) z) := by
  simp only [mixedRow, equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk]
  have hs : ∀ p : F.Label × F.Label, mixedRepresentation ρ (ModularGroup.S ^ 2) z p =
      z (F.dualLabel p.1, F.dualLabel p.2) := fun p =>
    mixedRepresentation_S_sq_apply F M ρ hr z p.1 p.2
  simp only [hs]
  rw [← sum_pair_dual F (fun p => z p * generalizedIndicatorAll F (mixedFamily F p)
    (F.simple a) (-1) 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only [mixedFamily]
  rw [mixed_neg_one_zero_value, mixed_one_zero_value]
  congr 2
  exact_mod_cast F.fusion_dual_all p.1 p.2 a

open Classical in
/-- **Charge symmetry at the row `(0,-1)`.** -/
theorem chargeSymmetry_zero_neg_one (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label) (z : F.Label × F.Label → ℂ) :
    mixedRow F a 0 1 z = mixedRow F a 0 (-1) (mixedRepresentation ρ (ModularGroup.S ^ 2) z) := by
  simp only [mixedRow, equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk]
  have hs : ∀ p : F.Label × F.Label, mixedRepresentation ρ (ModularGroup.S ^ 2) z p =
      z (F.dualLabel p.1, F.dualLabel p.2) := fun p =>
    mixedRepresentation_S_sq_apply F M ρ hr z p.1 p.2
  simp only [hs]
  rw [← sum_pair_dual F (fun p => z p * generalizedIndicatorAll F (mixedFamily F p)
    (F.simple a) 0 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only [mixedFamily]
  have hv := mixedZeroIndicatorValue_holds F p.1 p.2 a
  rw [mixed_zero_one_value, hv, F.dualLabel_involutive p.2]
  congr 1
  have hiff : (F.dualLabel p.1 = p.2) ↔ (p.1 = F.dualLabel p.2) := by
    constructor
    · rintro h; rw [← h, F.dualLabel_involutive]
    · rintro h; rw [h, F.dualLabel_involutive]
  by_cases h : p.1 = F.dualLabel p.2
  · rw [if_pos (hiff.mpr h), if_pos h, F.dimension_dualLabel,
      categoricalS_dual_both F M.toRibbon]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

open Classical in
/-- **Residual (S move at rows with both entries nonzero).** -/
def MixedNonzeroSMove (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ →
    ∀ (a : F.Label) (m l : ℤ), m ≠ 0 → l ≠ 0 → IsCoprime m l →
      ∀ z : F.Label × F.Label → ℂ,
        mixedRow F a l (-m) z = mixedRow F a m l (mixedRepresentation ρ ModularGroup.S⁻¹ z)

open Classical in
/-- **The `S` move along the orbit from the nonzero rows alone.** -/
theorem SMoveOrbit_of_nonzero (F : SphericalFusion C) (M : Modular F)
    (hN : MixedNonzeroSMove F M) : MixedSMoveOrbit F M := by
  intro ρ hr a γ z
  set σ := mixedRepresentation ρ with hσ
  have hB := mixedBaseSMove_holds F M ρ hr a
  have h10 := chargeSymmetry_one_zero F M ρ hr a
  have h01 := chargeSymmetry_zero_neg_one F M ρ hr a
  have mulσ : ∀ g h w, σ g (σ h w) = σ (g * h) w := by
    intro g h w; rw [map_mul, LinearEquiv.mul_apply]
  have g1 : (ModularGroup.S⁻¹ * ModularGroup.S⁻¹ : SL(2, ℤ)) = ModularGroup.S ^ 2 := by decide
  have g2 : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 * ModularGroup.S⁻¹ : SL(2, ℤ)) = 1 := by
    decide
  have g3 : (ModularGroup.S⁻¹ * ModularGroup.S ^ 2 : SL(2, ℤ)) =
      ModularGroup.S ^ 2 * ModularGroup.S⁻¹ := by decide
  have hall : ∀ m l, IsCoprime m l →
      ∀ w, mixedRow F a l (-m) w = mixedRow F a m l (σ ModularGroup.S⁻¹ w) := by
    intro m l hml w
    by_cases hm : m = 0
    · subst hm
      rcases Int.isUnit_iff.mp (isCoprime_zero_left.mp hml) with rfl | rfl
      · -- row (0,1)
        rw [neg_zero, h01, hB, mulσ, mulσ, g2, map_one]; rfl
      · -- row (0,-1)
        rw [neg_zero, hB, mulσ, g1, h10]
    · by_cases hl : l = 0
      · subst hl
        rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hml) with rfl | rfl
        · exact hB w
        · -- row (-1,0)
          rw [neg_neg, h01, hB, h10, mulσ, mulσ, g3]
      · exact hN ρ hr a m l hm hl hml w
  have hcop : IsCoprime (rowAction 1 0 γ).1 (rowAction 1 0 γ).2 := by
    rw [rowAction_one_zero]
    refine ⟨γ 1 1, -γ 1 0, ?_⟩
    have h := γ.property
    rw [Matrix.det_fin_two] at h
    simp only
    linarith
  exact hall _ _ hcop z

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence

universe u v w

/-- **The two remaining residuals**: the `S` move at rows with both entries nonzero, and
cyclotomic mixed S entries. -/
def NSMixedNonzeroResidualsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    MixedNonzeroSMove F M ∧ MixedSCyclotomic F M

/-- **The kernel half of NS 6.8 from the nonzero-row `S` move and cyclotomic mixed S.** -/
theorem nsProjectiveKernelAll_of_nonzeroResiduals (h : NSMixedNonzeroResidualsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  apply nsProjectiveKernelAll_of_SResiduals
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hN, hc⟩ := h C F M
  exact ⟨SMoveOrbit_of_nonzero F M hN, hc⟩

/-- **Both classification inputs from the two remaining residuals.** -/
theorem dln_inputs_of_nonzeroResiduals (h : NSMixedNonzeroResidualsAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_nonzeroResiduals h) hB hlift hT

end VOA.Huang.DLNBridge

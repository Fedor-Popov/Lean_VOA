/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceSBase

/-!
# The zero-degree mixed indicator

The closed rotation of a mixed central object `A ⊠ B` with strand `W` is precomposition with a
right loop of inverse monodromy around `B` (`closedRotation_mixed`); that right loop is the
ordinary monodromy loop of `W` around `B` (`rightLoop_eq_monodromyLoop`).  For simple objects this
gives `MixedZeroIndicatorValue` (`mixedZeroIndicatorValue_holds`), hence the base row of the `S`
move (`mixedBaseSMove_holds`).
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

/-- A loop of `W` to the right of `B`, whose left leg makes an inverse monodromy with `B`. -/
def rightLoop (P : Pivotal C) (B W : C) : B ⟶ B :=
  (ρ_ B).inv ≫ B ◁ P.cup W ≫ (α_ B Wᘁ W).inv ≫
    ((β_ Wᘁ B).inv ≫ (β_ B Wᘁ).inv) ▷ W ≫ (α_ B Wᘁ W).hom ≫ B ◁ ε_ W Wᘁ ≫ (ρ_ B).hom

/-- The mixed half-braiding is an inverse monodromy on `B` followed by the ordinary braiding
(stated on the explicit composite of `mixedCenter_halfBraiding`). -/
theorem mixed_halfBraiding_factor (A B U : C) :
    (α_ A B U).hom ≫ A ◁ (β_ U B).inv ≫ (α_ A U B).inv ≫ (β_ A U).hom ▷ B ≫ (α_ U A B).hom =
      (α_ A B U).hom ≫ A ◁ ((β_ U B).inv ≫ (β_ B U).inv) ≫ (α_ A B U).inv ≫
        (β_ (A ⊗ B) U).hom := by
  rw [braiding_tensor_left_hom]
  simp only [whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc A (β_ B U).inv, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

theorem whiskerRight_leftUnitor_comp {Z X : C} (f : Z ⟶ 𝟙_ C) (g : X ⟶ 𝟙_ C) :
    f ▷ X ≫ (λ_ X).hom ≫ g = Z ◁ g ≫ (ρ_ Z).hom ≫ f := by
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, unitors_equal,
    rightUnitor_naturality]

/-- **Closed rotation of a mixed object** is precomposition with a right loop on `B`. -/
theorem closedRotation_mixed (P : Pivotal C) (A B W : C) (f : A ⊗ B ⟶ 𝟙_ C) :
    closedRotation P (mixedCenter A B) W f = (A ◁ rightLoop P B W) ≫ f := by
  have E1 : (β_ (A ⊗ B) Wᘁ).hom ▷ W ≫ (α_ Wᘁ (A ⊗ B) W).hom ≫ Wᘁ ◁ (f ▷ W) ≫
      Wᘁ ◁ (λ_ W).hom ≫ ε_ W Wᘁ =
      (α_ (A ⊗ B) Wᘁ W).hom ≫ f ▷ (Wᘁ ⊗ W) ≫ (λ_ _).hom ≫ ε_ W Wᘁ := by
    rw [← associator_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      ← braiding_naturality_left, braiding_tensorUnit_left]
    monoidal
  change (ρ_ (A ⊗ B)).inv ≫ (A ⊗ B) ◁ η_ Wᘁ (Wᘁ)ᘁ ≫
    (A ⊗ B) ◁ (Wᘁ ◁ (P.j W).inv) ≫ (α_ _ _ _).inv ≫
    ((mixedCenter A B).2.β Wᘁ).hom ▷ W ≫ (α_ _ _ _).hom ≫
    Wᘁ ◁ (f ▷ W) ≫ Wᘁ ◁ (λ_ W).hom ≫ ε_ W Wᘁ = _
  rw [mixedCenter_halfBraiding, mixed_halfBraiding_factor]
  change (ρ_ (A ⊗ B)).inv ≫ (A ⊗ B) ◁ η_ Wᘁ (Wᘁ)ᘁ ≫
    (A ⊗ B) ◁ (Wᘁ ◁ (P.j W).inv) ≫ (α_ (A ⊗ B) Wᘁ W).inv ≫
    ((α_ A B Wᘁ).hom ≫ A ◁ ((β_ Wᘁ B).inv ≫ (β_ B Wᘁ).inv) ≫ (α_ A B Wᘁ).inv ≫
      (β_ (A ⊗ B) Wᘁ).hom) ▷ W ≫ (α_ Wᘁ (A ⊗ B) W).hom ≫
    Wᘁ ◁ (f ▷ W) ≫ Wᘁ ◁ (λ_ W).hom ≫ ε_ W Wᘁ = _
  simp only [comp_whiskerRight, Category.assoc]
  rw [E1, whiskerRight_leftUnitor_comp]
  dsimp [rightLoop, Pivotal.cup]
  monoidal

/-- **Right loop equals left monodromy loop.** -/
theorem rightLoop_eq_monodromyLoop (P : Pivotal C) (B W : C) :
    rightLoop P B W = monodromyLoop P W B := by
  have hcup : B ◁ P.cup W =
      (β_ B (𝟙_ C)).hom ≫ P.cup W ▷ B ≫ (β_ B (Wᘁ ⊗ W)).inv := by
    rw [← braiding_naturality_right_assoc]
    simp
  have hcap : B ◁ ε_ W Wᘁ = (β_ B (Wᘁ ⊗ W)).hom ≫ ε_ W Wᘁ ▷ B ≫ (β_ B (𝟙_ C)).inv := by
    rw [← braiding_naturality_right_assoc]
    simp
  have hc := cup_monodromy P W B
  -- `(*)`: transport the cup identity
  have hstar : P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ (β_ W B).hom ≫ (α_ Wᘁ B W).inv ≫
      ((β_ Wᘁ B).hom ≫ (β_ B Wᘁ).hom) ▷ W =
      P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ (β_ B W).inv ≫ (α_ Wᘁ B W).inv := by
    conv_rhs => rw [← hc]
    simp
  have hmid : P.cup W ▷ B ≫ (β_ B (Wᘁ ⊗ W)).inv ≫ (α_ B Wᘁ W).inv ≫
      ((β_ Wᘁ B).inv ≫ (β_ B Wᘁ).inv) ▷ W ≫ (α_ B Wᘁ W).hom ≫ (β_ B (Wᘁ ⊗ W)).hom =
      P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ ((β_ W B).hom ≫ (β_ B W).hom) ≫
        (α_ Wᘁ W B).inv := by
    rw [braiding_tensor_right_inv, braiding_tensor_right_hom]
    have e : P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ (β_ B W).inv ≫ (α_ Wᘁ B W).inv ≫
        (β_ B Wᘁ).inv ▷ W ≫ (β_ Wᘁ B).inv ▷ W =
        P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ (β_ W B).hom ≫ (α_ Wᘁ B W).inv := by
      rw [← reassoc_of% hstar]
      simp
    calc _ = (P.cup W ▷ B ≫ (α_ Wᘁ W B).hom ≫ Wᘁ ◁ (β_ B W).inv ≫ (α_ Wᘁ B W).inv ≫
          (β_ B Wᘁ).inv ▷ W ≫ (β_ Wᘁ B).inv ▷ W) ≫ (α_ Wᘁ B W).hom ≫
          Wᘁ ◁ (β_ B W).hom ≫ (α_ Wᘁ W B).inv := by
          simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc,
            inv_hom_whiskerRight_assoc]
      _ = _ := by
          rw [e]
          simp
  calc rightLoop P B W
      = (ρ_ B).inv ≫ (β_ B (𝟙_ C)).hom ≫
          (P.cup W ▷ B ≫ (β_ B (Wᘁ ⊗ W)).inv ≫ (α_ B Wᘁ W).inv ≫
            ((β_ Wᘁ B).inv ≫ (β_ B Wᘁ).inv) ▷ W ≫ (α_ B Wᘁ W).hom ≫
            (β_ B (Wᘁ ⊗ W)).hom) ≫ ε_ W Wᘁ ▷ B ≫ (β_ B (𝟙_ C)).inv ≫ (ρ_ B).hom := by
        rw [rightLoop, hcup, hcap]
        simp only [Category.assoc]
    _ = _ := by
        rw [hmid, braiding_tensorUnit_right]
        simp only [monodromyLoop, Pivotal.partialTraceLeft, monodromy]
        simp

theorem signedTensorPower_neg_one (V : C) : signedTensorPower V (-1) = Vᘁ := by
  simp [signedTensorPower]
  rfl

open Classical in
theorem finrank_mixed_unit (F : SphericalFusion C) (i j : F.Label) :
    Module.finrank ℂ (F.simple i ⊗ F.simple j ⟶ 𝟙_ C) =
      if j = F.dualLabel i then 1 else 0 := by
  rw [(homCongr (Iso.refl _) F.unitIso.symm).finrank_eq, F.finrank_hom_symm]
  exact fusion_unit_target F i j

open Classical in
/-- Trace of a mixed closed rotation, from the scalar of the monodromy loop of the strand. -/
theorem trace_closedRotation_mixed (F : SphericalFusion C) (i j : F.Label) (W : C) (c : ℂ)
    (hW : monodromyLoop F.toPivotal W (F.simple j) = c • 𝟙 (F.simple j)) :
    LinearMap.trace ℂ (F.simple i ⊗ F.simple j ⟶ 𝟙_ C)
      (closedRotation F.toPivotal (mixedCenter (F.simple i) (F.simple j)) W) =
      if i = F.dualLabel j then c else 0 := by
  have hrot : closedRotation F.toPivotal (mixedCenter (F.simple i) (F.simple j)) W =
      c • (1 : Module.End ℂ _) := by
    ext f
    rw [closedRotation_mixed, rightLoop_eq_monodromyLoop, hW]
    simp
    rfl
  letI := F.homFinite (F.simple i ⊗ F.simple j) (𝟙_ C)
  rw [hrot]
  calc _ = c • LinearMap.trace ℂ (F.simple i ⊗ F.simple j ⟶ 𝟙_ C) 1 := LinearMap.map_smul _ c 1
    _ = c * (Module.finrank ℂ (F.simple i ⊗ F.simple j ⟶ 𝟙_ C) : ℂ) := by
      rw [LinearMap.trace_one, smul_eq_mul]
    _ = _ := by
      rw [finrank_mixed_unit]
      have hiff : (j = F.dualLabel i) ↔ (i = F.dualLabel j) := by
        constructor
        · rintro rfl; exact (F.dualLabel_involutive i).symm
        · rintro rfl; exact (F.dualLabel_involutive j).symm
      by_cases h : i = F.dualLabel j
      · rw [if_pos (hiff.mpr h), if_pos h]; simp
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; simp

open Classical in
/-- **The zero-degree mixed indicator value** (`ν_{0,-1}` on `X_i ⊠ X_j` with probe `X_a`). -/
theorem mixedZeroIndicatorValue_holds (F : SphericalFusion C) : MixedZeroIndicatorValue F := by
  intro i j a
  simp only [generalizedIndicatorAll, lt_irrefl, if_false, if_true]
  rw [signedTensorPower_neg_one]
  exact trace_closedRotation_mixed F i j _ _ (monodromyLoop_simple F a j)

/-- **The base row of the `S` move holds for every modular category.** -/
theorem mixedBaseSMove_holds (F : SphericalFusion C) (M : Modular F) : MixedBaseSMove F M :=
  baseSMove_of_zeroValue F M (mixedZeroIndicatorValue_holds F)

end VOA.Huang.NSCongruence

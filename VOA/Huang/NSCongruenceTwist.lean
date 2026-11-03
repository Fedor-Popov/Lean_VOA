/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceOrbit
import VOA.Huang.NgSchauenburgPartialTrace

/-!
# The mixed twist identity

For a mixed central object `X = A ⊠ B` (positive braiding on `A`, inverse opposite braiding on
`B`) the composite `u^c_X ≫ j⁻¹` of the central Drinfeld morphism with the inverse pivotal
structure is a partial trace of the self half-braiding (`centralDrinfeld_comp_j_inv`), and that
partial trace factorizes as the tensor product of a negative curl on `A` and a positive curl on
`B` (`partialTrace_mixed_halfBraiding`).
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

section Pivotal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- **Lemma K.**  The central Drinfeld morphism followed by the inverse pivotal structure is the
left partial trace of the inverse self half-braiding. -/
theorem centralDrinfeld_comp_j_inv (P : Pivotal C) (Y : Center C) :
    centralDrinfeldMorphism Y ≫ (P.j Y.1).inv =
      P.partialTraceLeft Y.1 (Y.2.β Y.1).inv := by
  have hn := halfBraiding_inv_naturality Y (P.j Y.1).inv
  dsimp [Pivotal.partialTraceLeft, Pivotal.cup, centralDrinfeldMorphism]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ← hn,
    whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, leftUnitor_naturality]

end Pivotal

section Braided
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The inverse mixed half-braiding, with all associators retained. -/
theorem mixedCenter_halfBraiding_inv (X Y U : C) :
    ((mixedCenter X Y).2.β U).inv =
      (α_ U X Y).inv ≫ (β_ X U).inv ▷ Y ≫ (α_ X U Y).hom ≫
        X ◁ (β_ U Y).hom ≫ (α_ X Y U).inv := by
  dsimp [mixedCenter, oppositeBraidedCenter, Center.ofBraidedObj]
  simp

/-- **Factorization of the mixed curl.**  The partial trace of the inverse mixed self
half-braiding is the tensor product of the negative curl on `A` and the positive curl on `B`.
Pivotal and braided structure only; no twist is used. -/
theorem partialTrace_mixed_halfBraiding (F : SphericalFusion C) (A B : C) :
    F.toPivotal.partialTraceLeft (A ⊗ B) ((mixedCenter A B).2.β (A ⊗ B)).inv =
      F.toPivotal.partialTraceLeft A (β_ A A).inv ⊗ₘ
        F.toPivotal.partialTraceLeft B (β_ B B).hom := by
  set ta := F.toPivotal.partialTraceLeft A (β_ A A).inv with hta
  set tb := F.toPivotal.partialTraceLeft B (β_ B B).hom with htb
  rw [F.partialTraceLeft_tensor A B]
  change F.toPivotal.partialTraceLeft B (F.toPivotal.partialTraceLeft A
    ((α_ A B (A ⊗ B)).inv ≫ ((mixedCenter A B).2.β (A ⊗ B)).inv ≫
      (α_ A B (A ⊗ B)).hom)) = _
  -- the inner (A-loop) decomposition
  have hG : (α_ A B (A ⊗ B)).inv ≫ ((mixedCenter A B).2.β (A ⊗ B)).inv ≫
      (α_ A B (A ⊗ B)).hom =
      A ◁ ((α_ B A B).inv ≫ (β_ A B).inv ▷ B ≫ (α_ A B B).hom) ≫
        ((α_ A A (B ⊗ B)).inv ≫ (β_ A A).inv ▷ (B ⊗ B) ≫ (α_ A A (B ⊗ B)).hom) ≫
        A ◁ (A ◁ (β_ B B).hom ≫ (α_ A B B).inv ≫ (β_ A B).hom ▷ B ≫ (α_ B A B).hom) := by
    rw [mixedCenter_halfBraiding_inv, braiding_tensor_right_inv, braiding_tensor_left_hom]
    monoidal
  rw [hG, F.toPivotal.partialTraceLeft_precomp, F.toPivotal.partialTraceLeft_postcomp,
    F.toPivotal.partialTraceLeft_whisker, ← hta]
  -- the outer (B-loop) decomposition
  have hH : ((α_ B A B).inv ≫ (β_ A B).inv ▷ B ≫ (α_ A B B).hom) ≫ ta ▷ (B ⊗ B) ≫
      (A ◁ (β_ B B).hom ≫ (α_ A B B).inv ≫ (β_ A B).hom ▷ B ≫ (α_ B A B).hom) =
      B ◁ (ta ▷ B ≫ (β_ A B).hom) ≫
        ((α_ B B A).inv ≫ (β_ B B).hom ▷ A ≫ (α_ B B A).hom) ≫ B ◁ (β_ A B).inv := by
    have h1 : (β_ A B).inv ▷ B ≫ (α_ A B B).hom ≫ ta ▷ (B ⊗ B) =
        (B ◁ ta) ▷ B ≫ (β_ A B).inv ▷ B ≫ (α_ A B B).hom := by
      rw [← associator_naturality_left, ← comp_whiskerRight_assoc,
        ← braiding_inv_naturality_right, comp_whiskerRight_assoc]
    have h2 : (β_ A B).inv ▷ B ≫ (α_ A B B).hom ≫ A ◁ (β_ B B).hom ≫ (α_ A B B).inv ≫
        (β_ A B).hom ▷ B ≫ (α_ B A B).hom =
        (β_ A B).inv ▷ B ≫ (β_ (A ⊗ B) B).hom := by
      rw [braiding_tensor_left_hom]
    have h3 : (β_ A B).inv ▷ B ≫ (β_ (A ⊗ B) B).hom =
        (β_ (B ⊗ A) B).hom ≫ B ◁ (β_ A B).inv := by
      rw [braiding_naturality_left]
    calc
      _ = (α_ B A B).inv ≫ (B ◁ ta) ▷ B ≫ ((β_ A B).inv ▷ B ≫ (α_ A B B).hom ≫
          A ◁ (β_ B B).hom ≫ (α_ A B B).inv ≫ (β_ A B).hom ▷ B ≫ (α_ B A B).hom) := by
        simp only [Category.assoc]
        rw [reassoc_of% h1]
      _ = (α_ B A B).inv ≫ (B ◁ ta) ▷ B ≫ (β_ (B ⊗ A) B).hom ≫ B ◁ (β_ A B).inv := by
        rw [h2, h3]
      _ = _ := by
        rw [braiding_tensor_left_hom]
        simp only [whiskerLeft_comp, Category.assoc]
        rw [← associator_inv_naturality_middle_assoc]
        monoidal
  rw [hH, F.toPivotal.partialTraceLeft_precomp, F.toPivotal.partialTraceLeft_postcomp,
    F.toPivotal.partialTraceLeft_whisker, ← htb]
  rw [MonoidalCategory.tensorHom_def, Category.assoc, ← braiding_naturality_right_assoc]
  simp

/-! ## Curls and the ribbon twist -/

/-- **Lemma R.**  The negative left curl is the inverse ribbon twist (from `j = θ ≫ u`). -/
theorem negativeCurl (F : SphericalFusion C) (R : Ribbon F.toPivotal) (V : C) :
    F.toPivotal.partialTraceLeft V (β_ V V).inv = (R.twist V).inv := by
  have hK := centralDrinfeld_comp_j_inv F.toPivotal (Center.ofBraidedObj V)
  have hu : centralDrinfeldMorphism (Center.ofBraidedObj V) = drinfeldMorphism V := rfl
  change _ = F.toPivotal.partialTraceLeft V (β_ V V).inv at hK
  rw [← hK, hu]
  change drinfeldMorphism V ≫ (F.j V).inv = _
  apply (cancel_epi (R.twist V).hom).mp
  rw [← Category.assoc, ← R.pivotal V]
  simp

/-- The inverse monodromy of a dual pair below the evaluation is a double twist on one leg
(ribbon unit, balance and duality axioms). -/
theorem inverseMonodromy_evaluation (P : Pivotal C) (R : Ribbon P) (V : C) :
    (β_ V Vᘁ).inv ≫ (β_ Vᘁ V).inv ≫ ε_ V Vᘁ =
      Vᘁ ◁ ((R.twist V).hom ≫ (R.twist V).hom) ≫ ε_ V Vᘁ := by
  have hn := R.naturality (ε_ V Vᘁ)
  rw [R.unit, Category.comp_id, R.balance] at hn
  have h1 : (β_ V Vᘁ).inv ≫ (β_ Vᘁ V).inv ≫ ε_ V Vᘁ =
      ((R.twist Vᘁ).hom ⊗ₘ (R.twist V).hom) ≫ ε_ V Vᘁ := by
    conv_lhs => rw [hn]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    rw [← braiding_inv_naturality_assoc, ← braiding_inv_naturality_assoc]
    simp
  rw [h1, R.dual, MonoidalCategory.tensorHom_def, Category.assoc,
    ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc]

/-- A strand passing around both legs of the pivotal cup does nothing. -/
theorem cup_monodromy (P : Pivotal C) (V T : C) :
    P.cup V ▷ T ≫ (α_ Vᘁ V T).hom ≫ Vᘁ ◁ (β_ V T).hom ≫ (α_ Vᘁ T V).inv ≫
      ((β_ Vᘁ T).hom ≫ (β_ T Vᘁ).hom) ▷ V ≫ (α_ Vᘁ T V).hom ≫ Vᘁ ◁ (β_ T V).hom ≫
      (α_ Vᘁ V T).inv = P.cup V ▷ T := by
  have h1 := braiding_naturality_left (P.cup V) T
  have h2 := braiding_naturality_right T (P.cup V)
  have h3 : P.cup V ▷ T ≫ (β_ (Vᘁ ⊗ V) T).hom ≫ (β_ T (Vᘁ ⊗ V)).hom = P.cup V ▷ T := by
    rw [reassoc_of% h1, h2]
    simp
  rw [braiding_tensor_left_hom, braiding_tensor_right_hom] at h3
  rw [comp_whiskerRight]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h3

/-- **Lemma L2.**  The positive left curl is the ribbon twist.  Uses the ribbon unit, balance
and duality axioms through `inverseMonodromy_evaluation`, and Lemma R. -/
theorem positiveCurl (F : SphericalFusion C) (R : Ribbon F.toPivotal) (V : C) :
    F.toPivotal.partialTraceLeft V (β_ V V).hom = (R.twist V).hom := by
  have hc := cup_monodromy F.toPivotal V V
  have key : F.toPivotal.cup V ▷ V ≫ (α_ Vᘁ V V).hom ≫ Vᘁ ◁ (β_ V V).hom =
      F.toPivotal.cup V ▷ V ≫ (α_ Vᘁ V V).hom ≫ Vᘁ ◁ (β_ V V).inv ≫ (α_ Vᘁ V V).inv ≫
        ((β_ V Vᘁ).inv ≫ (β_ Vᘁ V).inv) ▷ V ≫ (α_ Vᘁ V V).hom := by
    conv_rhs => rw [← hc]
    simp
  have hcap := inverseMonodromy_evaluation F.toPivotal R V
  set τ := (R.twist V).hom ≫ (R.twist V).hom with hτ
  calc F.toPivotal.partialTraceLeft V (β_ V V).hom
      = (λ_ V).inv ≫ (F.toPivotal.cup V ▷ V ≫ (α_ Vᘁ V V).hom ≫ Vᘁ ◁ (β_ V V).hom) ≫
          (α_ Vᘁ V V).inv ≫ ε_ V Vᘁ ▷ V ≫ (λ_ V).hom := by
        simp [Pivotal.partialTraceLeft]
    _ = (λ_ V).inv ≫ F.toPivotal.cup V ▷ V ≫ (α_ Vᘁ V V).hom ≫ Vᘁ ◁ (β_ V V).inv ≫
          (α_ Vᘁ V V).inv ≫ ((β_ V Vᘁ).inv ≫ (β_ Vᘁ V).inv ≫ ε_ V Vᘁ) ▷ V ≫
          (λ_ V).hom := by
        rw [key]
        simp
    _ = (λ_ V).inv ≫ F.toPivotal.cup V ▷ V ≫ (α_ Vᘁ V V).hom ≫
          Vᘁ ◁ ((β_ V V).inv ≫ τ ▷ V) ≫
          (α_ Vᘁ V V).inv ≫ ε_ V Vᘁ ▷ V ≫ (λ_ V).hom := by
        rw [hcap, comp_whiskerRight]
        simp only [Category.assoc]
        rw [← associator_inv_naturality_middle_assoc, whiskerLeft_comp_assoc]
    _ = F.toPivotal.partialTraceLeft V (V ◁ τ ≫ (β_ V V).inv) := by
        rw [← braiding_inv_naturality_right]
        simp [Pivotal.partialTraceLeft]
    _ = (R.twist V).hom := by
        rw [F.toPivotal.partialTraceLeft_precomp, negativeCurl F R V, hτ]
        simp

/-- The central twist of a mixed object, as a morphism: `u^c ≫ j⁻¹ = θ_A⁻¹ ⊗ θ_B`. -/
theorem centralDrinfeld_mixed_comp_j_inv (F : SphericalFusion C) (R : Ribbon F.toPivotal)
    (A B : C) :
    centralDrinfeldMorphism (mixedCenter A B) ≫ (F.j (A ⊗ B)).inv =
      (R.twist A).inv ⊗ₘ (R.twist B).hom := by
  have hK := centralDrinfeld_comp_j_inv F.toPivotal (mixedCenter A B)
  change _ = F.toPivotal.partialTraceLeft (A ⊗ B) ((mixedCenter A B).2.β (A ⊗ B)).inv at hK
  rw [partialTrace_mixed_halfBraiding, negativeCurl F R, positiveCurl F R] at hK
  exact hK

/-- **The mixed twist identity holds for every modular category.**  On `X_i ⊠ X_j` the
pivotal structure is `θ_i / θ_j` times the central Drinfeld morphism. -/
theorem mixedTwistIdentity_holds (F : SphericalFusion C) (M : Modular F) :
    MixedTwistIdentity F M := by
  intro i j
  have hK := centralDrinfeld_mixed_comp_j_inv F M.toRibbon (F.simple i) (F.simple j)
  have hti : (M.toRibbon.twist (F.simple i)).inv =
      (M.twistScalar i)⁻¹ • 𝟙 (F.simple i) := by
    rw [← cancel_epi (M.toRibbon.twist (F.simple i)).hom, Iso.hom_inv_id,
      ← M.toRibbon.twistScalar_smul_id i]
    simp [smul_smul, inv_mul_cancel₀ (M.toRibbon.twistScalar_ne_zero i)]
  have htj := (M.toRibbon.twistScalar_smul_id j).symm
  rw [hti, htj] at hK
  simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, id_whiskerRight, whiskerLeft_id, Linear.smul_comp,
    Linear.comp_smul, Category.id_comp, smul_smul] at hK
  have h2 := (Iso.comp_inv_eq _).mp hK
  change (F.j (F.simple i ⊗ F.simple j)).hom = _
  rw [h2]
  erw [Linear.smul_comp, Category.id_comp]
  rw [smul_smul]
  have hne_i := M.toRibbon.twistScalar_ne_zero i
  have hne_j := M.toRibbon.twistScalar_ne_zero j
  have hc : M.twistScalar i / M.twistScalar j * (M.twistScalar j * (M.twistScalar i)⁻¹) = 1 := by
    field_simp
  rw [hc, one_smul]

end Braided

end VOA.Huang.NSCongruence

import VOA.Huang.NSSMove3DiagonalTrace

/-! # Rotation as a partial trace, and single-step two-block traces -/
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

/-- Moving a central source through a pivotal cup. -/
theorem halfBraiding_pivotalCup (P : Pivotal C) (A : Center C) (X : C) :
    (ρ_ A.1).inv ≫ A.1 ◁ P.cup X ≫ (α_ A.1 Xᘁ X).inv ≫
      (A.2.β Xᘁ).hom ▷ X =
    (λ_ A.1).inv ≫ P.cup X ▷ A.1 ≫ (α_ Xᘁ X A.1).hom ≫
      Xᘁ ◁ (A.2.β X).inv ≫ (α_ Xᘁ A.1 X).inv := by
  calc
    _ = ((ρ_ A.1).inv ≫ A.1 ◁ η_ Xᘁ (Xᘁ)ᘁ ≫
        (α_ A.1 Xᘁ (Xᘁ)ᘁ).inv ≫ (A.2.β Xᘁ).hom ▷ (Xᘁ)ᘁ) ≫
        (Xᘁ ⊗ A.1) ◁ (P.j X).inv := by
      dsimp [Pivotal.cup]
      simp only [whiskerLeft_comp, Category.assoc]
      rw [associator_inv_naturality_right_assoc, whisker_exchange]
    _ = _ := by
      rw [halfBraiding_coevaluation]
      dsimp [Pivotal.cup]
      simp only [Category.assoc, comp_whiskerRight]
      rw [← associator_inv_naturality_right, ← whiskerLeft_comp_assoc,
        halfBraiding_inv_naturality, whiskerLeft_comp_assoc,
        ← associator_naturality_middle_assoc]

/-- A block rotation is a partial trace of the inverse half-braiding. -/
theorem centerRotation_eq_partialTrace (P : Pivotal C) (A : Center C)
    (X Y : C) (f : A.1 ⟶ X ⊗ Y) :
    centerRotation P A X Y f =
      P.partialTraceLeft X ((A.2.β X).inv ≫ f ▷ X ≫ (α_ X Y X).hom) := by
  rw [centerRotation_eq_cup, reassoc_of% (halfBraiding_pivotalCup P A X)]
  dsimp [Pivotal.partialTraceLeft, leftDuality, tensorLeftHomEquiv]
  monoidal

/-- A resolution on the exterior strand of an inverse half-braiding. -/
theorem inverseCrossing_exterior_resolution (F : SphericalFusion C) (A : Center C)
    (U W : C) (p : W ⟶ A.1) (q : A.1 ⟶ W) (R : W ⊗ U ⟶ U ⊗ W) :
    (∑ i, ∑ β, F.scalarTrace (U ⊗ W)
      (F.compositionDual (F.simpleHomBasis U i) β ▷ W ≫
        F.simple i ◁ p ≫ (A.2.β (F.simple i)).inv ≫ q ▷ F.simple i ≫
        W ◁ F.simpleHomBasis U i β ≫ R)) =
      F.scalarTrace (U ⊗ W) (U ◁ p ≫ (A.2.β U).inv ≫ q ▷ U ≫ R) := by
  let L : (U ⟶ U) →ₗ[ℂ] ℂ :=
    { toFun := fun e => F.scalarTrace (U ⊗ W)
        (U ◁ p ≫ (A.2.β U).inv ≫ q ▷ U ≫ W ◁ e ≫ R)
      map_add' := by intros; simp [MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add,
        Preadditive.add_comp]
      map_smul' := by intros; simp }
  have he (i : F.Label) (β : Fin (Module.finrank ℂ (F.simple i ⟶ U))) :
      F.compositionDual (F.simpleHomBasis U i) β ▷ W ≫
        F.simple i ◁ p ≫ (A.2.β (F.simple i)).inv ≫ q ▷ F.simple i ≫
        W ◁ F.simpleHomBasis U i β ≫ R =
      U ◁ p ≫ (A.2.β U).inv ≫ q ▷ U ≫
        W ◁ (F.compositionDual (F.simpleHomBasis U i) β ≫
          F.simpleHomBasis U i β) ≫ R := by
    rw [← whisker_exchange_assoc, ← halfBraiding_inv_naturality_assoc,
      whisker_exchange_assoc, whiskerLeft_comp]
    simp only [Category.assoc]
  simp_rw [he]
  change (∑ i, ∑ β, L (F.compositionDual (F.simpleHomBasis U i) β ≫
    F.simpleHomBasis U i β)) = _
  simp_rw [← map_sum]
  rw [F.sum_compositionDual_comp]
  simp [L]

/-- The endomorphism obtained by closing the extra tensor block. -/
def inverseBlockOperator (P : Pivotal C) (A : Center C) (U W : C)
    (R : W ⊗ U ⟶ U ⊗ W) : Module.End ℂ (A.1 ⟶ W) where
  toFun f := P.partialTraceLeftLinear U A.1 W ((A.2.β U).inv ≫ f ▷ U ≫ R)
  map_add' := by
    intros
    simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.comp_add,
      Preadditive.add_comp, map_add]
  map_smul' := by
    intros
    simp

/-- The categorical contraction for each pair of dual-basis maps. -/
theorem inverseBlockOperator_trace_pair (F : SphericalFusion C) (A : Center C)
    (U W : C) (R : W ⊗ U ⟶ U ⊗ W) (f : A.1 ⟶ W) (g : W ⟶ A.1) :
    F.scalarTrace A.1 (inverseBlockOperator F.toPivotal A U W R f ≫ g) =
      F.scalarTrace (U ⊗ W) (U ◁ g ≫ (A.2.β U).inv ≫ f ▷ U ≫ R) := by
  change F.scalarTrace A.1 (F.toPivotal.partialTraceLeft U _ ≫ g) = _
  rw [← F.toPivotal.partialTraceLeft_postcomp, F.scalarTrace_partialTraceLeft,
    F.scalarTrace_comp_comm]

/-- All inverse two-block closures are ordinary traces of an explicit
endomorphism. This does not yet identify that endomorphism with a rotation power. -/
theorem inverseTwoBlockClosure_eq_trace (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    (∑ i, ∑ j, twoBlockClosure F V n k i j (inverseChannelCrossing F A i j)) =
      LinearMap.trace ℂ (A.1 ⟶ tensorPower V (n + 1))
        (inverseBlockOperator F.toPivotal A (tensorPower V (k + 1))
          (tensorPower V (n + 1)) (blockReassociation V n k).hom) := by
  let U := tensorPower V (k + 1)
  let W := tensorPower V (n + 1)
  let R := (blockReassociation V n k).hom
  rw [F.linearTrace_eq_sum_normalized_channels (F.simpleHomBasis A.1)
    (F.simpleHomBasis W)]
  simp only [twoBlockClosure, LinearMap.coe_mk, AddHom.coe_mk,
    inverseChannelCrossing, map_smul, map_sum, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [inverseBlockOperator_trace_pair]
  convert inverseCrossing_exterior_resolution F A U W
    (F.compositionDual (F.simpleHomBasis W j) α ≫ F.simpleHomBasis A.1 j γ)
    (F.compositionDual (F.simpleHomBasis A.1 j) γ ≫ F.simpleHomBasis W j α) R using 1
  simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp,
    comp_whiskerRight, Category.assoc, U, W, R]

/-- Reassociating a final one-factor block is the existing append map. -/
theorem blockReassociation_right_zero (V : C) (n : ℕ) :
    (blockReassociation V n 0).hom = (appendPower V n).hom := by
  have h : (joinPower V 0 n).inv = eqToHom (by simp only [Nat.zero_add]; rfl) := by
    apply (cancel_epi (joinPower V 0 n).hom).mp
    rw [Iso.hom_inv_id, joinPower_zero]
    simp
  simp [blockReassociation, h]

/-- The one-factor partial-trace operator is the genuine single rotation. -/
theorem inverseBlockOperator_single (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) :
    inverseBlockOperator F.toPivotal A V (tensorPower V (n + 1))
      (blockReassociation V n 0).hom =
      (generalizedRotation F.toPivotal A V n).toLinearMap := by
  ext f
  change F.toPivotal.partialTraceLeft V
    ((A.2.β V).inv ≫ f ▷ V ≫ (blockReassociation V n 0).hom) =
    generalizedRotation F.toPivotal A V n f
  rw [blockReassociation_right_zero]
  cases n with
  | zero =>
    dsimp only [tensorPower] at f
    simp only [appendPower, Iso.refl_hom, Category.comp_id]
    rw [generalizedRotation_one_centralDrinfeld,
      ← F.partialTraceLeft_dinatural f (A.2.β V).inv, ← halfBraiding_inv_naturality,
      F.toPivotal.partialTraceLeft_postcomp, ← centralDrinfeld_comp_j_inv]
    simp only [Category.assoc]
  | succ n =>
    rw [generalizedRotation_apply, centerRotation_eq_partialTrace,
      ← F.toPivotal.partialTraceLeft_postcomp]
    simp [appendPower, Category.assoc]

/-- The inverse trace formula for every positive degree at exponent one,
including all unequal block sizes with `k=0`. -/
theorem inverseTwoBlockTrace_single (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) :
    generalizedIndicatorInt F.toPivotal A V n 1 =
      ∑ i, ∑ j, twoBlockClosure F V n 0 i j (inverseChannelCrossing F A i j) := by
  rw [inverseTwoBlockClosure_eq_trace]
  change _ = LinearMap.trace ℂ (A.1 ⟶ tensorPower V (n + 1))
    (inverseBlockOperator F.toPivotal A V (tensorPower V (n + 1))
      (blockReassociation V n 0).hom)
  rw [inverseBlockOperator_single]
  simp [generalizedIndicatorInt]

end VOA.Huang.NSCongruence

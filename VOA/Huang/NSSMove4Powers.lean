import VOA.Huang.NSSMove4Trace

/-! # Composition of the two-block partial-trace operators -/
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

/-- Closing two exterior blocks successively composes the two operators. -/
theorem inverseBlockOperator_tensor (F : SphericalFusion C) (A : Center C)
    (U T W : C) (R : W ⊗ U ⟶ U ⊗ W) (S : W ⊗ T ⟶ T ⊗ W) :
    inverseBlockOperator F.toPivotal A (U ⊗ T) W
      ((α_ W U T).inv ≫ R ▷ T ≫ (α_ U W T).hom ≫
        U ◁ S ≫ (α_ U T W).inv) =
      (inverseBlockOperator F.toPivotal A T W S).comp
        (inverseBlockOperator F.toPivotal A U W R) := by
  ext f
  change F.toPivotal.partialTraceLeft (U ⊗ T) _ = _
  rw [F.partialTraceLeft_tensor]
  have hx : (A.2.β (U ⊗ T)).inv =
      (α_ U T A.1).hom ≫ U ◁ (A.2.β T).inv ≫ (α_ U A.1 T).inv ≫
        (A.2.β U).inv ▷ T ≫ (α_ A.1 U T).hom := by
    apply (cancel_epi (A.2.β (U ⊗ T)).hom).mp
    rw [Iso.hom_inv_id, A.2.monoidal]
    simp
  rw [hx]
  have he : (α_ U T A.1).inv ≫
      ((α_ U T A.1).hom ≫ U ◁ (A.2.β T).inv ≫ (α_ U A.1 T).inv ≫
        (A.2.β U).inv ▷ T ≫ (α_ A.1 U T).hom) ≫ f ▷ (U ⊗ T) ≫
      ((α_ W U T).inv ≫ R ▷ T ≫ (α_ U W T).hom ≫
        U ◁ S ≫ (α_ U T W).inv) ≫ (α_ U T W).hom =
      U ◁ (A.2.β T).inv ≫
        ((α_ U A.1 T).inv ≫ ((A.2.β U).inv ≫ f ▷ U ≫ R) ▷ T ≫
          (α_ U W T).hom) ≫ U ◁ S := by
    monoidal
  simp only [Category.assoc] at he ⊢
  rw [he, F.toPivotal.partialTraceLeft_precomp]
  have hp := F.toPivotal.partialTraceLeft_postcomp U
    ((α_ U A.1 T).inv ≫ ((A.2.β U).inv ≫ f ▷ U ≫ R) ▷ T ≫
      (α_ U W T).hom) S
  simp only [Category.assoc] at hp
  rw [hp, F.toPivotal.partialTraceLeft_whisker]
  rfl

/-- The two-block reassociation satisfies the tensor composition law. -/
theorem blockReassociation_succ (V : C) (n k : ℕ) :
    (blockReassociation V n (k + 1)).hom =
      (α_ (tensorPower V (n + 1)) V (tensorPower V (k + 1))).inv ≫
        (blockReassociation V n 0).hom ▷ tensorPower V (k + 1) ≫
        (α_ V (tensorPower V (n + 1)) (tensorPower V (k + 1))).hom ≫
        V ◁ (blockReassociation V n k).hom ≫
        (α_ V (tensorPower V (k + 1)) (tensorPower V (n + 1))).inv := by
  rw [blockReassociation_right_zero]
  apply (cancel_mono (joinPower V (k + 1) n).hom).mp
  simp only [blockReassociation, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinPower_succ V k n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]
  rw [← whiskerLeft_comp_assoc V (joinPower V k n).inv (joinPower V k n).hom,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  have h := joinPower_middle V n k
  rw [joinPower_succ V n k] at h
  apply (cancel_epi (α_ (tensorPower V (n + 1)) V
    (tensorPower V (k + 1))).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have h' := congrArg (fun f => f ≫ eqToHom
    (show tensorPower V (n + 1 + k + 2) = tensorPower V (k + 1 + n + 2) by
      congr 1; omega)) h.symm
  simpa only [Category.assoc, whiskerLeft_eqToHom, eqToHom_trans] using h'

/-- Every positive power of the genuine rotation is the two-block operator. -/
theorem inverseBlockOperator_power (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    inverseBlockOperator F.toPivotal A (tensorPower V (k + 1))
      (tensorPower V (n + 1)) (blockReassociation V n k).hom =
      (generalizedRotation F.toPivotal A V n).toLinearMap ^ (k + 1) := by
  induction k with
  | zero => simpa only [tensorPower, pow_one] using inverseBlockOperator_single F A V n
  | succ k ih =>
    rw [blockReassociation_succ]
    change inverseBlockOperator F.toPivotal A (V ⊗ tensorPower V (k + 1)) _ _ = _
    rw [inverseBlockOperator_tensor, ih, inverseBlockOperator_single]
    exact (pow_succ _ _).symm

/-- The full inverse clause of the two-block trace formula, with arbitrary
central source, probe, and positive block sizes. -/
theorem inverseTwoBlockTrace (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    generalizedIndicatorInt F.toPivotal A V n (k + 1) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j (inverseChannelCrossing F A i j) := by
  rw [inverseTwoBlockClosure_eq_trace, inverseBlockOperator_power]
  change LinearMap.trace ℂ (A.1 ⟶ tensorPower V (n + 1))
    (((generalizedRotation F.toPivotal A V n) ^ ((k + 1 : ℕ) : ℤ)).toLinearMap) = _
  rw [zpow_natCast]
  congr 1
  ext f
  change ((generalizedRotation F.toPivotal A V n) ^ (k + 1)) f = _
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end VOA.Huang.NSCongruence

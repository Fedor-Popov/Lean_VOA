import VOA.Huang.NSSMove5Forward

/-! # Composition and powers of the forward reverse-Hom operator -/
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

/-- Successive exterior closures compose the forward operators. -/
theorem forwardBlockOperator_tensor (F : SphericalFusion C) (A : Center C)
    (W T U : C) (R : W ⊗ U ⟶ U ⊗ W) (S : T ⊗ U ⟶ U ⊗ T) :
    forwardBlockOperator F.toPivotal A (W ⊗ T) U
      ((α_ W T U).hom ≫ W ◁ S ≫ (α_ W U T).inv ≫
        R ▷ T ≫ (α_ U W T).hom) =
      (forwardBlockOperator F.toPivotal A T U S).comp
        (forwardBlockOperator F.toPivotal A W U R) := by
  ext g
  change F.toPivotal.partialTraceLeft (W ⊗ T) _ = _
  rw [F.partialTraceLeft_tensor, A.2.monoidal]
  have he : (α_ W T U).inv ≫
      ((α_ W T U).hom ≫ W ◁ S ≫ (α_ W U T).inv ≫
        R ▷ T ≫ (α_ U W T).hom) ≫ g ▷ (W ⊗ T) ≫
      ((α_ A.1 W T).inv ≫ (A.2.β W).hom ▷ T ≫
        (α_ W A.1 T).hom ≫ W ◁ (A.2.β T).hom ≫ (α_ W T A.1).inv) ≫
      (α_ W T A.1).hom =
      W ◁ S ≫ ((α_ W U T).inv ≫ (R ≫ g ▷ W ≫ (A.2.β W).hom) ▷ T ≫
        (α_ W A.1 T).hom) ≫ W ◁ (A.2.β T).hom := by monoidal
  simp only [Category.assoc] at he ⊢
  rw [he, F.toPivotal.partialTraceLeft_precomp]
  have hp := F.toPivotal.partialTraceLeft_postcomp W
    ((α_ W U T).inv ≫ (R ≫ g ▷ W ≫ (A.2.β W).hom) ▷ T ≫
      (α_ W A.1 T).hom) (A.2.β T).hom
  simp only [Category.assoc] at hp
  rw [hp, F.toPivotal.partialTraceLeft_whisker]
  rfl

/-- Swapping the two block degrees inverts the reassociation. -/
theorem blockReassociation_swap (V : C) (n k : ℕ) :
    (blockReassociation V n k).hom = (blockReassociation V k n).inv := by
  simp [blockReassociation]

/-- The forward reassociation law in its first block degree. -/
theorem blockReassociation_left_succ (V : C) (n k : ℕ) :
    (blockReassociation V (n + 1) k).hom =
      (α_ V (tensorPower V (n + 1)) (tensorPower V (k + 1))).hom ≫
        V ◁ (blockReassociation V n k).hom ≫
        (α_ V (tensorPower V (k + 1)) (tensorPower V (n + 1))).inv ≫
        (blockReassociation V 0 k).hom ▷ tensorPower V (n + 1) ≫
        (α_ (tensorPower V (k + 1)) V (tensorPower V (n + 1))).hom := by
  simp_rw [blockReassociation_swap]
  apply (cancel_epi (blockReassociation V k (n + 1)).hom).mp
  rw [Iso.hom_inv_id, blockReassociation_succ]
  simp

/-- Every forward closure is a power of the single-exterior-factor operator. -/
theorem forwardBlockOperator_power (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    forwardBlockOperator F.toPivotal A (tensorPower V (n + 1))
      (tensorPower V (k + 1)) (blockReassociation V n k).hom =
      (forwardBlockOperator F.toPivotal A V (tensorPower V (k + 1))
        (blockReassociation V 0 k).hom) ^ (n + 1) := by
  induction n with
  | zero => simp only [Nat.zero_add, tensorPower, pow_one]
  | succ n ih =>
    rw [blockReassociation_left_succ]
    change forwardBlockOperator F.toPivotal A (V ⊗ tensorPower V (n + 1)) _ _ = _
    rw [forwardBlockOperator_tensor, ih]
    exact (pow_succ _ _).symm

end VOA.Huang.NSCongruence

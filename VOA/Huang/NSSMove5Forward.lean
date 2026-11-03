import VOA.Huang.NSSMove4Assembly

/-! # Forward closures as operators on the reverse Hom space -/
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

/-- Close the exterior block after the forward half-braiding, on reverse maps. -/
def forwardBlockOperator (P : Pivotal C) (A : Center C) (W U : C)
    (R : W ⊗ U ⟶ U ⊗ W) : Module.End ℂ (U ⟶ A.1) where
  toFun g := P.partialTraceLeftLinear W U A.1 (R ≫ g ▷ W ≫ (A.2.β W).hom)
  map_add' := by
    intros
    simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.comp_add,
      Preadditive.add_comp, map_add]
  map_smul' := by intros; simp

/-- The pairing of the forward operator is the uncontracted categorical diagram. -/
theorem forwardBlockOperator_trace_pair (F : SphericalFusion C) (A : Center C)
    (W U : C) (R : W ⊗ U ⟶ U ⊗ W) (g : U ⟶ A.1) (f : A.1 ⟶ U) :
    F.scalarTrace U (forwardBlockOperator F.toPivotal A W U R g ≫ f) =
      F.scalarTrace (U ⊗ W) (g ▷ W ≫ (A.2.β W).hom ≫ W ◁ f ≫ R) := by
  change F.scalarTrace U (F.toPivotal.partialTraceLeft W _ ≫ f) = _
  rw [← F.toPivotal.partialTraceLeft_postcomp, F.scalarTrace_partialTraceLeft]
  simpa only [Category.assoc] using F.scalarTrace_comp_comm R
    (g ▷ W ≫ (A.2.β W).hom ≫ W ◁ f)

/-- Resolve the exterior strand of a forward half-braiding. -/
theorem forwardCrossing_exterior_resolution (F : SphericalFusion C) (A : Center C)
    (W U : C) (g : U ⟶ A.1) (f : A.1 ⟶ U) (R : W ⊗ U ⟶ U ⊗ W) :
    (∑ j, ∑ α, F.scalarTrace (U ⊗ W)
      (g ▷ W ≫ A.1 ◁ F.compositionDual (F.simpleHomBasis W j) α ≫
        (A.2.β (F.simple j)).hom ≫ F.simple j ◁ f ≫
        F.simpleHomBasis W j α ▷ U ≫ R)) =
      F.scalarTrace (U ⊗ W) (g ▷ W ≫ (A.2.β W).hom ≫ W ◁ f ≫ R) := by
  let L : (W ⟶ W) →ₗ[ℂ] ℂ :=
    { toFun := fun e => F.scalarTrace (U ⊗ W)
        (g ▷ W ≫ (A.2.β W).hom ≫ W ◁ f ≫ e ▷ U ≫ R)
      map_add' := by intros; simp [MonoidalPreadditive.add_whiskerRight,
        Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by intros; simp }
  have he (j : F.Label) (α : Fin (Module.finrank ℂ (F.simple j ⟶ W))) :
      g ▷ W ≫ A.1 ◁ F.compositionDual (F.simpleHomBasis W j) α ≫
        (A.2.β (F.simple j)).hom ≫ F.simple j ◁ f ≫
        F.simpleHomBasis W j α ▷ U ≫ R =
      g ▷ W ≫ (A.2.β W).hom ≫ W ◁ f ≫
        (F.compositionDual (F.simpleHomBasis W j) α ≫
          F.simpleHomBasis W j α) ▷ U ≫ R := by
    rw [A.2.naturality_assoc, ← whisker_exchange_assoc]
    simp only [comp_whiskerRight, Category.assoc]
  simp_rw [he]
  change (∑ j, ∑ α, L (F.compositionDual (F.simpleHomBasis W j) α ≫
    F.simpleHomBasis W j α)) = _
  simp_rw [← map_sum]
  rw [F.sum_compositionDual_comp]
  simp [L]

/-- The original forward closure equals the trace of the reverse-Hom operator. -/
theorem forwardTwoBlockClosure_eq_trace (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    (∑ i, ∑ j, twoBlockClosure F V n k i j (forwardChannelCrossing F A i j)) =
      LinearMap.trace ℂ (tensorPower V (k + 1) ⟶ A.1)
        (forwardBlockOperator F.toPivotal A (tensorPower V (n + 1))
          (tensorPower V (k + 1)) (blockReassociation V n k).hom) := by
  let U := tensorPower V (k + 1)
  let W := tensorPower V (n + 1)
  let R := (blockReassociation V n k).hom
  rw [F.linearTrace_eq_sum_normalized_channels (F.simpleHomBasis U)
    (F.simpleHomBasis A.1)]
  simp only [twoBlockClosure, LinearMap.coe_mk, AddHom.coe_mk,
    forwardChannelCrossing, map_smul, map_sum, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext γ
    arg 2; ext j
    rw [Finset.sum_comm]
  conv_lhs => arg 2; ext γ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro γ _
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [forwardBlockOperator_trace_pair]
  convert forwardCrossing_exterior_resolution F A W U
    (F.compositionDual (F.simpleHomBasis U i) β ≫ F.simpleHomBasis A.1 i γ)
    (F.compositionDual (F.simpleHomBasis A.1 i) γ ≫ F.simpleHomBasis U i β) R using 1
  simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp,
    comp_whiskerRight, Category.assoc, U, W, R]
  congr 1
  ext j
  congr 1
  ext α
  congr 1
  rw [← whisker_exchange_assoc (F.simpleHomBasis A.1 i γ),
    ← whisker_exchange_assoc (F.simpleHomBasis W j α)]

end VOA.Huang.NSCongruence

import VOA.Huang.NSSMove5Adjoint

/-! # The full forward two-block trace formula -/
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

/-- Operators adjoint under categorical trace have equal ordinary linear trace. -/
theorem linearTrace_eq_of_trace_pair (F : SphericalFusion C) (A U : C)
    (E : Module.End ℂ (A ⟶ U)) (T : Module.End ℂ (U ⟶ A))
    (h : ∀ f g, F.scalarTrace A (E f ≫ g) = F.scalarTrace A (f ≫ T g)) :
    LinearMap.trace ℂ (A ⟶ U) E = LinearMap.trace ℂ (U ⟶ A) T := by
  rw [F.linearTrace_eq_sum_normalized_channels (F.simpleHomBasis A) (F.simpleHomBasis U),
    F.linearTrace_eq_sum_normalized_channels (F.simpleHomBasis U) (F.simpleHomBasis A)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [h, F.scalarTrace_comp_comm]

/-- Adjointness is preserved by every natural power. -/
theorem trace_pair_pow (F : SphericalFusion C) (A U : C)
    (E : Module.End ℂ (A ⟶ U)) (T : Module.End ℂ (U ⟶ A))
    (h : ∀ f g, F.scalarTrace A (E f ≫ g) = F.scalarTrace A (f ≫ T g))
    (n : ℕ) (f : A ⟶ U) (g : U ⟶ A) :
    F.scalarTrace A ((E ^ n) f ≫ g) = F.scalarTrace A (f ≫ (T ^ n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ' E, Module.End.mul_apply, h, ih, pow_succ T, Module.End.mul_apply]

/-- Forward closures compute the negative power of the genuine central rotation. -/
theorem forwardTwoBlockTrace (F : SphericalFusion C) (A : Center C)
    (V : C) (n k : ℕ) :
    generalizedIndicatorInt F.toPivotal A V k (-(n + 1)) =
      ∑ i, ∑ j, twoBlockClosure F V n k i j (forwardChannelCrossing F A i j) := by
  rw [forwardTwoBlockClosure_eq_trace, forwardBlockOperator_power]
  have he : ((generalizedRotation F.toPivotal A V k) ^ (-(n + 1 : ℤ))).toLinearMap =
      (generalizedRotation F.toPivotal A V k).symm.toLinearMap ^ (n + 1) := by
    ext f
    rw [LinearEquiv.coe_coe]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
      ← inv_pow, LinearEquiv.pow_apply, Module.End.pow_apply]
    rfl
  unfold generalizedIndicatorInt
  rw [he]
  apply linearTrace_eq_of_trace_pair
  exact trace_pair_pow F A.1 (tensorPower V (k + 1)) _ _
    (forwardBlockOperator_single_pair F A V k) (n + 1)

/-- The entire remaining forward clause, without a modularity hypothesis. -/
theorem mixedForwardTraceFormula_holds (F : SphericalFusion C) :
    MixedForwardTraceFormula F := fun V n k a b =>
  forwardTwoBlockTrace F (mixedCenter (F.simple a) (F.simple b)) V n k

/-- Both two-block trace clauses hold. -/
theorem mixedTwoBlockTraceFormula_holds (F : SphericalFusion C) :
    MixedTwoBlockTraceFormula F :=
  (mixedTwoBlockTraceFormula_iff_forward F).mpr (mixedForwardTraceFormula_holds F)

end VOA.Huang.NSCongruence

import VOA.Huang.NSCyclotomicDimensions
import VOA.Huang.NSCongruenceCharge
import VOA.Huang.NgSchauenburgModularFormula

/-! # Projective kernel assembly from the nonzero S move alone

This file uses the S move to obtain cyclotomic dimensions from a finite-order
rotation trace. It does not establish unconditional mixed S cyclotomicity.
No congruence statement is used in the dimension argument.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- Orbit equivariance and the raw T period identify the rows `(N,1)` and `(0,1)`. -/
theorem mixedRow_twistOrder_one_eq_zero_one (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (a : F.Label)
    (z : F.Label × F.Label → ℂ) :
    mixedRow F a M.toRibbon.twistOrder 1 z = mixedRow F a 0 1 z := by
  have he := orbitEquivariance_of_SMove F M hS ρ hr a
  have hn := he (ModularGroup.T ^ (-(M.toRibbon.twistOrder : ℤ)) * ModularGroup.S⁻¹) z
  have h0 := he (ModularGroup.T ^ (-(0 : ℤ)) * ModularGroup.S⁻¹) z
  rw [rowAction_one_T_neg_S_inv, modularInvolution_T_neg_S_inv] at hn h0
  simp only [map_mul, LinearEquiv.mul_apply, zpow_natCast, map_pow,
    mixedRepresentation_T_period F M ρ hr, le_one_apply] at hn
  simp only [zpow_zero, one_mul] at h0
  exact hn.trans h0.symm

/-- The twist-trivial mixed source `(unit*,unit)` has an N-th order rotation
in degree N, hence its degree `(N,1)` indicator lies in `cycloField N`. -/
theorem mixed_unit_indicator_mem_cycloField (F : SphericalFusion C) (M : Modular F)
    (V : C) :
    generalizedIndicatorAll F
      (mixedCenter (F.simple (F.dualLabel F.unitLabel)) (F.simple F.unitLabel)) V
      M.toRibbon.twistOrder 1 ∈ cycloField M.toRibbon.twistOrder := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero M.toRibbon.finite_twist.1.ne'
  have hj := mixedTwistIdentity_holds F M (F.dualLabel F.unitLabel) F.unitLabel
  have hj' : (F.j (mixedCenter (F.simple (F.dualLabel F.unitLabel))
      (F.simple F.unitLabel)).1).hom = (1 : ℂ) • centralDrinfeldMorphism
        (mixedCenter (F.simple (F.dualLabel F.unitLabel)) (F.simple F.unitLabel)) := by
    simpa [M.toRibbon.twistScalar_dualLabel, M.toRibbon.twistScalar_unitLabel] using hj
  rw [hn, Nat.cast_succ, generalizedIndicatorAll_positive]
  let A := mixedCenter (F.simple (F.dualLabel F.unitLabel)) (F.simple F.unitLabel)
  letI := F.homFinite A.1 (tensorPower V (n + 1))
  have hp := generalizedRotation_pow_scalar F.toPivotal A V n one_ne_zero hj'
  simp only [inv_one, one_smul] at hp
  simpa [generalizedIndicatorInt] using
    trace_mem_cycloField (generalizedRotation F.toPivotal A V n).toLinearMap
      (Nat.succ_pos n) hp

open Classical in
/-- Under the S move and a genuine modular lift, dimensions are finite-order
rotation traces in the cyclotomic field of the raw twist order. -/
theorem simpleDimensionsCyclotomic_of_SMove (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) : SimpleDimensionsCyclotomic F M := by
  intro a
  have he := mixedRow_twistOrder_one_eq_zero_one F M hS ρ hr a
    (Pi.single (F.dualLabel F.unitLabel, F.unitLabel) 1)
  simp only [mixedRow, equivariantIndicator_basis, mixedFamily] at he
  rw [mixed_zero_one_value, if_pos rfl, categoricalS_unit_right,
    F.dimension_dualLabel, F.dimension_unitLabel, div_one] at he
  rw [← he]
  exact mixed_unit_indicator_mem_cycloField F M (F.simple a)

open Classical in
theorem mixedSCyclotomic_of_SMove (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) : MixedSCyclotomic F M :=
  mixedSCyclotomic_of_dimensions F M (simpleDimensionsCyclotomic_of_SMove F M hS ρ hr)

open Classical in
/-- The nonzero-row S move alone suffices for each genuine modular lift. -/
theorem projectiveKernel_of_nonzeroSMove (F : SphericalFusion C) (M : Modular F)
    (hS : MixedNonzeroSMove F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder := by
  have hs := SMoveOrbit_of_nonzero F M hS
  exact projectiveKernel_of_SMove_SCyclotomic F M hs (mixedSCyclotomic_of_SMove F M hs ρ hr) ρ hr

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

/-- Only the nonzero-row S move, uniformly over modular categories. -/
def NSMixedNonzeroSMoveAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F), MixedNonzeroSMove F M

/-- The kernel half of NS 6.8 from the nonzero-row S move, with no independent
cyclotomicity assumption. -/
theorem nsProjectiveKernelAll_of_nonzeroSMove (h : NSMixedNonzeroSMoveAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact ⟨M.toRibbon.twistOrder, M.toRibbon.finite_twist.1,
    fun ρ hr => projectiveKernel_of_nonzeroSMove F M (h C F M) ρ hr⟩

end VOA.Huang.DLNBridge

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSScreeningCartan

/-!
# Raising-current reduction for the inverse-DS screening

The affine raising current is the Pi exponential `exp(eta)`.  On the source half lattice its
zero-mode exponent is zero.  On the shifted `nu` coset the exponent is one because
`(eta,nu)=1`; odd locality also forces the relative cocycle sign `-1`.  This file constructs
both actions on their correct carriers.

Their intertwining with the concrete half-power `exp(nu)` is reduced to one bosonic identity:

`- etaDress (a-1) (nuDress b p) = nuDress (b-1) (etaDress a p)`.

This is the `P=1` specialization of the already-proved general-lattice odd-pairing
`shift_comm_P` identity.  The current general-lattice theorem is tied to a positive-definite
integral lattice and therefore cannot be instantiated by the null vectors `eta,nu` in the
hyperbolic Pi realization.  Everything surrounding this direction-parametric Newton identity,
including both charge actions and the full operator reduction, is proved here.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace ScreeningCoset

open Module (End)
open scoped TensorProduct
open InverseDSPi
open HalfLattice

noncomputable section

/-! ## Charge shifts by `eta` -/

/-- Addition of `eta` on a half-lattice label. -/
def addEtaHalfCharge (q : HalfEtaCharge) : HalfEtaCharge := ⟨q.label + 2⟩

/-- Addition of `eta` on a shifted `nu + (r/2)eta` label. -/
def addEtaNuCosetCharge (q : NuCosetCharge) : NuCosetCharge := ⟨q.label + 2⟩

@[simp] theorem addEtaNuCosetCharge_nuCosetCharge (q : HalfEtaCharge) :
    addEtaNuCosetCharge (nuCosetCharge q) = nuCosetCharge (addEtaHalfCharge q) := rfl

def sourceEtaShiftLine : HalfEtaChargeLine →ₗ[ℂ] HalfEtaChargeLine :=
  Finsupp.lsum ℂ (fun q : HalfEtaCharge =>
    (Finsupp.lsingle (addEtaHalfCharge q) : ℂ →ₗ[ℂ] HalfEtaChargeLine))

@[simp] theorem sourceEtaShiftLine_basis (q : HalfEtaCharge) :
    sourceEtaShiftLine (halfEtaChargeBasis q) =
      halfEtaChargeBasis (addEtaHalfCharge q) := by
  rw [sourceEtaShiftLine, halfEtaChargeBasis, Finsupp.lsum_single,
    Finsupp.lsingle_apply]
  rfl

/-- The target shift contains the odd-pairing cocycle `epsilon(eta,nu)=-1`.
The opposite order in the source was normalized with `epsilon(nu,eta)=1`. -/
def targetEtaShiftLine : NuCosetChargeLine →ₗ[ℂ] NuCosetChargeLine :=
  Finsupp.lsum ℂ (fun q : NuCosetCharge =>
    (-1 : ℂ) •
      (Finsupp.lsingle (addEtaNuCosetCharge q) : ℂ →ₗ[ℂ] NuCosetChargeLine))

@[simp] theorem targetEtaShiftLine_basis (q : NuCosetCharge) :
    targetEtaShiftLine (nuCosetChargeBasis q) =
      -nuCosetChargeBasis (addEtaNuCosetCharge q) := by
  rw [targetEtaShiftLine, nuCosetChargeBasis, Finsupp.lsum_single,
    LinearMap.smul_apply, Finsupp.lsingle_apply, neg_one_smul]
  rfl

/-! ## Source and target raising-current fields -/

def sourceEtaExponentialFam (j : ℤ) (q : HalfEtaCharge) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiHalfFockCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiHalfFockCarrier)
    (((TensorProduct.mk ℂ HyperFock HalfEtaChargeLine).flip
      (halfEtaChargeBasis (addEtaHalfCharge q))).comp (etaDress j))

/-- `exp(eta)` on the source half-lattice carrier.  Since `eta` is null, its zero-mode
exponent on every `(1/2)Z eta` sector is zero. -/
def sourceEtaExponentialField : FormalDist (End ℂ PiHalfFockCarrier) :=
  fun j => TensorProduct.lift (Finsupp.lsum ℂ (sourceEtaExponentialFam j)).flip

theorem sourceEtaExponentialField_state (j : ℤ) (p : HyperFock)
    (q : HalfEtaCharge) :
    sourceEtaExponentialField j (piHalfFockState p q) =
      piHalfFockState (etaDress j p) (addEtaHalfCharge q) := by
  rw [sourceEtaExponentialField, piHalfFockState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (sourceEtaExponentialFam j))
    (halfEtaChargeBasis q) p = _
  rw [halfEtaChargeBasis, Finsupp.lsum_single, sourceEtaExponentialFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

def targetEtaExponentialFam (j : ℤ) (q : NuCosetCharge) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiNuCosetCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiNuCosetCarrier)
    (((TensorProduct.mk ℂ HyperFock NuCosetChargeLine).flip
      (-nuCosetChargeBasis (addEtaNuCosetCharge q))).comp (etaDress (j - 1)))

/-- `exp(eta)` on the target `nu` coset.  The oscillator index is shifted by one because
`(eta,nu)=1`, and the charge vector has the relative cocycle sign `-1`. -/
def targetEtaExponentialField : FormalDist (End ℂ PiNuCosetCarrier) :=
  fun j => TensorProduct.lift (Finsupp.lsum ℂ (targetEtaExponentialFam j)).flip

theorem targetEtaExponentialField_state (j : ℤ) (p : HyperFock)
    (q : NuCosetCharge) :
    targetEtaExponentialField j (piNuCosetState p q) =
      -piNuCosetState (etaDress (j - 1) p) (addEtaNuCosetCharge q) := by
  rw [targetEtaExponentialField, piNuCosetState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (targetEtaExponentialFam j))
    (nuCosetChargeBasis q) p = _
  rw [nuCosetChargeBasis, Finsupp.lsum_single, targetEtaExponentialFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rw [piNuCosetState, TensorProduct.tmul_neg]

/-! ## The single bosonic identity and the exact reduction -/

/-- The odd cross-pairing (`(eta,nu)=1`) Newton identity.  This is the precise bosonic
specialization of general-lattice `shift_comm_P` which remains to be made direction-parametric. -/
def EtaNuOddCrossIdentity : Prop :=
  ∀ a b : ℤ, ∀ p : HyperFock,
    -(etaDress (a - 1) (nuDress b p)) =
      nuDress (b - 1) (etaDress a p)

theorem halfPowerMatch_addEta_iff (t : ℤ) (q : HalfEtaCharge) :
    HalfPowerMatch t (addEtaHalfCharge q) ↔ HalfPowerMatch t q := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s + 1, ?_⟩
    change t = 2 * (s + 1) + q.label
    change t = 2 * s + (q.label + 2) at hs
    omega
  · rintro ⟨s, hs⟩
    refine ⟨s - 1, ?_⟩
    change t = 2 * (s - 1) + (q.label + 2)
    omega

theorem raisingCurrent_intertwines_nuExponential_state
    (hcross : EtaNuOddCrossIdentity) (j t : ℤ) (p : HyperFock)
    (q : HalfEtaCharge) :
    targetEtaExponentialField j
        (nuExponentialHalfField t (piHalfFockState p q)) =
      nuExponentialHalfField t
        (sourceEtaExponentialField j (piHalfFockState p q)) := by
  by_cases hm : HalfPowerMatch t q
  · obtain ⟨s, hs⟩ := hm
    rw [nuExponentialHalfField_piHalfFockState_of_eq t s q p hs,
      targetEtaExponentialField_state, sourceEtaExponentialField_state]
    have hs' : t = 2 * (s - 1) + (addEtaHalfCharge q).label := by
      change t = 2 * (s - 1) + (q.label + 2)
      omega
    rw [nuExponentialHalfField_piHalfFockState_of_eq t (s - 1)
      (addEtaHalfCharge q) (etaDress j p) hs']
    rw [addEtaNuCosetCharge_nuCosetCharge]
    exact congrArg
      (fun x => piNuCosetState x (nuCosetCharge (addEtaHalfCharge q)))
      (hcross j s p)
  · rw [nuExponentialHalfField_piHalfFockState_of_not_match t q p hm,
      map_zero, sourceEtaExponentialField_state,
      nuExponentialHalfField_piHalfFockState_of_not_match]
    exact fun h => hm ((halfPowerMatch_addEta_iff t q).mp h)

/-- Assuming exactly the direction-parametric odd Newton identity, the raising current commutes
coefficientwise with the heterotypic screening exponential. -/
theorem raisingCurrent_intertwines_nuExponential
    (hcross : EtaNuOddCrossIdentity) (j t : ℤ) :
    heterotypicBracketCoeff (targetEtaExponentialField j)
      (nuExponentialHalfField t) (sourceEtaExponentialField j) = 0 := by
  refine LinearMap.ext fun x => ?_
  change (heterotypicBracketCoeff (targetEtaExponentialField j)
      (nuExponentialHalfField t) (sourceEtaExponentialField j)) x = 0
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g₁ g₂ h₁ h₂ =>
          erw [TensorProduct.tmul_add, map_add, h₁, h₂, add_zero]
      | single q a =>
          rw [← Finsupp.smul_single_one]
          erw [TensorProduct.tmul_smul, map_smul]
          change a • (targetEtaExponentialField j
              (nuExponentialHalfField t (piHalfFockState p q)) -
            nuExponentialHalfField t
              (sourceEtaExponentialField j (piHalfFockState p q))) = 0
          rw [raisingCurrent_intertwines_nuExponential_state hcross,
            sub_self, smul_zero]

end
end ScreeningCoset
end InverseDS
end VOA

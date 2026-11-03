/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSScreeningTensor
import VOA.Examples.InverseDSPiNegativeExponential

/-!
# The lowering-current screening gate

Adamović--Milas, equation (2.3), realizes the lowering current as

`f = ((k+2) omega - nu(-1)^2 - (k+1) nu(-2)) exp(-eta)`.

At `k=-8/5` the coefficients are `2/5` and `3/5`.  This file constructs the source and shifted
target actions of the last factor `exp(-eta)`.  On the shifted target its zero-mode exponent is
`(-eta,nu)=-1`, so its oscillator coefficient is shifted by `-1`; the odd lattice pairing again
forces a cocycle sign `-1`.

The remaining input is genuinely Virasoro-theoretic.  The screening vector `v^(k)` is a
Virasoro primary of weight `(3/4)k+1=-1/5`.  We state its half-power Ward identity coefficient by
coefficient.  Together with the direction-parametric Newton contraction for pairing `-1`, this
identity is precisely what cancels the simple pole of `exp(-eta)` against the quadratic-linear
`nu` expression in `f`.  The repository does not yet have a concrete Virasoro intertwining
operator on the Lee--Yang module, so this Ward identity is the smallest analytic construction
gap in the lowering-current proof.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace ScreeningLowering

open Module (End)
open scoped TensorProduct
open HalfLattice
open InverseDSPi
open ScreeningCoset

noncomputable section

/-! ## The negative eta exponential on the two Pi carriers -/

def subEtaHalfCharge (q : HalfEtaCharge) : HalfEtaCharge := ⟨q.label - 2⟩

def subEtaNuCosetCharge (q : NuCosetCharge) : NuCosetCharge := ⟨q.label - 2⟩

@[simp] theorem subEtaNuCosetCharge_nuCosetCharge (q : HalfEtaCharge) :
    subEtaNuCosetCharge (nuCosetCharge q) = nuCosetCharge (subEtaHalfCharge q) := rfl

def sourceEtaNegativeFam (j : ℤ) (q : HalfEtaCharge) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiHalfFockCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiHalfFockCarrier)
    (((TensorProduct.mk ℂ HyperFock HalfEtaChargeLine).flip
      (halfEtaChargeBasis (subEtaHalfCharge q))).comp (etaNegDress j))

def sourceEtaNegativeField : FormalDist (End ℂ PiHalfFockCarrier) :=
  fun j => TensorProduct.lift (Finsupp.lsum ℂ (sourceEtaNegativeFam j)).flip

theorem sourceEtaNegativeField_state (j : ℤ) (p : HyperFock)
    (q : HalfEtaCharge) :
    sourceEtaNegativeField j (piHalfFockState p q) =
      piHalfFockState (etaNegDress j p) (subEtaHalfCharge q) := by
  rw [sourceEtaNegativeField, piHalfFockState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (sourceEtaNegativeFam j))
    (halfEtaChargeBasis q) p = _
  rw [halfEtaChargeBasis, Finsupp.lsum_single, sourceEtaNegativeFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

def targetEtaNegativeFam (j : ℤ) (q : NuCosetCharge) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiNuCosetCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiNuCosetCarrier)
    (((TensorProduct.mk ℂ HyperFock NuCosetChargeLine).flip
      (-nuCosetChargeBasis (subEtaNuCosetCharge q))).comp (etaNegDress (j + 1)))

/-- On the target coset, `exp(-eta)` has zero-mode exponent `-1`.  Hence total coefficient `j`
uses oscillator coefficient `j+1`; the prefactor is the odd-pairing cocycle. -/
def targetEtaNegativeField : FormalDist (End ℂ PiNuCosetCarrier) :=
  fun j => TensorProduct.lift (Finsupp.lsum ℂ (targetEtaNegativeFam j)).flip

theorem targetEtaNegativeField_state (j : ℤ) (p : HyperFock)
    (q : NuCosetCharge) :
    targetEtaNegativeField j (piNuCosetState p q) =
      -piNuCosetState (etaNegDress (j + 1) p) (subEtaNuCosetCharge q) := by
  rw [targetEtaNegativeField, piNuCosetState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (targetEtaNegativeFam j))
    (nuCosetChargeBasis q) p = _
  rw [nuCosetChargeBasis, Finsupp.lsum_single, targetEtaNegativeFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, piNuCosetState,
    TensorProduct.tmul_neg]

theorem negEta_nu_pairing_k85 :
    dotProduct (-etaDirection) (nuDirection boundaryLevel85) = -1 := by
  calc
    dotProduct (-etaDirection) (nuDirection boundaryLevel85) =
        -dotProduct etaDirection (nuDirection boundaryLevel85) := by
          simp [dotProduct]
    _ = -1 := by rw [etaDirection_nuDirection]

/-! ## The exact Virasoro Ward input -/

/-- The conformal weight `h_(2,1)=(3/4)k+1` of the screening vector at `k=-8/5`. -/
def k85ScreeningVirWeight : ℂ := -1 / 5

theorem k85ScreeningVirWeight_eq :
    k85ScreeningVirWeight = (3 / 4 : ℂ) * boundaryLevel85 + 1 := by
  norm_num [k85ScreeningVirWeight, boundaryLevel85]

universe u v

variable {Vir : Type u} {ShiftedVir : Type v}
variable [AddCommGroup Vir] [Module ℂ Vir]
variable [AddCommGroup ShiftedVir] [Module ℂ ShiftedVir]

/-- Coefficient form of the primary-field Ward identity
`[L_m,I(z)] = z^m (z d/dz + (m+1)h) I(z)`.

The intertwiner coefficient label `t` represents power `t/2`; therefore the coefficient on the
right is `t-2m`, with scalar `(t-2m)/2 + (m+1)h`. -/
def K85VirasoroIntertwinerWard
    (sourceL : ℤ → End ℂ Vir) (targetL : ℤ → End ℂ ShiftedVir)
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir)) : Prop :=
  ∀ m t : ℤ,
    (targetL m).comp (I t) - (I t).comp (sourceL m) =
      (((t - 2 * m : ℤ) : ℂ) / 2 +
        ((m + 1 : ℤ) : ℂ) * k85ScreeningVirWeight) • I (t - 2 * m)

/-- Minimal concrete data still required from the Lee--Yang intertwining-operator construction.
Lower truncation assembles the full screening; the Ward identity is exactly the new datum used by
the lowering-current cancellation. -/
structure K85VirasoroScreeningFieldData where
  sourceL : ℤ → End ℂ Vir
  targetL : ℤ → End ℂ ShiftedVir
  field : FormalDist (Vir →ₗ[ℂ] ShiftedVir)
  isHeterotypicField : ScreeningCoset.IsHeterotypicField field
  ward : K85VirasoroIntertwinerWard sourceL targetL field

/-- Numerical specialization of the inverse-DS lowering-current formula.  This theorem is kept
as a checked scalar normalization next to the Ward interface. -/
theorem k85_lowering_coefficients :
    (boundaryLevel85 + 2, -(boundaryLevel85 + 1)) =
      ((2 / 5 : ℂ), (3 / 5 : ℂ)) := by
  norm_num [boundaryLevel85]

end
end ScreeningLowering
end InverseDS
end VOA

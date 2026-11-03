/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiLattice

/-!
# The hyperbolic Heisenberg/Fock carrier for inverse DS

This file supplies the smallest honest oscillator representation needed before constructing the
inverse-DS free field `Pi`.  The existing rank-two polynomial Fock space has two orthonormal
oscillator families over `ℂ`.  Complex linear combinations

* `etaDirection = (1, I)` and
* `xiDirection = (1/2, -I/2)`

are null for the complex bilinear dot product and pair to one.  Their modes therefore satisfy the
rank-two hyperbolic Heisenberg relations.  The charge carrier is restricted to `ℂ[ℤ eta]`, modeled
as finitely supported functions on `ℤ`, and tensoring it with the oscillator Fock space gives
`PiFockCarrier`.

This is a representation of the oscillator Lie algebra together with a diagonal charge operator.
It is deliberately not claimed to be a vertex algebra: no exponential fields, cocycle dressing,
mutual locality, state-field correspondence, translation operator, or conformal vector is defined
here.  Those are the remaining reconstruction layer.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDSPi

open scoped BigOperators TensorProduct
open HeisenbergN MvPolynomial

noncomputable section

/-! ## Hyperbolic oscillators on the polynomial Fock space -/

/-- The two-oscillator polynomial Fock space. -/
abbrev HyperFock := HeisenbergN.FockN 2

/-- A mode in an arbitrary complex direction of the two-oscillator Fock space. -/
noncomputable def directionOsc (v : Fin 2 → ℂ) (m : ℤ) : Module.End ℂ HyperFock :=
  ∑ a : Fin 2, v a • HeisenbergN.oscN 2 1 a m

/-- Annihilation and zero modes in every complex direction kill the Fock vacuum. -/
theorem directionOsc_vacuum (v : Fin 2 → ℂ) (m : ℤ) (hm : 0 ≤ m) :
    directionOsc v m (HeisenbergN.vacuumN 2) = 0 := by
  simp only [directionOsc, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    HeisenbergN.oscN_vacuum 2 1 _ m hm, smul_zero, Finset.sum_const_zero]

/-- The commutator of two directional modes is controlled by their complex bilinear dot product. -/
theorem directionOsc_comm (v w : Fin 2 → ℂ) (m n : ℤ) :
    directionOsc v m * directionOsc w n - directionOsc w n * directionOsc v m
      = (if m + n = 0 then dotProduct v w * (m : ℂ) else 0) • LinearMap.id := by
  have e1 : directionOsc v m * directionOsc w n
      = ∑ a : Fin 2, ∑ b : Fin 2, (v a * w b) •
          (HeisenbergN.oscN 2 1 a m * HeisenbergN.oscN 2 1 b n) := by
    simp only [directionOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have e2 : directionOsc w n * directionOsc v m
      = ∑ a : Fin 2, ∑ b : Fin 2, (v a * w b) •
          (HeisenbergN.oscN 2 1 b n * HeisenbergN.oscN 2 1 a m) := by
    simp only [directionOsc]
    rw [Fintype.sum_mul_sum]
    simp only [smul_mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_comm (w b) (v a)]
  have hexpand :
      directionOsc v m * directionOsc w n - directionOsc w n * directionOsc v m
        = ∑ a : Fin 2, ∑ b : Fin 2, (v a * w b) •
            (HeisenbergN.oscN 2 1 a m * HeisenbergN.oscN 2 1 b n
              - HeisenbergN.oscN 2 1 b n * HeisenbergN.oscN 2 1 a m) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_sub]
  have hbr : ∀ a b : Fin 2,
      HeisenbergN.oscN 2 1 a m * HeisenbergN.oscN 2 1 b n
          - HeisenbergN.oscN 2 1 b n * HeisenbergN.oscN 2 1 a m
        = (if a = b ∧ m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
    intro a b
    rw [HeisenbergN.oscN_comm 2 1 a b m n, mul_one]
  rw [hexpand]
  simp only [hbr, smul_smul]
  by_cases hP : m + n = 0
  · rw [if_pos hP]
    simp only [← Finset.sum_smul]
    congr 1
    have hb : ∀ a : Fin 2,
        (∑ b : Fin 2, (v a * w b) *
          (if a = b ∧ m + n = 0 then (m : ℂ) else 0)) = v a * w a * (m : ℂ) := by
      intro a
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
          (fun h => absurd (Finset.mem_univ a) h)]
      simp [hP]
    simp only [hb]
    rw [← Finset.sum_mul]
    rfl
  · rw [if_neg hP, zero_smul]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    simp [hP]

/-- The null oscillator direction corresponding to the lattice vector `eta`. -/
def etaDirection : Fin 2 → ℂ := ![(1 : ℂ), Complex.I]

/-- The transverse null oscillator direction, normalized to pair to one with `etaDirection`. -/
def xiDirection : Fin 2 → ℂ := ![(1 / 2 : ℂ), -Complex.I / 2]

@[simp] theorem etaDirection_self : dotProduct etaDirection etaDirection = 0 := by
  simp [etaDirection, dotProduct, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem xiDirection_self : dotProduct xiDirection xiDirection = 0 := by
  simp [xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

@[simp] theorem etaDirection_xiDirection : dotProduct etaDirection xiDirection = 1 := by
  simp [etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

@[simp] theorem xiDirection_etaDirection : dotProduct xiDirection etaDirection = 1 := by
  rw [dotProduct_comm, etaDirection_xiDirection]

/-- The complex change of basis that realizes the integral hyperbolic plane inside the two
orthonormal oscillator directions. -/
def complexHyperbolicDirection (v : piLattice.carrier) : Fin 2 → ℂ :=
  (v 0 : ℂ) • etaDirection + (v 1 : ℂ) • xiDirection

/-- The change of basis carries the oscillator dot product to the integral hyperbolic form. -/
theorem complexHyperbolicDirection_pairing (v w : piLattice.carrier) :
    dotProduct (complexHyperbolicDirection v) (complexHyperbolicDirection w)
      = (piLattice.form v w : ℂ) := by
  rw [piLattice_form]
  push_cast
  simp [complexHyperbolicDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- The integral charge `q eta` maps to the corresponding multiple of the null oscillator
direction. -/
theorem complexHyperbolicDirection_etaCharge (q : ℤ) :
    complexHyperbolicDirection (etaCharge q) = (q : ℂ) • etaDirection := by
  funext a
  fin_cases a <;> simp [complexHyperbolicDirection, etaDirection, xiDirection]

/-- The modes of the first null current. -/
noncomputable def etaOsc (m : ℤ) : Module.End ℂ HyperFock := directionOsc etaDirection m

/-- The modes of the transverse null current. -/
noncomputable def xiOsc (m : ℤ) : Module.End ℂ HyperFock := directionOsc xiDirection m

/-- The first null current has zero self-commutator. -/
theorem etaOsc_comm (m n : ℤ) : etaOsc m * etaOsc n - etaOsc n * etaOsc m = 0 := by
  simp only [etaOsc]
  rw [directionOsc_comm, etaDirection_self]
  split_ifs <;> simp

/-- The transverse null current has zero self-commutator. -/
theorem xiOsc_comm (m n : ℤ) : xiOsc m * xiOsc n - xiOsc n * xiOsc m = 0 := by
  simp only [xiOsc]
  rw [directionOsc_comm, xiDirection_self]
  split_ifs <;> simp

/-- The normalized hyperbolic cross commutator. -/
theorem etaOsc_xiOsc_comm (m n : ℤ) :
    etaOsc m * xiOsc n - xiOsc n * etaOsc m
      = (if m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
  rw [etaOsc, xiOsc, directionOsc_comm, etaDirection_xiDirection, one_mul]

/-- The Fock vacuum. -/
def hyperVacuum : HyperFock := HeisenbergN.vacuumN 2

/-- The creation operator in direction `v` and oscillator energy `r + 1`. -/
noncomputable def directionCreate (v : Fin 2 → ℂ) (r : ℕ) : Module.End ℂ HyperFock :=
  directionOsc v (-((r : ℤ) + 1))

/-- Creation in the first null direction. -/
noncomputable def etaCreate (r : ℕ) : Module.End ℂ HyperFock := directionCreate etaDirection r

/-- Creation in the transverse null direction. -/
noncomputable def xiCreate (r : ℕ) : Module.End ℂ HyperFock := directionCreate xiDirection r

/-- A creation mode on the vacuum is the expected linear combination of polynomial generators. -/
theorem directionCreate_vacuum (v : Fin 2 → ℂ) (r : ℕ) :
    directionCreate v r hyperVacuum = ∑ a : Fin 2, v a • X (r, a) := by
  simp only [directionCreate, directionOsc, hyperVacuum, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [HeisenbergN.oscN_apply_neg 2 1 a (by omega)]
  simp [HeisenbergN.vacuumN]

@[simp] theorem etaOsc_vacuum (m : ℤ) (hm : 0 ≤ m) : etaOsc m hyperVacuum = 0 := by
  exact directionOsc_vacuum etaDirection m hm

@[simp] theorem xiOsc_vacuum (m : ℤ) (hm : 0 ≤ m) : xiOsc m hyperVacuum = 0 := by
  exact directionOsc_vacuum xiDirection m hm

/-! ## The isotropic charge-line carrier -/

/-- The group-algebra carrier `ℂ[ℤ eta]`, without an asserted multiplication or cocycle here. -/
abbrev EtaChargeLine := ℤ →₀ ℂ

/-- The basis vector of charge `q eta`. -/
def etaChargeBasis (q : ℤ) : EtaChargeLine := Finsupp.single q 1

/-- The oscillator Fock space tensored with the isotropic integral charge line. -/
abbrev PiFockCarrier := HyperFock ⊗[ℂ] EtaChargeLine

/-- A pure oscillator/charge state. -/
def piFockState (p : HyperFock) (q : ℤ) : PiFockCarrier := p ⊗ₜ[ℂ] etaChargeBasis q

/-- The vacuum of the carrier.  This is not yet a vertex-algebra vacuum theorem. -/
def piFockVacuum : PiFockCarrier := piFockState hyperVacuum 0

/-- The bare charge-line state with charge `q eta`. -/
def piFockExponential (q : ℤ) : PiFockCarrier := piFockState hyperVacuum q

@[simp] theorem piFockExponential_zero : piFockExponential 0 = piFockVacuum := rfl

/-- Lift an oscillator endomorphism to the Fock factor of the charge-line carrier. -/
noncomputable def liftHyperOsc (T : Module.End ℂ HyperFock) : Module.End ℂ PiFockCarrier :=
  LinearMap.rTensor EtaChargeLine T

@[simp] theorem liftHyperOsc_piFockState (T : Module.End ℂ HyperFock) (p : HyperFock) (q : ℤ) :
    liftHyperOsc T (piFockState p q) = piFockState (T p) q := by
  rw [liftHyperOsc, piFockState, LinearMap.rTensor_tmul]
  rfl

/-- The charge-line momentum, with eigenvalue `q` on charge `q eta`. -/
noncomputable def etaChargeMomentum : Module.End ℂ EtaChargeLine :=
  Finsupp.lsum ℂ (fun q : ℤ => (q : ℂ) •
    (Finsupp.lsingle q : ℂ →ₗ[ℂ] EtaChargeLine))

@[simp] theorem etaChargeMomentum_basis (q : ℤ) :
    etaChargeMomentum (etaChargeBasis q) = (q : ℂ) • etaChargeBasis q := by
  rw [etaChargeMomentum, etaChargeBasis, Finsupp.lsum_single, LinearMap.smul_apply,
    Finsupp.lsingle_apply]

/-- The transverse zero mode on the full carrier; it reads the integral `eta` charge. -/
noncomputable def xiZeroMode : Module.End ℂ PiFockCarrier :=
  LinearMap.lTensor HyperFock etaChargeMomentum

@[simp] theorem xiZeroMode_piFockState (p : HyperFock) (q : ℤ) :
    xiZeroMode (piFockState p q) = (q : ℂ) • piFockState p q := by
  rw [xiZeroMode, piFockState, LinearMap.lTensor_tmul, etaChargeMomentum_basis,
    TensorProduct.tmul_smul]

@[simp] theorem xiZeroMode_piFockVacuum : xiZeroMode piFockVacuum = 0 := by
  rw [piFockVacuum, xiZeroMode_piFockState]
  simp

/-- Oscillator modes do not change the integral charge sector. -/
theorem liftHyperOsc_preserves_charge (T : Module.End ℂ HyperFock) (p : HyperFock) (q : ℤ) :
    liftHyperOsc T (piFockState p q) = piFockState (T p) q :=
  liftHyperOsc_piFockState T p q

end
end InverseDSPi
end VOA

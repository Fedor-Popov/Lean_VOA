/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiHeisenberg

/-!
# Normalized inverse-DS free-field parameters

This file pins the conversion between the Adamovic--Milas hyperbolic basis and the concrete Pi
oscillators.  In their notation `c = eta` and `d = 2 xi`.  Consequently

* `mu = xi + (k/4) eta`, so the affine Cartan current is `h = 2 mu`;
* `nu = xi - (k/4) eta`, the momentum occurring in the screening and lowering current;
* the Pi background charge is `lambda = -nu`.

The identities below explain both the central charge `2+6k` and why the screening is external:
`nu` has a transverse `xi` component and hence is not an integral or half-integral multiple of
`eta`.
-/

namespace VOA
namespace InverseDSPi

open scoped BigOperators

noncomputable section

/-- Adamovic--Milas's `mu = d/2 + (k/4)c` in the concrete oscillator frame. -/
def muDirection (k : ℂ) : Fin 2 → ℂ := xiDirection + (k / 4) • etaDirection

/-- Adamovic--Milas's `nu = d/2 - (k/4)c` in the concrete oscillator frame. -/
def nuDirection (k : ℂ) : Fin 2 → ℂ := xiDirection - (k / 4) • etaDirection

/-- The Feigin--Fuchs background charge of Pi is `lambda = -nu`. -/
def piBackgroundDirection (k : ℂ) : Fin 2 → ℂ := -nuDirection k

@[simp] theorem etaDirection_muDirection (k : ℂ) :
    dotProduct etaDirection (muDirection k) = 1 := by
  simp [muDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

@[simp] theorem etaDirection_nuDirection (k : ℂ) :
    dotProduct etaDirection (nuDirection k) = 1 := by
  simp [nuDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

@[simp] theorem muDirection_self (k : ℂ) :
    dotProduct (muDirection k) (muDirection k) = k / 2 := by
  simp [muDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

@[simp] theorem nuDirection_self (k : ℂ) :
    dotProduct (nuDirection k) (nuDirection k) = -(k / 2) := by
  simp [nuDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

@[simp] theorem muDirection_nuDirection (k : ℂ) :
    dotProduct (muDirection k) (nuDirection k) = 0 := by
  simp [muDirection, nuDirection, etaDirection, xiDirection, dotProduct, Fin.sum_univ_two]
  ring_nf
  simp only [Complex.I_sq]
  ring

@[simp] theorem piBackgroundDirection_self (k : ℂ) :
    dotProduct (piBackgroundDirection k) (piBackgroundDirection k) = -(k / 2) := by
  simpa [piBackgroundDirection, dotProduct] using nuDirection_self k

@[simp] theorem piBackgroundDirection_eta (k : ℂ) :
    dotProduct (piBackgroundDirection k) etaDirection = -1 := by
  simp [piBackgroundDirection, nuDirection, etaDirection, xiDirection, dotProduct,
    Fin.sum_univ_two]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- Central charge of the rank-two hyperbolic boson with background `lambda=-nu`. -/
def piCentralCharge (k : ℂ) : ℂ := 2 - 12 *
  dotProduct (piBackgroundDirection k) (piBackgroundDirection k)

theorem piCentralCharge_eq (k : ℂ) : piCentralCharge k = 2 + 6 * k := by
  rw [piCentralCharge, piBackgroundDirection_self]
  ring

/-- The boundary level used in the present inverse-DS programme. -/
def boundaryLevel85 : ℂ := -8 / 5

@[simp] theorem piCentralCharge_boundary85 :
    piCentralCharge boundaryLevel85 = -38 / 5 := by
  rw [piCentralCharge_eq]
  norm_num [boundaryLevel85]

/-- The Lee--Yang plus Pi central charge equals the affine Sugawara central charge at level
`-8/5`. -/
theorem leeYang_add_piCentralCharge_boundary85 :
    (-22 / 5 : ℂ) + piCentralCharge boundaryLevel85 = -12 := by
  rw [piCentralCharge_boundary85]
  norm_num

/-- The affine `sl2` Sugawara central-charge formula agrees with the free-field sum. -/
theorem affineSugawaraCentralCharge_boundary85 :
    3 * boundaryLevel85 / (boundaryLevel85 + 2) = -12 := by
  norm_num [boundaryLevel85]

end
end InverseDSPi
end VOA

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangFockExponential
import VOA.Examples.LatticeBackgroundChargeA
import VOA.Examples.HeisenbergNVOA

/-!
# Lee--Yang Virasoro actions on nonintegral rank-one Fock sectors

The polynomial oscillator carrier has no momentum zero mode.  A Fock sector of arbitrary momentum
`p alpha` is therefore obtained by replacing the A1 current by
`alpha_n + 2p delta_(n,0)`.  Its Sugawara modes are
`L_n + p alpha_n + p^2 delta_(n,0)`.  These formulas make sense for every complex `p`, not only
for an integral lattice charge.

This file proves the Heisenberg and Virasoro relations for those arbitrary sectors, applies the
background-charge deformation, and specializes both the momentum-zero source and momentum-`c`
target to central charge `-22/5`.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangFockVirasoro

open Module (End)
open LatExp
open LeeYangWardClosure
open LeeYangFockExponential

noncomputable section

/-- The A1 oscillator on the rank-one polynomial Fock carrier. -/
def alphaMode (n : ℤ) : End ℂ LeeYangFock := HeisenbergN.oscN 1 2 0 n

/-- Current modes in the arbitrary momentum-`p alpha` Fock sector. -/
def sectorCurrent (p : ℂ) (n : ℤ) : End ℂ LeeYangFock :=
  alphaMode n + (if n = 0 then 2 * p else 0) • (1 : End ℂ LeeYangFock)

/-- Sugawara modes in the arbitrary momentum-`p alpha` Fock sector. -/
def sectorSugawara (p : ℂ) (n : ℤ) : End ℂ LeeYangFock :=
  HeisenbergN.LvirN 1 2 n + p • alphaMode n
    + (if n = 0 then p ^ 2 else 0) • (1 : End ℂ LeeYangFock)

/-- A scalar shift of each member of an operator family does not change pairwise commutators. -/
theorem centralShift_comm (A B : End ℂ LeeYangFock) (a b : ℂ) :
    (A + a • (1 : End ℂ LeeYangFock)) * (B + b • (1 : End ℂ LeeYangFock))
      - (B + b • (1 : End ℂ LeeYangFock)) * (A + a • (1 : End ℂ LeeYangFock))
    = A * B - B * A := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- Commutator of two members of a linearly perturbed operator family. -/
theorem linearPerturbation_comm (A B C D : End ℂ LeeYangFock) (p : ℂ) :
    (A + p • B) * (C + p • D) - (C + p • D) * (A + p • B) =
      (A * C - C * A) + p • (A * D - D * A) +
        p • (B * C - C * B) + p ^ 2 • (B * D - D * B) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub,
    smul_smul]
  module

/-- The unshifted A1 current has level two. -/
theorem alphaMode_comm (m n : ℤ) :
    alphaMode m * alphaMode n - alphaMode n * alphaMode m =
      (if m + n = 0 then 2 * (m : ℂ) else 0) • (1 : End ℂ LeeYangFock) := by
  change HeisenbergN.oscN 1 2 0 m * HeisenbergN.oscN 1 2 0 n -
      HeisenbergN.oscN 1 2 0 n * HeisenbergN.oscN 1 2 0 m = _
  rw [HeisenbergN.oscN_comm]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos ⟨rfl, hmn⟩]
    congr 1
    ring
  · rw [if_neg hmn, if_neg (by rintro ⟨_, h⟩; exact hmn h)]
    simp

/-- The shifted current still has level two. -/
theorem sectorCurrent_comm (p : ℂ) (m n : ℤ) :
    sectorCurrent p m * sectorCurrent p n - sectorCurrent p n * sectorCurrent p m =
      (if m + n = 0 then 2 * (m : ℂ) else 0) • (1 : End ℂ LeeYangFock) := by
  rw [sectorCurrent, sectorCurrent, centralShift_comm]
  exact alphaMode_comm m n

/-- The undeformed arbitrary-momentum sector has the usual free-boson central charge one. -/
theorem sectorSugawara_virasoro (p : ℂ) (m n : ℤ) :
    sectorSugawara p m * sectorSugawara p n
        - sectorSugawara p n * sectorSugawara p m =
      ((m : ℂ) - n) • sectorSugawara p (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0) •
          (1 : End ℂ LeeYangFock) := by
  let L : ℤ → End ℂ LeeYangFock := HeisenbergN.LvirN 1 2
  let A : ℤ → End ℂ LeeYangFock := alphaMode
  have hLL := HeisenbergN.L_virasoroN 1 2 (by norm_num : (2 : ℂ) ≠ 0) m n
  have hLAm := HeisenbergN.LvirN_comm_oscN 1 2 (by norm_num : (2 : ℂ) ≠ 0) 0 m n
  have hLAn := HeisenbergN.LvirN_comm_oscN 1 2 (by norm_num : (2 : ℂ) ≠ 0) 0 n m
  have hAA := HeisenbergN.oscN_comm 1 2 (0 : Fin 1) 0 m n
  change
    (L m + p • A m + (if m = 0 then p ^ 2 else 0) • 1) *
        (L n + p • A n + (if n = 0 then p ^ 2 else 0) • 1)
      - (L n + p • A n + (if n = 0 then p ^ 2 else 0) • 1) *
        (L m + p • A m + (if m = 0 then p ^ 2 else 0) • 1)
      = ((m : ℂ) - n) •
          (L (m + n) + p • A (m + n) +
            (if m + n = 0 then p ^ 2 else 0) • 1)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0) • 1
  rw [centralShift_comm]
  change
    (L m + p • A m) * (L n + p • A n) -
        (L n + p • A n) * (L m + p • A m) = _
  have hAL : A m * L n - L n * A m = ((m : ℂ)) • A (m + n) := by
    change L n * A m - A m * L n = (-(m : ℂ)) • A (n + m) at hLAn
    calc
      A m * L n - L n * A m = -(L n * A m - A m * L n) := by abel
      _ = -((-(m : ℂ)) • A (n + m)) := by rw [hLAn]
      _ = (m : ℂ) • A (m + n) := by rw [add_comm n m]; module
  have hAA' := alphaMode_comm m n
  change A m * A n - A n * A m = _ at hAA'
  change L m * A n - A n * L m = (-(n : ℂ)) • A (m + n) at hLAm
  change L m * L n - L n * L m = _ at hLL
  by_cases hmn : m + n = 0
  · have hn : (n : ℂ) = -(m : ℂ) := by
      have : n = -m := by omega
      rw [this]
      push_cast
      ring
    simp only [if_pos hmn]
    rw [linearPerturbation_comm, hLL, hLAm, hAL, hAA']
    simp only [if_pos hmn, hn]
    push_cast
    module
  · simp only [if_neg hmn]
    rw [linearPerturbation_comm, hLL, hLAm, hAL, hAA']
    simp only [if_neg hmn]
    push_cast
    module

/-- The sector Sugawara modes make the shifted current primary of weight one. -/
theorem sectorSugawara_comm_current (p : ℂ) (m n : ℤ) :
    sectorSugawara p m * sectorCurrent p n -
        sectorCurrent p n * sectorSugawara p m =
      (-(n : ℂ)) • sectorCurrent p (m + n) := by
  have hLA := HeisenbergN.LvirN_comm_oscN 1 2
    (by norm_num : (2 : ℂ) ≠ 0) 0 m n
  have hAA := HeisenbergN.oscN_comm 1 2 (0 : Fin 1) 0 m n
  rw [sectorSugawara, sectorCurrent, centralShift_comm]
  have hAA' := alphaMode_comm m n
  change HeisenbergN.LvirN 1 2 m * alphaMode n -
      alphaMode n * HeisenbergN.LvirN 1 2 m =
        (-(n : ℂ)) • alphaMode (m + n) at hLA
  rw [show
      (HeisenbergN.LvirN 1 2 m + p • alphaMode m) * alphaMode n -
          alphaMode n * (HeisenbergN.LvirN 1 2 m + p • alphaMode m) =
        (HeisenbergN.LvirN 1 2 m * alphaMode n -
          alphaMode n * HeisenbergN.LvirN 1 2 m) +
          p • (alphaMode m * alphaMode n - alphaMode n * alphaMode m) by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
        module,
    hLA, hAA']
  by_cases hmn : m + n = 0
  · have hn : (n : ℂ) = -(m : ℂ) := by
      have : n = -m := by omega
      rw [this]
      push_cast
      ring
    rw [if_pos hmn]
    simp only [sectorCurrent, if_pos hmn, hmn, alphaMode,
      HeisenbergN.oscN_zero, zero_add]
    rw [hn]
    simp only [if_true]
    module
  · rw [if_neg hmn, sectorCurrent, if_neg hmn]
    module

/-- Background-current modes in a momentum sector. -/
def sectorBackgroundCurrent (ell p : ℂ) (n : ℤ) : End ℂ LeeYangFock :=
  ell • sectorCurrent p n

/-- Feigin--Fuchs Virasoro modes in the momentum-`p alpha` sector. -/
def sectorVirasoro (ell p : ℂ) (n : ℤ) : End ℂ LeeYangFock :=
  sectorSugawara p n - ((n : ℂ) + 1) • sectorBackgroundCurrent ell p n

/-- Scaling the current by the background parameter scales its central commutator by the square of that parameter. The momentum shift has no effect on this commutator. -/
theorem sectorBackgroundCurrent_comm (ell p : ℂ) (m n : ℤ) :
    sectorBackgroundCurrent ell p m * sectorBackgroundCurrent ell p n
        - sectorBackgroundCurrent ell p n * sectorBackgroundCurrent ell p m =
      (if m + n = 0 then (2 * ell ^ 2) * (m : ℂ) else 0) •
        (1 : End ℂ LeeYangFock) := by
  rw [sectorBackgroundCurrent, sectorBackgroundCurrent]
  rw [show
      (ell • sectorCurrent p m) * (ell • sectorCurrent p n) -
          (ell • sectorCurrent p n) * (ell • sectorCurrent p m) =
        ell ^ 2 • (sectorCurrent p m * sectorCurrent p n -
          sectorCurrent p n * sectorCurrent p m) by
        simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
        ring]
  rw [sectorCurrent_comm, smul_smul]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    congr 1
    ring
  · rw [if_neg hmn, if_neg hmn, mul_zero, zero_smul]

/-- The background current transforms as a weight-one current under the sector Sugawara action. This mixed commutator controls the cross terms when the stress tensor is shifted. -/
theorem sectorSugawara_comm_backgroundCurrent (ell p : ℂ) (m n : ℤ) :
    sectorSugawara p m * sectorBackgroundCurrent ell p n
        - sectorBackgroundCurrent ell p n * sectorSugawara p m =
      (-(n : ℂ)) • sectorBackgroundCurrent ell p (m + n) := by
  rw [sectorBackgroundCurrent, sectorBackgroundCurrent]
  rw [show
      sectorSugawara p m * (ell • sectorCurrent p n) -
          (ell • sectorCurrent p n) * sectorSugawara p m =
        ell • (sectorSugawara p m * sectorCurrent p n -
          sectorCurrent p n * sectorSugawara p m) by
        simp only [mul_smul_comm, smul_mul_assoc, smul_sub]]
  rw [sectorSugawara_comm_current, smul_smul, smul_smul]
  congr 1
  ring

/-- The background-deformed arbitrary-momentum sector is Virasoro of central charge
`1 - 24 ell^2`. -/
theorem sectorVirasoro_virasoro (ell p : ℂ) (m n : ℤ) :
    sectorVirasoro ell p m * sectorVirasoro ell p n
        - sectorVirasoro ell p n * sectorVirasoro ell p m =
      ((m : ℂ) - n) • sectorVirasoro ell p (m + n)
        + (if m + n = 0 then
            ((m : ℂ) ^ 3 - m) / 12 * (1 - 24 * ell ^ 2) else 0) •
          (1 : End ℂ LeeYangFock) := by
  have hcore := LatGen.BgA.bg_virasoro_core
    (sectorSugawara p) (sectorBackgroundCurrent ell p) 1 (2 * ell ^ 2)
    (fun s t => by
      rw [sectorSugawara_virasoro]
      by_cases hst : s + t = 0 <;> simp [hst])
    (sectorSugawara_comm_backgroundCurrent ell p)
    (sectorBackgroundCurrent_comm ell p) m n
  simpa only [sectorVirasoro, mul_one,
    show (1 - 12 * (2 * ell ^ 2) : ℂ) = 1 - 24 * ell ^ 2 by ring] using hcore

/-- At the selected background, every momentum sector carries Lee--Yang central charge. -/
theorem k85SectorVirasoro_isLeeYang (p : ℂ) :
    IsLeeYangModeFamily (sectorVirasoro k85FockBackground p) := by
  intro m n
  rw [sectorVirasoro_virasoro]
  have hc : (1 - 24 * k85FockBackground ^ 2 : ℂ) = leeYangCentralCharge := by
    have h := k85FockBackground_normSq
    rw [leeYangCentralCharge]
    linear_combination (-12) * h
  rw [hc]
  simp only [ite_smul, zero_smul]

/-- Source Lee--Yang Fock Virasoro modes. -/
def k85SourceL : ℤ → End ℂ LeeYangFock :=
  sectorVirasoro k85FockBackground 0

/-- Shifted-target Lee--Yang Fock Virasoro modes. -/
def k85TargetL : ℤ → End ℂ LeeYangFock :=
  sectorVirasoro k85FockBackground k85FockCharge

/-- The zero-momentum source Fock modes satisfy the Virasoro commutation relations at Lee–Yang central charge. This is a statement about their operator algebra, not about simplicity of the Fock representation. -/
theorem k85SourceL_isLeeYang : IsLeeYangModeFamily k85SourceL :=
  k85SectorVirasoro_isLeeYang 0

/-- The shifted target sector satisfies the same Lee–Yang Virasoro relations as the source. Changing momentum changes the vacuum weight but leaves the central charge unchanged. -/
theorem k85TargetL_isLeeYang : IsLeeYangModeFamily k85TargetL :=
  k85SectorVirasoro_isLeeYang k85FockCharge

end
end LeeYangFockVirasoro
end InverseDS
end VOA

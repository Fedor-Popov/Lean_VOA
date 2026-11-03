/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangFockBoundary
import VOA.Examples.LatticeChargeMFields

/-!
# A nonintegral Lee--Yang Fock exponential

The rank-one A1 oscillator implementation already contains a direction-parametric Newton
exponential `EEC c` for every complex scalar `c`; only the charge-line part of the lattice VOA is
integral.  We use that arbitrary-momentum oscillator field directly.

We choose the large Lee--Yang branch `X = 2/5`.  Since the A1 oscillator has norm two, the
exponential momentum is `c alpha` with `c^2 = 2/5`, and the background charge is
`lambda = (3/4)c alpha`.  The resulting weight is `c^2 - 2 lambda c = -1/5`.

The source sector has momentum zero, so the oscillator coefficient with integral power `s`
has half-power numerator `t = 2s`.  Odd coefficients vanish.  This file constructs that
heterotypic coefficient field and proves lower truncation without any lattice-integrality
hypothesis.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangFockExponential

open Module (End)
open ScreeningCoset ScreeningLowering
open LatExp

noncomputable section

/-- The oscillator Fock carrier used for both the momentum-zero source sector and the
momentum-`c alpha` target sector.  Their Virasoro actions will differ. -/
abbrev LeeYangFock := LatExp.B

/-- The selected nonintegral A1 momentum coefficient, on the `X = 2/5` branch. -/
def k85FockCharge : ℂ := ((Real.sqrt (2 / 5 : ℝ) : ℝ) : ℂ)

/-- The selected momentum has half norm `c^2 = 2/5`. -/
theorem k85FockCharge_sq : k85FockCharge ^ 2 = (2 / 5 : ℂ) := by
  have hreal : Real.sqrt (2 / 5 : ℝ) ^ 2 = (2 / 5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [k85FockCharge]
  simpa using congrArg (fun x : ℝ => (x : ℂ)) hreal

/-- The rank-one background coefficient `lambda = 3c/4`. -/
def k85FockBackground : ℂ := (3 / 4) * k85FockCharge

/-- Its ambient squared norm is `2 lambda^2 = 9/20`. -/
theorem k85FockBackground_normSq :
    2 * k85FockBackground ^ 2 = (9 / 20 : ℂ) := by
  rw [k85FockBackground, mul_pow, k85FockCharge_sq]
  norm_num

/-- The chosen charged exponential has Lee--Yang weight `-1/5`. -/
theorem k85FockWeight :
    k85FockCharge ^ 2 - 2 * k85FockBackground * k85FockCharge =
      k85ScreeningVirWeight := by
  calc
    k85FockCharge ^ 2 - 2 * k85FockBackground * k85FockCharge =
        (-1 / 2 : ℂ) * k85FockCharge ^ 2 := by
          rw [k85FockBackground]
          ring
    _ = k85ScreeningVirWeight := by
      rw [k85FockCharge_sq, k85ScreeningVirWeight]
      norm_num

/-! ## Half-power reindexing -/

/-- An integral oscillator power `s` represents half-power numerator `t = 2s`. -/
def EvenHalfPowerMatch (t : ℤ) : Prop := ∃ s : ℤ, t = 2 * s

/-- The oscillator index belonging to an even half-power numerator. -/
def matchedOscillatorIndex (t : ℤ) (h : EvenHalfPowerMatch t) : ℤ := h.choose

theorem matchedOscillatorIndex_eq (t s : ℤ)
    (hmatch : EvenHalfPowerMatch t) (h : t = 2 * s) :
    matchedOscillatorIndex t hmatch = s := by
  have hs := hmatch.choose_spec
  dsimp only [matchedOscillatorIndex]
  omega

/-- The arbitrary-momentum Fock exponential, indexed by half-power numerators.  Its coefficients
are heterotypic maps from the momentum-zero Fock sector to the momentum-`c alpha` sector; the
underlying vector spaces happen to be the same polynomial Fock space. -/
noncomputable def k85FockField : FormalDist (LeeYangFock →ₗ[ℂ] LeeYangFock) := by
  classical
  exact
  fun t => if h : EvenHalfPowerMatch t
    then EEC k85FockCharge (matchedOscillatorIndex t h)
    else 0

theorem k85FockField_of_eq (t s : ℤ) (h : t = 2 * s) :
    k85FockField t = EEC k85FockCharge s := by
  classical
  rw [k85FockField, dif_pos ⟨s, h⟩]
  congr 1
  apply matchedOscillatorIndex_eq t s
  exact h

theorem k85FockField_of_not_match (t : ℤ) (h : ¬ EvenHalfPowerMatch t) :
    k85FockField t = 0 := by
  classical
  rw [k85FockField, dif_neg h]

/-- The nonintegral half-power exponential is lower truncated on every source Fock vector. -/
theorem k85FockField_isHeterotypicField :
    ScreeningCoset.IsHeterotypicField k85FockField := by
  intro x
  obtain ⟨B, hB⟩ := EEC_isField k85FockCharge x
  refine ⟨2 * B, fun t ht => ?_⟩
  by_cases hm : EvenHalfPowerMatch t
  · obtain ⟨s, hs⟩ := hm
    rw [k85FockField_of_eq t s hs]
    exact hB s (by omega)
  · rw [k85FockField_of_not_match t hm, LinearMap.zero_apply]

end
end LeeYangFockExponential
end InverseDS
end VOA

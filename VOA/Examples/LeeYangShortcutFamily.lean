import VOA.Examples.AffineSl2BoundarySingularFamily
import VOA.Examples.AffineSl2BelowCriticalAnchor
import VOA.Examples.VirasoroBoundaryRealStructure

/-!
# Level-generic arithmetic and auxiliary positivity for the shortcut

For boundary affine level `-2 + 2/(2n+1)`, the diagonal coset has the
`M(2,2n+3)` central charge. Its anomaly-cancelling auxiliary level is always
below critical, so auxiliary graded unitarity requires no per-index input.

OPEN: per-index coset/relative-complex constructions, Kähler geometry,
tensor positivity, filtered Virasoro image comparison, normalized invariant
metric comparison, and the refined character. No family transfer endpoint
is asserted here.
-/

namespace VOA.LeeYangShortcutFamily

open AffineSl2BoundarySingularFamily AffineSl2BelowCritical VirGradedUnitarity
open AffineSl2GeneralRigidity

noncomputable section

/-- The target is the boundary minimal model with odd parameter `2n+3`. -/
abbrev centralCharge (n : ℕ) : ℂ := boundaryCharge (n + 1)

/-- The explicit `M(2,2n+3)` central-charge formula. -/
theorem centralCharge_formula (n : ℕ) :
    centralCharge n = 1 - 3 * (2 * (n : ℂ) + 1) ^ 2 / (2 * n + 3) := by
  simp only [centralCharge, boundaryCharge, boundaryMinimalCentralCharge,
    Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_add, Nat.cast_add, Nat.cast_one]
  congr 2 <;> ring

/-- Subtracting the diagonal Sugawara charge gives exactly the target charge. -/
theorem diagonal_coset_centralCharge (n : ℕ) :
    3 * level n / (level n + 2) + 1 -
        3 * (level n + 1) / (level n + 3) = centralCharge n := by
  rw [centralCharge_formula]
  have hq : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (2 * (n : ℚ) + 1) ≠ 0 by positivity)
  have hq' : (2 * (n : ℂ) + 3) ≠ 0 := by
    exact_mod_cast (show (2 * (n : ℚ) + 3) ≠ 0 by positivity)
  simp only [level, denominator, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  field_simp [hq, hq']
  ring_nf
  have hq'' : (3 + (n : ℂ) * 2) ≠ 0 := by simpa [add_comm, mul_comm] using hq'
  field_simp [hq'']
  ring

/-- At the first nontrivial affine boundary level the target is Lee--Yang. -/
@[simp] theorem centralCharge_one : centralCharge 1 = LeeYang.leeYangC :=
  boundaryCharge_two_eq_leeYangC

/-- The already constructed canonical real structure at each target charge. -/
abbrev realStructure (n : ℕ) : RealStructure (VirSimple.virasoroSimple (centralCharge n)) :=
  boundaryVirasoroRealStructure (n + 1)

/-- The real auxiliary level cancelling the diagonal affine anomaly. -/
def auxiliaryLevel (n : ℕ) : ℝ := -3 - 2 / (2 * (n : ℝ) + 1)

/-- This is the BRST anomaly level `-4-(k+1)` for the diagonal level `k+1`. -/
theorem auxiliaryLevel_eq (n : ℕ) :
    (auxiliaryLevel n : ℂ) = -4 - (level n + 1) := by
  simp only [auxiliaryLevel, level, denominator, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- All auxiliary levels lie strictly below the affine critical level. -/
theorem auxiliaryLevel_below_critical (n : ℕ) : auxiliaryLevel n < -2 := by
  have h : (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) := by positivity
  dsimp [auxiliaryLevel]
  linarith

/-- Auxiliary graded unitarity is discharged for the whole boundary family. -/
theorem auxiliary_gradedUnitary (n : ℕ) :
    GradedUnitary
      (universalForm (auxiliaryLevel n : ℂ)
        (noncritical_of_lt (auxiliaryLevel_below_critical n)))
      (compactRealFamily (auxiliaryLevel n) (auxiliaryLevel_below_critical n))
      (ordinaryFlag (auxiliaryLevel n : ℂ)
        (noncritical_of_lt (auxiliaryLevel_below_critical n))) :=
  universal_gradedUnitary_belowCritical_unconditional
    (auxiliaryLevel n) (auxiliaryLevel_below_critical n)

end
end VOA.LeeYangShortcutFamily

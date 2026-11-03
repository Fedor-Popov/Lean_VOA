import VOA.Classification.COne.OrbC2gSectors

/-! # Arithmetic audit of the printed Dong--Jiang leading-coefficient formula

This file checks the ten-term expression in the proof of Lemma 4.4 of
arXiv:1209.1168v2. At weight 20 it differs from `djC20` by a factor of 13;
at weight 22 it agrees with `djC22`. The expression is NOT identified with
a VOA coefficient in this file, so this is not a disproof of CubicSeedRemainders.
-/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2g
open OrbC2b

/-- Coefficient of the pure first-oscillator monomial in an E-E term. -/
def printedEE (r : ℕ) : ℚ := 2 * 8^(r/2) / r.factorial

/-- The analogous coefficient in sqrt(2) times an E-F term (r odd). -/
def printedEF (r : ℕ) : ℚ := -8 * 8^((r-1)/2) / r.factorial

/-- The ten terms printed in the proof of Dong--Jiang Lemma 4.4,
with N the total weight. No state-level interpretation is assumed. -/
def printedLeading (N : ℕ) : ℚ :=
  -2700 * printedEE N - 13500 * printedEE (N-2) -
    18000 * printedEF (N-3) - 31500 * printedEE (N-4) -
    15300 * printedEF (N-5) - 9060 * printedEE (N-6) -
    1620 * printedEF (N-7) - 345 * printedEE (N-8) -
    20 * printedEF (N-9) - printedEE (N-10)

/-- Exact evaluation of the printed expression; denominator includes 13. -/
theorem printedLeading_twenty : printedLeading 20 = -447232 / 169744575 := by
  decide +kernel

theorem printedLeading_twenty_two : printedLeading 22 = djC22 := by
  decide +kernel

theorem printedLeading_twenty_eq_thirteenth : printedLeading 20 = djC20 / 13 := by
  decide +kernel

/-- The printed expression and the existing target constant disagree. -/
theorem printedLeading_twenty_ne_target : printedLeading 20 ≠ djC20 := by
  decide +kernel

/-- The raw weight-sixteen seed's leading coefficient found by the independent
rational calculation. Its identification with the actual state is not asserted here. -/
def candidateSeedLeading : ℚ := 1024 / 23648625

/-- Candidate pure L(-2) vacuum coefficients from exact rational elimination.
These numbers are data, not VOA decomposition theorems. -/
def candidateVacuum20 : ℚ := -32810205184 / 1867190325
def candidateVacuum22 : ℚ := -389824230981632 / 289024257597075

theorem candidate_coefficients_consistent :
    candidateVacuum20 = 2^10 * (printedLeading 20 - djB20/4*candidateSeedLeading) ∧
    candidateVacuum22 = 2^11 * (printedLeading 22 - djB22/8*candidateSeedLeading) := by
  decide +kernel

/-- Even allowing a free parameter does not reconcile these two candidate
vacuum coefficients with the unchanged pair of target constants. -/
theorem no_common_parameter_for_candidate_coefficients :
    ¬ ∃ t : ℂ,
      (candidateVacuum20 : ℂ) = 2^10 * ((djC20 : ℂ) - djB20/4*t) ∧
      (candidateVacuum22 : ℂ) = 2^11 * ((djC22 : ℂ) - djB22/8*t) := by
  rintro ⟨t,h20,h22⟩
  norm_num [candidateVacuum20, candidateVacuum22, djC20, djC22, djB20, djB22] at h20 h22
  have ht : t = (1024/23648625 : ℂ) := by
    linear_combination (norm := ring_nf) (189189/4968632320 : ℂ) * h22
  rw [ht] at h20
  norm_num at h20

/-- Correcting the weight-20 number retains the nonzero determinant needed
by the final C2 argument. This is still only arithmetic. -/
theorem corrected_determinant_ne_zero :
    (2^10 * printedLeading 20) * djB22 - (2^11 * djC22) * djB20 ≠ 0 := by
  decide +kernel

end VOA.Classification.COne.OrbC2g

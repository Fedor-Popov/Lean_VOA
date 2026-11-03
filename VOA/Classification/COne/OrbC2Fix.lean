/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbC2bRelations
import VOA.Classification.COne.OrbC2gArithmetic

/-!
# Correcting the weight-20 constant of Dong–Jiang Lemma 4.4

The constant `OrbC2b.djC20` was transcribed from the printed statement of Dong–Jiang
(arXiv:1209.1168), Lemma 4.4.  Evaluating the ten-term expression in the paper's own proof gives
`djC20 / 13` instead (`OrbC2g.printedLeading_twenty_eq_thirteenth`, kernel-checked), and an
independent rational elimination is consistent with the corrected value but with no value of the
free parameter for the transcribed one (`OrbC2g.candidate_coefficients_consistent`,
`OrbC2g.no_common_parameter_for_candidate_coefficients`).  Hence the residual
`OrbC2b.TetrahedralDongJiangRelations`, stated with `djC20`, is very likely FALSE as stated.

This file states the CORRECTED relation `TetrahedralDongJiangRelationsCorrected` (weight-20
constant `djC20Corrected = printedLeading 20`) and shows that the whole `C₂` argument survives:
the free coefficient `t` of the weight-sixteen primary cancels from the elimination determinant for
every value of the weight-20 constant, and the corrected determinant is nonzero
(`OrbC2g.corrected_determinant_ne_zero`).

Status: the corrected relations themselves are still an OPEN VOA input (their state-level
certificates are not proved here); nothing in this file is unconditional for `C₂`.
-/

namespace VOA.Classification.COne.OrbC2Fix

open VOA.Classification.COne VOA.Classification.COne.OrbC2b VOA.Classification.COne.OrbC2g

/-- The corrected weight-20 constant: the value of Dong–Jiang's ten-term expression. -/
def djC20Corrected : ℚ := printedLeading 20

theorem djC20Corrected_eq : djC20Corrected = djC20 / 13 :=
  printedLeading_twenty_eq_thirteenth

theorem djC20Corrected_ne_djC20 : djC20Corrected ≠ djC20 :=
  printedLeading_twenty_ne_target

theorem corrected_determinant_ne_zero' :
    (2 ^ 10 * djC20Corrected) * djB22 - (2 ^ 11 * djC22) * djB20 ≠ 0 :=
  corrected_determinant_ne_zero

/-- The unknown coefficient `t` cancels from the corrected determinant. -/
theorem corrected_shifted_determinant (t : ℂ) :
    (2 ^ 10 * ((djC20Corrected : ℂ) - (djB20 : ℂ) / 4 * t)) * (djB22 : ℂ) -
      (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) * (djB20 : ℂ) ≠ 0 := by
  have he :
      (2 ^ 10 * ((djC20Corrected : ℂ) - (djB20 : ℂ) / 4 * t)) * (djB22 : ℂ) -
      (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) * (djB20 : ℂ) =
      (2 ^ 10 * (djC20Corrected : ℂ)) * (djB22 : ℂ) -
        (2 ^ 11 * (djC22 : ℂ)) * (djB20 : ℂ) := by ring
  rw [he]
  exact_mod_cast corrected_determinant_ne_zero'

section Elimination
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The corrected relations force the vacuum's eleventh conformal power to vanish. -/
theorem dongJiang_elimination_corrected (D : Module.End ℂ M) (v x : M) (t : ℂ)
    (h20 : (2 ^ 10 * ((djC20Corrected : ℂ) - (djB20 : ℂ) / 4 * t)) • ((D ^ 10) v) +
      (djB20 : ℂ) • ((D ^ 2) x) = 0)
    (h22 : (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) • ((D ^ 11) v) +
      (djB22 : ℂ) • ((D ^ 3) x) = 0) :
    (D ^ 11) v = 0 ∧ (D ^ 3) x = 0 := by
  have h := congrArg D h20
  simp only [map_add, map_smul, map_zero] at h
  have hp (j : ℕ) (y : M) : D ((D ^ j) y) = (D ^ (j + 1)) y := by
    rw [pow_succ', Module.End.mul_apply]
  rw [hp, hp] at h
  exact exceptional_two_relations_vanish (corrected_shifted_determinant t) h h22

end Elimination

/-- OPEN VOA input, CORRECTED: Dong–Jiang Lemmas 4.3–4.4 with the weight-20 constant evaluated
from the paper's own ten-term expression. -/
def TetrahedralDongJiangRelationsCorrected : Prop :=
  ∃ (X : (orbifold tetra).carrier) (t : ℂ), X ∈ (orbifoldVOA tetra).grading 16 ∧
    let W := orbifoldVOA tetra
    let D := exceptionalConformalEnd W
    let v := mk₂ W W.vacuum
    let x := mk₂ W X
    (2 ^ 10 * ((djC20Corrected : ℂ) - (djB20 : ℂ) / 4 * t)) • ((D ^ 10) v) +
      (djB20 : ℂ) • ((D ^ 2) x) = 0 ∧
    (2 ^ 11 * ((djC22 : ℂ) - (djB22 : ℂ) / 8 * t)) • ((D ^ 11) v) +
      (djB22 : ℂ) • ((D ^ 3) x) = 0

/-- The `A₄` `C₂` theorem from the CORRECTED relations and the span input. -/
theorem tetra_c2Cofinite_of_dongJiang_corrected (hs : TetrahedralConformalSpan)
    (hr : TetrahedralDongJiangRelationsCorrected) : C2Cofinite (orbifoldVOA tetra) := by
  obtain ⟨X, t, _, h20, h22⟩ := hr
  exact c2Cofinite_of_conformal_towers _ hs (dongJiang_elimination_corrected _ _ _ t h20 h22).1

/-- The moving-pair input for `A₄` from the corrected relations. -/
theorem tetrahedralMovingPairSpan_of_dongJiang_corrected (hF : TetrahedralStandardForm)
    (hs : TetrahedralConformalSpan) (hr : TetrahedralDongJiangRelationsCorrected) :
    OrbC2.TetrahedralMovingPairSpan :=
  tetrahedralMovingPairSpan_of_cubic hF
    (cubicMovingPairSpan_iff_tetra_c2.mpr (tetra_c2Cofinite_of_dongJiang_corrected hs hr))

end VOA.Classification.COne.OrbC2Fix

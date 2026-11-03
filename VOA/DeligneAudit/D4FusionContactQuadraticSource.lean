import VOA.DeligneAudit.D4FusionContactQuadraticSourceCore

/-! The 27 quadratic certificate rows are actual source relations modulo
radical length one. No finite-dimensionality or numerical-rank premise. -/
namespace VOA.DeligneAudit.D4FusionContact.Quadratic.Source

open VOA.DeligneAudit.SectorWeyl
open scoped BigOperators

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

/-- Every raw certificate row vanishes in the actual quotient by length one. -/
theorem raw_row_zero (h : HighestRel R w m)
    (hs : R.op 18 0 (R.op 18 0 w) = 0) (r : Fin 27) :
    rowEval R w (raw r) = 0 := by
  induction r using Fin.strong_induction_on with
  | h r ih =>
      by_cases hr : r = 0
      · subst r
        simp only [rowEval, raw_zero, Int.cast_ite, Int.cast_one, Int.cast_zero,
          ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        change (piece R w 1).mkQ (R.op 18 0 (R.op 18 0 w)) = 0
        rw [hs, map_zero]
      · have he : raw r = derive (direction r) (raw (previous r)) :=
          funext (recurrence r hr)
        rw [he, rowEval_derive h, ih (previous r) (previous_lt r hr), map_zero]

/-- The machine-checked integer rows annihilate actual quadratic source
words modulo radical length one. This is the source bridge used by the
independent nine-column elimination certificate. -/
theorem raw_rows_mem (h : HighestRel R w m)
    (hs : R.op 18 0 (R.op 18 0 w) = 0) (r : Fin 27) :
    (∑ j : Fin 36, (raw r j : ℂ) •
      R.op (pair j).1 0 (R.op (pair j).2 0 w)) ∈ piece R w 1 := by
  apply (Submodule.Quotient.mk_eq_zero (piece R w 1)).mp
  change (piece R w 1).mkQ _ = 0
  simpa only [rowEval, qcolumn, quadratic, pair_indices, map_sum, map_smul] using
    raw_row_zero h hs r

/-- The same source bridge in endomorphism-power notation. -/
theorem raw_rows_mem_of_square (h : HighestRel R w m)
    (hs : (R.op 18 0 ^ 2) w = 0) (r : Fin 27) :
    (∑ j : Fin 36, (raw r j : ℂ) •
      R.op (pair j).1 0 (R.op (pair j).2 0 w)) ∈ piece R w 1 :=
  raw_rows_mem h (by simpa only [pow_two, Module.End.mul_apply] using hs) r

end
end VOA.DeligneAudit.D4FusionContact.Quadratic.Source

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.raw_rows_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.raw_rows_mem_of_square

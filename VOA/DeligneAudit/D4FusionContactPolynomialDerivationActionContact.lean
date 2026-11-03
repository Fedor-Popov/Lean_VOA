import VOA.DeligneAudit.D4FusionContactPolynomialDerivationActionCore
import VOA.DeligneAudit.D4FusionContactCurrentPolarization

/-! Actual normalized positive-contact currents on the restricted PBW grading.
They kill the generator, send a central letter to its radical partner,
and commute with the eight other letters modulo strictly lower length. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl

noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

/-- The actual normalized positive-contact action, with PBW degree zero. -/
def eGr (h : HighestRel R w m) (i : Fin 8) (k : ℕ) : Module.End ℂ (Gr R w) :=
  grPreservingOp R w (currentRaise R i k)
    (fun _ _ hv => current_raise_mem h i k hv)

theorem eGr_generator_zero (h : HighestRel R w m) (i : Fin 8) (k : ℕ) :
    eGr h i k (grGenerator R w) = 0 := by
  apply Subtype.ext
  change (grPreservingOp R w (currentRaise R i k)
    (fun _ _ hv => current_raise_mem h i k hv) (grWord R w []) : AmbientGr R w) = 0
  rw [grPreservingOp_grWord]
  change symbol R w 0 (currentRaise R i k w) = 0
  rw [current_raise_kills h i k, map_zero]

/-- The center bracket is an actual radical current and survives at top length. -/
theorem eGr_center_comm (h : HighestRel R w m) (i : Fin 8) (k r : ℕ) :
    eGr h i k * grOp R w 8 r - grOp R w 8 r * eGr h i k =
      grOp R w i.castSucc (k + r) := by
  apply LinearMap.ext_on_range (grWord_span_top R w)
  intro l
  apply Subtype.ext
  change (((grPreservingOp R w (currentRaise R i k)
    (fun _ _ hv => current_raise_mem h i k hv) * grOp R w 8 r -
      grOp R w 8 r * grPreservingOp R w (currentRaise R i k)
        (fun _ _ hv => current_raise_mem h i k hv)) (grWord R w l)) : AmbientGr R w) = _
  rw [grPreservingOp_comm_word]
  have hc := congrArg (fun T : Module.End ℂ V => T (nword R w l))
    (current_raise_center_comm R i k r)
  change currentRaise R i k (R.op (radIndex 8) r (nword R w l)) -
    R.op (radIndex 8) r (currentRaise R i k (nword R w l)) =
      R.op (radIndex i.castSucc) (k+r) (nword R w l) at hc
  rw [hc, grOp_grWord]
  rfl

/-- The noncentral bracket is a zero-grade current, hence lies strictly
below the length of this graded commutator on actual word symbols. -/
theorem eGr_radical_comm (h : HighestRel R w m) (i j : Fin 8) (k r : ℕ) :
    eGr h i k * grOp R w j.castSucc r -
      grOp R w j.castSucc r * eGr h i k = 0 := by
  apply LinearMap.ext_on_range (grWord_span_top R w)
  intro l
  apply Subtype.ext
  change (((grPreservingOp R w (currentRaise R i k)
    (fun _ _ hv => current_raise_mem h i k hv) * grOp R w j.castSucc r -
      grOp R w j.castSucc r * grPreservingOp R w (currentRaise R i k)
        (fun _ _ hv => current_raise_mem h i k hv)) (grWord R w l)) : AmbientGr R w) = 0
  rw [grPreservingOp_comm_word]
  have hv := current_bracket_root_word_mem h i j k r l
  rw [← Ple_eq_currentPiece] at hv
  exact symbol_zero_of_mem R w hv

/-- The normalized contact derivation replaces exactly the central color. -/
theorem eGr_comm (h : HighestRel R w m) (i : Fin 8) (j : Fin 9) (k r : ℕ) :
    eGr h i k * grOp R w j r - grOp R w j r * eGr h i k =
      if j = 8 then grOp R w i.castSucc (k + r) else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [if_pos rfl] using eGr_center_comm h i k r
  · have hj : j.castSucc ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      change j.val = 8 at hv
      omega
    simpa only [if_neg hj] using eGr_radical_comm h i j k r

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.eGr_generator_zero
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.eGr_comm

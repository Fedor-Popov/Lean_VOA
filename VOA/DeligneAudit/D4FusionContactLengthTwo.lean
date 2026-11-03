import VOA.DeligneAudit.D4FusionContactCubic

/-! # The actual center-cube relation bounds radical-word length by two -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem piece_three_le_two (h : HighestRel R w m) (hC : (center R ^ 3) w = 0) :
    piece R w 3 ≤ piece R w 2 := by
  apply Submodule.span_le.mpr
  rintro u ⟨l, hl, rfl⟩
  by_cases htwo : l.length ≤ 2
  · exact radicalWord_mem R w l htwo
  · obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp (by omega : l.length = 3)
    exact cubic_mem_two h hC a b c

theorem piece_two_radical_invariant (h : HighestRel R w m) (hC : (center R ^ 3) w = 0)
    (i : Fin 9) : piece R w 2 ≤ (piece R w 2).comap (R.op (radIndex i) 0) := by
  intro v hv
  exact piece_three_le_two h hC (radical_op_mem R w i hv)

/-- Every actual zero-mode radical word reduces to length at most two.
This is a spanning statement derived from the center cube, not a
finite-dimensionality or normal-form hypothesis. -/
theorem radicalWord_mem_two (h : HighestRel R w m) (hC : (center R ^ 3) w = 0) :
    ∀ l : List (Fin 9), radicalWord R l w ∈ piece R w 2
  | [] => generator_mem R w 2
  | i :: l => piece_two_radical_invariant h hC i (radicalWord_mem_two h hC l)

theorem piece_le_two (h : HighestRel R w m) (hC : (center R ^ 3) w = 0) (d : ℕ) :
    piece R w d ≤ piece R w 2 := by
  apply Submodule.span_le.mpr
  rintro u ⟨l, _, rfl⟩
  exact radicalWord_mem_two h hC l

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.radicalWord_mem_two
#print axioms VOA.DeligneAudit.D4FusionContact.piece_le_two

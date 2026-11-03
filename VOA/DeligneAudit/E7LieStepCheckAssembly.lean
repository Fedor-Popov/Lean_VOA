import VOA.DeligneAudit.E7LieStepDefs

/-! Concatenation of small, independently kernel-checked propagation ranges. -/
namespace VOA.DeligneAudit.E7Lie

theorem stepOK_range_append {start left right : ℕ}
    (hL : (List.range' start left).all stepOK = true)
    (hR : (List.range' (start + left) right).all stepOK = true) :
    (List.range' start (left + right)).all stepOK = true := by
  rw [← List.range'_append_1, List.all_append, hL, hR]
  rfl

end VOA.DeligneAudit.E7Lie

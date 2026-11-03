import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 773 through 796: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_036 : (List.range' 773 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

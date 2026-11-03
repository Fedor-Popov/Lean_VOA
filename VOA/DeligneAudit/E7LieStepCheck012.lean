import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 266 through 289: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_012 : (List.range' 266 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

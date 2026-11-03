import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 531 through 554: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_024 : (List.range' 531 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

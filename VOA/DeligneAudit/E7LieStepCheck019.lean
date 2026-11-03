import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 411 through 434: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_019 : (List.range' 411 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

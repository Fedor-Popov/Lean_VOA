import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 387 through 410: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_018 : (List.range' 387 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

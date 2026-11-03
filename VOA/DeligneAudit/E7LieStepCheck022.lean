import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 483 through 506: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_022 : (List.range' 483 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

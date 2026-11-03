import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1472 through 1495: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_068 : (List.range' 1472 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

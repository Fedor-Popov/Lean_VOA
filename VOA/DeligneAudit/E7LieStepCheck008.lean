import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 193 through 193: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_008 : (List.range' 193 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

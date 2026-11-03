import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 49 through 72: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_002 : (List.range' 49 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

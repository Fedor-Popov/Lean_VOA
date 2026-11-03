import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 25 through 48: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_001 : (List.range' 25 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

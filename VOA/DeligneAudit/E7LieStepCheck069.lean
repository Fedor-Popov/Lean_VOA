import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1496 through 1519: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_069 : (List.range' 1496 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

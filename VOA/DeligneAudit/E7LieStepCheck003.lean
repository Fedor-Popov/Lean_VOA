import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 73 through 96: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_003 : (List.range' 73 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

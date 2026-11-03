import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 990 through 1013: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_046 : (List.range' 990 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

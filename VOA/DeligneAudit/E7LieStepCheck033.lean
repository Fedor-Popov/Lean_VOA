import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 724 through 747: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_033 : (List.range' 724 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

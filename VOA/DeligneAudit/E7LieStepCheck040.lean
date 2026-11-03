import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 869 through 892: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_040 : (List.range' 869 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

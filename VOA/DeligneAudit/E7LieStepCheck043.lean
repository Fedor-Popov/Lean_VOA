import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 941 through 964: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_043 : (List.range' 941 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

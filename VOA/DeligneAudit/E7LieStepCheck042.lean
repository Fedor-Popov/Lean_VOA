import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 917 through 940: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_042 : (List.range' 917 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

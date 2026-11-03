import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1351 through 1351: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_062 : (List.range' 1351 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

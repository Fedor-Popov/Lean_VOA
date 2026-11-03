import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 338 through 361: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_015 : (List.range' 338 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

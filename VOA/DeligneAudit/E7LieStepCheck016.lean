import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 362 through 385: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_016 : (List.range' 362 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

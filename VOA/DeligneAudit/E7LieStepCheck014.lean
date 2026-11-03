import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 314 through 337: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_014 : (List.range' 314 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

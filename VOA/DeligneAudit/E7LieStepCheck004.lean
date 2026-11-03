import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 97 through 120: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_004 : (List.range' 97 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

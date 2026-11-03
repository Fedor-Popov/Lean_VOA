import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 145 through 168: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_006 : (List.range' 145 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

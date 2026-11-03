import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 604 through 627: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_028 : (List.range' 604 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

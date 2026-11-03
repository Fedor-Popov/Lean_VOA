import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 652 through 675: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_030 : (List.range' 652 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

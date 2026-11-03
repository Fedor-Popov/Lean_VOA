import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 121 through 144: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_005 : (List.range' 121 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

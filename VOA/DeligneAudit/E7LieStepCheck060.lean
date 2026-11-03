import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1303 through 1326: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_060 : (List.range' 1303 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

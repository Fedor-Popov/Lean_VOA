import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1424 through 1447: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_066 : (List.range' 1424 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

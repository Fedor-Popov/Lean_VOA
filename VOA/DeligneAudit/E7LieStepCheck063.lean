import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1352 through 1375: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_063 : (List.range' 1352 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

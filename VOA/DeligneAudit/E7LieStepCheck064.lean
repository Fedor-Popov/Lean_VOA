import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1376 through 1399: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_064 : (List.range' 1376 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

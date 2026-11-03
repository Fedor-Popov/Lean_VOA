import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1086 through 1109: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_050 : (List.range' 1086 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

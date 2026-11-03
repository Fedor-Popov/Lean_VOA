import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 290 through 313: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_013 : (List.range' 290 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

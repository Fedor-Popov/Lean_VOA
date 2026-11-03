import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 628 through 651: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_029 : (List.range' 628 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

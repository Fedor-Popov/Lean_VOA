import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 218 through 241: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_010 : (List.range' 218 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

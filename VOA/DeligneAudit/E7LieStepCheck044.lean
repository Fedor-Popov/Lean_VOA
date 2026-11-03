import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 965 through 965: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_044 : (List.range' 965 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

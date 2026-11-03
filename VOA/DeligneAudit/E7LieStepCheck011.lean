import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 242 through 265: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_011 : (List.range' 242 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

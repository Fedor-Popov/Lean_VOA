import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1279 through 1302: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_059 : (List.range' 1279 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

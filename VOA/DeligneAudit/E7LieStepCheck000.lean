import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1 through 24: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_000 : (List.range' 1 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

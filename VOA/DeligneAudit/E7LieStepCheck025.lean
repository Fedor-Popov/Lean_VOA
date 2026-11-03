import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 555 through 578: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_025 : (List.range' 555 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

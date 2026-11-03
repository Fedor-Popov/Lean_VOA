import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 580 through 603: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_027 : (List.range' 580 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 748 through 771: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_034 : (List.range' 748 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

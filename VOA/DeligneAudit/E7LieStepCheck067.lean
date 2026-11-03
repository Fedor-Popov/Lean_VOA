import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1448 through 1471: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_067 : (List.range' 1448 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

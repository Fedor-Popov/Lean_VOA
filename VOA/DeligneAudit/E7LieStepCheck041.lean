import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 893 through 916: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_041 : (List.range' 893 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 194 through 217: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_009 : (List.range' 194 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

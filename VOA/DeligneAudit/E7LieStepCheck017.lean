import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 386 through 386: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_017 : (List.range' 386 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

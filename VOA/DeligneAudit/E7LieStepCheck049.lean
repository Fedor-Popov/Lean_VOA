import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1062 through 1085: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_049 : (List.range' 1062 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1014 through 1037: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_047 : (List.range' 1014 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

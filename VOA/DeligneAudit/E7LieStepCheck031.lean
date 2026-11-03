import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 676 through 699: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_031 : (List.range' 676 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

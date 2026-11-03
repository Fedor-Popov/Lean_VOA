import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1400 through 1423: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_065 : (List.range' 1400 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 821 through 844: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_038 : (List.range' 821 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

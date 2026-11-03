import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1255 through 1278: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_058 : (List.range' 1255 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

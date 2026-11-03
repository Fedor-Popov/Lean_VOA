import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1520 through 1538: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_070 : (List.range' 1520 19).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 169 through 192: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_007 : (List.range' 169 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

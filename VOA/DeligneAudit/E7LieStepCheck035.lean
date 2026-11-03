import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 772 through 772: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_035 : (List.range' 772 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

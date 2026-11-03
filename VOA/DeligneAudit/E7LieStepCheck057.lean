import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 1231 through 1254: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_057 : (List.range' 1231 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

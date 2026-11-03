import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 579 through 579: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_026 : (List.range' 579 1).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

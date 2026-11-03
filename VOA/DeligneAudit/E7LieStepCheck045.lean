import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 966 through 989: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_045 : (List.range' 966 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

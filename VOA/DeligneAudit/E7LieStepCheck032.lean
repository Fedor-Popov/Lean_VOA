import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 700 through 723: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_032 : (List.range' 700 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

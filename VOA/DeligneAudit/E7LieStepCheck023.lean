import VOA.DeligneAudit.E7LieStepDefs

/-! E₇ propagation steps 507 through 530: at most 24 per kernel check. -/
namespace VOA.DeligneAudit.E7Lie

theorem steps_small_023 : (List.range' 507 24).all stepOK = true := by
  decide +kernel

end VOA.DeligneAudit.E7Lie

import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Small certificate pieces for the guarded D4 resource repair. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_node_038_3 : nodeChecks 775 780 = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4

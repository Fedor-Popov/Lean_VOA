import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Small certificate pieces for the guarded D4 resource repair. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_anti_two_0 :
    (List.range' 0 4).all (fun d => !decide (2 < d) || antiCheck 2 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4

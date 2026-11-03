import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Small certificate pieces for the guarded D4 resource repair. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_anti_three_4 :
    (List.range' 16 4).all (fun d => !decide (3 < d) || antiCheck 3 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4

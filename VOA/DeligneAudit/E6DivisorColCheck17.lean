import VOA.DeligneAudit.E6DivisorData

/-! Fixed columns 68 through 71 of the original E6 certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_colChecks_68 :
    (List.range' 68 4).all (fun x => colCheck br colE6 78 x) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

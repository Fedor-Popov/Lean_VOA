import VOA.DeligneAudit.E6DivisorData

/-! Fixed columns 56 through 59 of the original E6 certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_colChecks_56 :
    (List.range' 56 4).all (fun x => colCheck br colE6 78 x) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

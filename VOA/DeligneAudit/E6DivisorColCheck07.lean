import VOA.DeligneAudit.E6DivisorData

/-! Fixed columns 28 through 31 of the original E6 certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_colChecks_28 :
    (List.range' 28 4).all (fun x => colCheck br colE6 78 x) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

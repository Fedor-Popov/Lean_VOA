import VOA.DeligneAudit.E6DivisorData

/-! Fixed columns 16 through 19 of the original E6 certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_colChecks_16 :
    (List.range' 16 4).all (fun x => colCheck br colE6 78 x) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

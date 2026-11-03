import VOA.DeligneAudit.E6DivisorData

/-! An unchanged fixed E6 divisor certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_U_93 : (List.range' 93 93).all UCheck = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

import VOA.DeligneAudit.E6DivisorData

/-! An unchanged fixed E6 divisor certificate. -/
namespace VOA.DeligneAudit.DeligneDivisor.E6
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_root : tab 0 = [(77, 77, 1)] ∧ par 0 = (0, false, 0, 0, 0) := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.E6

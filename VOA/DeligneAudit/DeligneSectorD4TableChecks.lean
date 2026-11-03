import VOA.DeligneAudit.DeligneSectorD4TableData

/-! The original D4 range and Jacobi checks with integer-only imports. -/
namespace VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

theorem d4_rangeCheck : rangeCheck 28 br = true := by decide +kernel

theorem d4_jacCheck : jacCheck 28 br = true := by decide +kernel


end VOA.DeligneAudit.DeligneSector.D4

#print axioms VOA.DeligneAudit.DeligneSector.D4.d4_jacCheck

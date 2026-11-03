import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry94 : entry e7T 75 88 = [(94, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry95 : entry e7T 70 90 = [(95, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry96 : entry e7T 70 91 = [(96, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry97 : entry e7T 71 92 = [(97, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry94
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry95
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry96
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry97

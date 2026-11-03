import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry0 : entry e7T 13 76 = [(0, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry1 : entry e7T 12 75 = [(1, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry2 : entry e7T 11 74 = [(2, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry3 : entry e7T 10 73 = [(3, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry0
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry1
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry2
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry3

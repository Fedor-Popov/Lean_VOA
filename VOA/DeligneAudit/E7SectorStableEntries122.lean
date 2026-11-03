import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry122 : entry e7T 71 120 = [(122, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry123 : entry e7T 70 121 = [(123, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry124 : entry e7T 75 121 = [(124, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry125 : entry e7T 71 123 = [(125, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry122
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry123
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry124
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry125

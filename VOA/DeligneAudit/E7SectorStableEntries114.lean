import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry114 : entry e7T 71 110 = [(114, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry115 : entry e7T 71 111 = [(115, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry116 : entry e7T 70 113 = [(116, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry117 : entry e7T 70 114 = [(117, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry114
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry115
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry116
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry117

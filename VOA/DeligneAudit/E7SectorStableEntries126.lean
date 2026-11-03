import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry126 : entry e7T 70 124 = [(126, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry127 : entry e7T 72 125 = [(127, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry128 : entry e7T 71 126 = [(128, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry129 : entry e7T 72 128 = [(129, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry126
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry127
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry128
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry129

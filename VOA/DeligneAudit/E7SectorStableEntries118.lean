import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry118 : entry e7T 72 114 = [(118, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry119 : entry e7T 71 116 = [(119, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry120 : entry e7T 70 118 = [(120, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry121 : entry e7T 73 118 = [(121, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry118
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry119
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry120
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry121

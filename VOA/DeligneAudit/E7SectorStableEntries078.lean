import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry78 : entry e7T 71 72 = [(78, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry79 : entry e7T 72 73 = [(79, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry80 : entry e7T 73 74 = [(80, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry81 : entry e7T 73 75 = [(81, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry78
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry79
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry80
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry81

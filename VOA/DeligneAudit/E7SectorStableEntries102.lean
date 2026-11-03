import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry102 : entry e7T 71 98 = [(102, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry103 : entry e7T 70 99 = [(103, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry104 : entry e7T 71 100 = [(104, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry105 : entry e7T 73 100 = [(105, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry102
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry103
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry104
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry105

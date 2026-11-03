import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry130 : entry e7T 73 129 = [(130, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry131 : entry e7T 74 130 = [(131, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry132 : entry e7T 76 131 = [(132, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry130
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry131
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry132

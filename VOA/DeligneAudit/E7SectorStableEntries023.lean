import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry23 : entry e7T 9 18 = [(23, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry24 : entry e7T 11 18 = [(24, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry25 : entry e7T 10 19 = [(25, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry26 : entry e7T 7 21 = [(26, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry23
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry24
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry25
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry26

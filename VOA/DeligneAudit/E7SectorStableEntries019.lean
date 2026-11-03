import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry19 : entry e7T 11 13 = [(19, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry20 : entry e7T 7 15 = [(20, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry21 : entry e7T 8 16 = [(21, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry22 : entry e7T 9 17 = [(22, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry19
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry20
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry21
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry22

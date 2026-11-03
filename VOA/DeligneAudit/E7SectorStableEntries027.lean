import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry27 : entry e7T 8 22 = [(27, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry28 : entry e7T 8 23 = [(28, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry29 : entry e7T 9 24 = [(29, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry30 : entry e7T 9 25 = [(30, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry27
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry28
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry29
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry30

import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry110 : entry e7T 74 105 = [(110, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry111 : entry e7T 70 107 = [(111, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry112 : entry e7T 70 109 = [(112, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry113 : entry e7T 72 109 = [(113, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry110
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry111
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry112
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry113

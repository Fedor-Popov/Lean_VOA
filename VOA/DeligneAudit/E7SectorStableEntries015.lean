import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry15 : entry e7T 8 9 = [(15, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry16 : entry e7T 9 10 = [(16, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry17 : entry e7T 10 11 = [(17, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry18 : entry e7T 10 12 = [(18, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry15
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry16
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry17
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry18

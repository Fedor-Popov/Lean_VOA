import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry67 : entry e7T 10 66 = [(67, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry68 : entry e7T 11 67 = [(68, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry69 : entry e7T 13 68 = [(69, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry77 : entry e7T 70 71 = [(77, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry67
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry68
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry69
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry77

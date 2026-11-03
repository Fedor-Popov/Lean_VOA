import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry4 : entry e7T 9 72 = [(4, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry5 : entry e7T 8 71 = [(5, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry6 : entry e7T 7 70 = [(6, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry14 : entry e7T 7 8 = [(14, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry4
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry5
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry6
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry14

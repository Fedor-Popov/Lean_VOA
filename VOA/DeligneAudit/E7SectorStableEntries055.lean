import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry55 : entry e7T 9 51 = [(55, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry56 : entry e7T 8 53 = [(56, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry57 : entry e7T 7 55 = [(57, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry58 : entry e7T 10 55 = [(58, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry55
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry56
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry57
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry58

import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry47 : entry e7T 11 42 = [(47, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry48 : entry e7T 7 44 = [(48, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry49 : entry e7T 7 46 = [(49, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry50 : entry e7T 9 46 = [(50, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry47
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry48
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry49
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry50

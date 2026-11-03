import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry63 : entry e7T 7 61 = [(63, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry64 : entry e7T 9 62 = [(64, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry65 : entry e7T 8 63 = [(65, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry66 : entry e7T 9 65 = [(66, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry63
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry64
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry65
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry66

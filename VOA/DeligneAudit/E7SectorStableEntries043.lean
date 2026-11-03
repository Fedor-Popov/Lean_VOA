import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry43 : entry e7T 7 39 = [(43, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry44 : entry e7T 9 39 = [(44, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry45 : entry e7T 7 41 = [(45, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry46 : entry e7T 8 42 = [(46, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry43
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry44
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry45
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry46

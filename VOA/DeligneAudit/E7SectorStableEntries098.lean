import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry98 : entry e7T 73 92 = [(98, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry99 : entry e7T 71 93 = [(99, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry100 : entry e7T 72 94 = [(100, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry101 : entry e7T 70 97 = [(101, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry98
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry99
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry100
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry101

import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry82 : entry e7T 74 76 = [(82, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry83 : entry e7T 70 78 = [(83, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry84 : entry e7T 71 79 = [(84, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry85 : entry e7T 72 80 = [(85, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry82
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry83
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry84
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry85

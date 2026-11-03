import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry86 : entry e7T 72 81 = [(86, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry87 : entry e7T 74 81 = [(87, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry88 : entry e7T 73 82 = [(88, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry89 : entry e7T 70 84 = [(89, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry86
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry87
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry88
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry89

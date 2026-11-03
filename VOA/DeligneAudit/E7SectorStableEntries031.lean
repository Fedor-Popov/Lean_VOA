import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry31 : entry e7T 12 25 = [(31, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry32 : entry e7T 7 27 = [(32, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry33 : entry e7T 7 28 = [(33, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry34 : entry e7T 8 29 = [(34, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry31
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry32
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry33
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry34

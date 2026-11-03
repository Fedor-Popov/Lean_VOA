import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry59 : entry e7T 8 57 = [(59, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry60 : entry e7T 7 58 = [(60, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry61 : entry e7T 12 58 = [(61, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry62 : entry e7T 8 60 = [(62, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry59
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry60
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry61
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry62

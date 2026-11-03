import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry39 : entry e7T 8 35 = [(39, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry40 : entry e7T 7 36 = [(40, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry41 : entry e7T 8 37 = [(41, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry42 : entry e7T 10 37 = [(42, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry39
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry40
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry41
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry42

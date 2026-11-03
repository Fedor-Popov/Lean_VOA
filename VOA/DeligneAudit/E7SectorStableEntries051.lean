import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry51 : entry e7T 8 47 = [(51, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry52 : entry e7T 8 48 = [(52, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry53 : entry e7T 7 50 = [(53, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry54 : entry e7T 7 51 = [(54, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry51
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry52
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry53
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry54

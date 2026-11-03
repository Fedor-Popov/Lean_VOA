import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry35 : entry e7T 10 29 = [(35, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry36 : entry e7T 8 30 = [(36, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry37 : entry e7T 9 31 = [(37, (1 : ℤ))] := by
  decide +kernel

theorem stable_entry38 : entry e7T 7 34 = [(38, (1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry35
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry36
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry37
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry38

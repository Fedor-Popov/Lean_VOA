import VOA.DeligneAudit.E7SectorIntegerTable

/-! Exact integer bracket entries for E7 stability propagation.
These small certificates retain the original singleton table equalities. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.AffineGeneral.SCLie

theorem stable_entry90 : entry e7T 71 85 = [(90, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry91 : entry e7T 71 86 = [(91, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry92 : entry e7T 72 87 = [(92, (-1 : ℤ))] := by
  decide +kernel

theorem stable_entry93 : entry e7T 72 88 = [(93, (-1 : ℤ))] := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry90
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry91
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry92
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.stable_entry93

import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed E7 structure-table comparison for rows 84 through 86.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink084_087 : (List.range' 84 3).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink084_087

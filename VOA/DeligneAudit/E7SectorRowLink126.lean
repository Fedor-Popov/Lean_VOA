import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed E7 structure-table comparison for rows 126 through 128.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink126_129 : (List.range' 126 3).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink126_129

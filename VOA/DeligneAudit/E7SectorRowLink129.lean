import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed E7 structure-table comparison for rows 129 through 129.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink129_130 : (List.range' 129 1).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink129_130

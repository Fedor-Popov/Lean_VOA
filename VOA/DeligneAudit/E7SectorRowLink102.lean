import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed E7 structure-table comparison for rows 102 through 104.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink102_105 : (List.range' 102 3).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink102_105

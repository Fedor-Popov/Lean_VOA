import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed E7 structure-table comparison for rows 66 through 68.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink066_069 : (List.range' 66 3).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink066_069

import VOA.DeligneAudit.E7SectorLinkDefs

/-! Fixed three-row E7 structure-table comparison at the highest indices.
The checked predicate is the unchanged original whole-row comparison. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem rowLink130_133 : (List.range' 130 3).all rowLinkOK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink130_133

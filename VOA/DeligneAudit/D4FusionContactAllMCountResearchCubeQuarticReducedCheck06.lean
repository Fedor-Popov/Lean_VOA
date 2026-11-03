import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedData

/-! This fixed finite row uses ordinary unbounded jets; only integer
coefficient cancellation is checked. No rank is computed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

-- The fixed row-list recursion exceeds the default depth; memory remains guarded.
set_option maxRecDepth 8000 in
theorem certificate06 : QuarticReducedRows.fastCollect (residualRow 6) = [] := by
  decide +kernel

#print axioms certificate06
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

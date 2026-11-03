import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedData

/-! This fixed finite row uses ordinary unbounded jets; only integer
coefficient cancellation is checked. No rank is computed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

-- The fixed row-list recursion exceeds the default depth; memory remains guarded.
set_option maxRecDepth 8000 in
theorem certificate15 : QuarticReducedRows.fastCollect (residualRow 15) = [] := by
  decide +kernel

#print axioms certificate15
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

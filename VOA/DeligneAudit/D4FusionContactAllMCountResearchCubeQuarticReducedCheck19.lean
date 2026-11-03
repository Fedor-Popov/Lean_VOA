import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedData

/-! This fixed finite row uses ordinary unbounded jets; only integer
coefficient cancellation is checked. No rank is computed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

-- The fixed row-list recursion exceeds the default depth; memory remains guarded.
set_option maxRecDepth 8000 in
theorem certificate19 : QuarticReducedRows.fastCollect (residualRow 19) = [] := by
  decide +kernel

#print axioms certificate19
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedData

/-! This fixed finite row uses ordinary unbounded jets; only integer
coefficient cancellation is checked. No rank is computed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

-- The fixed row-list recursion exceeds the default depth; memory remains guarded.
set_option maxRecDepth 8000 in
theorem certificate01 : QuarticReducedRows.fastCollect (residualRow 1) = [] := by
  decide +kernel

#print axioms certificate01
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

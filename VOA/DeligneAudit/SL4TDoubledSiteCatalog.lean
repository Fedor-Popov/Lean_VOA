import VOA.DeligneAudit.SL4TDoubledSiteTransport

/-! Ordered catalog fibers after removing the two distinguished middle sites. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The surviving index order is exactly the doubled-site catalog order. -/
theorem doubledSitePairs_indexed :
    doubledSitePairs = (List.finRange 10).map doubledSitePairStates := by
  decide

/-- Removing a middle site leaves the outer label unchanged. -/
theorem mixedBNext_outer (q : MixedParams) (s : MixedBState) :
    (mixedBNext q s).A = q.A := by cases s <;> rfl

/-- Removing a middle site decreases the middle label by one. -/
theorem mixedBNext_middle (q : MixedParams) (s : MixedBState) :
    (mixedBNext q s).B = q.B - 1 := by cases s <;> rfl

/-- The inner block has zero outer sites and two fewer middle sites. -/
theorem doubledSiteReducedParams_labels (q : MixedParams) (k : Fin 10) :
    (doubledSiteReducedParams q k).A = q.A ∧
      (doubledSiteReducedParams q k).B = q.B - 2 := by
  simp only [doubledSiteReducedParams, mixedBNext_outer, mixedBNext_middle]
  exact ⟨trivial, by omega⟩

/-- Validity after both removals implies validity after the first removal. -/
theorem doubledSiteReducedParams_first_valid (q : MixedParams) (k : Fin 10)
    (h : MixedValid (doubledSiteReducedParams q k)) :
    MixedValid (mixedBNext q (doubledSitePairStates k).1) := by
  have hv := mixedBPrevious_valid _ h (doubledSitePairStates k).2
  simpa only [doubledSiteReducedParams, mixedBPrevious_next] using hv

/-- The catalog count shift is precisely the shortened-cutoff shift of its pair. -/
theorem doubledSitePairStates_level (k : Fin 10) :
    doubledSiteDoubleCount (doubledSitePairStates k) +
      doubledSiteTripleCount (doubledSitePairStates k) = doubledPairLevelShift k := by
  fin_cases k <;> decide

/-- Taking the fiber of an inserted pair removes the same two states from the parameters. -/
theorem doubledSitePrepend_fiber (q : MixedParams) (k : Fin 10)
    (l : List (MixedParams × MixedCellCounts)) :
    mixedCatalogFiber q (l.map (doubledSitePrepend (doubledSitePairStates k))) =
      (mixedCatalogFiber (doubledSiteReducedParams q k) l).map
        (mixedCellShift (doubledSiteDoubleCount (doubledSitePairStates k))
          (doubledSiteTripleCount (doubledSitePairStates k))) := by
  apply mixedCatalogFiber_map q l
    (fun x => mixedBPrevious (mixedBPrevious x (doubledSitePairStates k).2)
      (doubledSitePairStates k).1)
    (fun x => doubledSiteReducedParams x k)
    (mixedCellShift (doubledSiteDoubleCount (doubledSitePairStates k))
      (doubledSiteTripleCount (doubledSitePairStates k)))
  · intro x
    simp only [doubledSiteReducedParams, mixedBPrevious_next]
  · intro x
    simp only [doubledSiteReducedParams, mixedBNext_previous]

/-- The ordered doubled-site fiber is the concatenation of the ten inner block fibers. -/
theorem doubledSiteCellCatalog_levels (q : MixedParams) (hA : q.A = 0)
    (hB : 2 ≤ q.B) :
    (mixedCatalogFiber q (doubledSiteCellCatalog (q.B.toNat - 2))).map mixedCellLevel =
      (List.finRange 10).flatMap (fun k =>
        (mixedCellLevels (q.B.toNat - 2) (doubledSiteReducedParams q k)).map
          (fun n => n + doubledPairLevelShift k)) := by
  rw [doubledSiteCellCatalog, doubledSitePairs_indexed, List.flatMap_map,
    mixedCatalogFiber_flatMap, List.map_flatMap]
  congr 1
  funext k
  rw [doubledSitePrepend_fiber, mixedCellCatalog_fiber 0 (q.B.toNat - 2) _
    (by rw [(doubledSiteReducedParams_labels q k).1, hA]; rfl)
    (by rw [(doubledSiteReducedParams_labels q k).2]; omega)]
  simp only [Nat.zero_add, mixedCellLevels, List.map_map, Function.comp_def,
    mixedCellShift_level, doubledSitePairStates_level]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doubledSitePairs_indexed
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_outer
#print axioms VOA.DeligneAudit.SL4T.mixedBNext_middle
#print axioms VOA.DeligneAudit.SL4T.doubledSiteReducedParams_labels
#print axioms VOA.DeligneAudit.SL4T.doubledSiteReducedParams_first_valid
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairStates_level
#print axioms VOA.DeligneAudit.SL4T.doubledSitePrepend_fiber
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_levels

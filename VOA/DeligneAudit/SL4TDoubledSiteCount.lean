import VOA.DeligneAudit.SL4TMixedBlockTotal

/-! The weighted cell count for one doubled middle-weight site and arbitrary remaining sites. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.CVsl2

/-- Surviving ordered pairs, with the second site in reverse order within each first site. -/
def doubledSitePairs : List (MixedBState × MixedBState) :=
  [(.s1, .s1), (.s2, .s2), (.s2, .s1), (.d1, .d1), (.d1, .s2),
    (.d1, .s1), (.d2, .d2), (.d2, .d1), (.d2, .s2), (.d2, .s1)]

/-- The number of roots in the retained characteristic alphabet at the doubled site. -/
def doubledSiteRootCount (p : MixedBState × MixedBState) : ℕ :=
  mixedBZeroRoots p.1 + mixedBZeroRoots p.2

/-- A doubled pair contributes a double precisely when it contains one retained root. -/
def doubledSiteDoubleCount (p : MixedBState × MixedBState) : ℕ :=
  if doubledSiteRootCount p = 1 then 1 else 0

/-- A doubled pair contributes a triple precisely when it contains two retained roots. -/
def doubledSiteTripleCount (p : MixedBState × MixedBState) : ℕ :=
  if doubledSiteRootCount p = 2 then 1 else 0

/-- Reinsert both sites, keeping the block parameters and the double/triple contribution. -/
def doubledSitePrepend (p : MixedBState × MixedBState)
    (c : MixedParams × MixedCellCounts) : MixedParams × MixedCellCounts :=
  (mixedBPrevious (mixedBPrevious c.1 p.2) p.1,
    mixedCellShift (doubledSiteDoubleCount p) (doubledSiteTripleCount p) c.2)

/-- Every surviving doubled pair followed by an arbitrary word of ordinary middle sites. -/
def doubledSiteCellCatalog (n : ℕ) : List (MixedParams × MixedCellCounts) :=
  doubledSitePairs.flatMap (fun p => (mixedCellCatalog 0 n).map (doubledSitePrepend p))

/-- The roots and cutoff increments agree with the double/triple counts. -/
theorem doubledSite_counts (p : MixedBState × MixedBState) :
    doubledSiteDoubleCount p + 2 * doubledSiteTripleCount p = doubledSiteRootCount p ∧
      doubledSiteDoubleCount p + doubledSiteTripleCount p = min (doubledSiteRootCount p) 1 := by
  rcases p with ⟨i, j⟩
  cases i <;> cases j <;>
    norm_num [doubledSiteDoubleCount, doubledSiteTripleCount, doubledSiteRootCount,
      mixedBZeroRoots]

/-- A pair's contribution multiplies the mass of every following catalog. -/
theorem mixedCatalogMass_doubledSitePrepend (p : MixedBState × MixedBState)
    (l : List (MixedParams × MixedCellCounts)) :
    mixedCatalogMass (l.map (doubledSitePrepend p)) =
      (3 ^ doubledSiteTripleCount p * 2 ^ doubledSiteDoubleCount p) * mixedCatalogMass l := by
  simp [mixedCatalogMass, doubledSitePrepend, List.map_map, Function.comp_def,
    mixedCellContribution_shift, List.sum_map_mul_left]

/-- The complete doubled-site catalog has mass twenty times six per remaining site. -/
theorem doubledSiteCellCatalog_mass (n : ℕ) :
    mixedCatalogMass (doubledSiteCellCatalog n) = 20 * 6 ^ n := by
  rw [doubledSiteCellCatalog, mixedCatalogMass_flatMap]
  simp [doubledSitePairs, mixedCatalogMass_doubledSitePrepend, mixedCellCatalog_mass,
    doubledSiteTripleCount, doubledSiteDoubleCount, doubledSiteRootCount, mixedBZeroRoots]
  ring

/-- Each catalog entry belongs to a valid block with exactly two extra middle sites. -/
theorem doubledSiteCellCatalog_valid (n : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ doubledSiteCellCatalog n) :
    MixedValid c.1 ∧ c.1.A = 0 ∧ c.1.B = n + 2 := by
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hv, hA, hB⟩ := mixedCellCatalog_valid 0 n d hd
  refine ⟨mixedBPrevious_valid _ (mixedBPrevious_valid _ hv p.2) p.1, ?_, ?_⟩
  · rcases p with ⟨i, j⟩
    cases i <;> cases j <;> simp [doubledSitePrepend, mixedBPrevious, hA]
  · rcases p with ⟨i, j⟩
    cases i <;> cases j <;> simp [doubledSitePrepend, mixedBPrevious, hB] <;> ring

/-- Catalog weights are determined by their double and triple counts. -/
theorem mixedCellCatalog_count_weight (A B : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ mixedCellCatalog A B) : mixedWeight c.1 = (c.2.1 : ℤ) + 2 * c.2.2 := by
  obtain ⟨hv, hA, hB⟩ := mixedCellCatalog_valid A B c hc
  have hf : c.2 ∈ mixedCatalogFiber c.1 (mixedCellCatalog A B) := by
    apply List.mem_filterMap.mpr
    exact ⟨c, hc, by simp⟩
  rw [mixedCellCatalog_fiber A B c.1 hA hB] at hf
  exact mixedCellData_weight (A + B) c.1 hv (by omega) c.2 hf

/-- Inserting both site roots gives the correct highest weight of its new block. -/
theorem doubledSitePrepend_weight (p : MixedBState × MixedBState)
    (c : MixedParams × MixedCellCounts)
    (hc : mixedWeight c.1 = (c.2.1 : ℤ) + 2 * c.2.2) :
    mixedWeight (doubledSitePrepend p c).1 =
      ((doubledSitePrepend p c).2.1 : ℤ) + 2 * (doubledSitePrepend p c).2.2 := by
  have hp : (doubledSiteDoubleCount p : ℤ) + 2 * doubledSiteTripleCount p =
      doubledSiteRootCount p := by exact_mod_cast (doubledSite_counts p).1
  have hs (q : MixedParams) (s : MixedBState) :
      mixedWeight (mixedBPrevious q s) = mixedWeight q + mixedBZeroRoots s := by
    have he := mixedBNext_weight (mixedBPrevious q s) s
    simpa only [mixedBNext_previous] using he
  simp only [doubledSitePrepend, mixedCellShift, hs, hc, Nat.cast_add]
  have hz : (doubledSiteRootCount p : ℤ) = mixedBZeroRoots p.1 + mixedBZeroRoots p.2 := by
    simp [doubledSiteRootCount]
  rw [hz] at hp
  linarith

/-- The balanced rank-one product is exactly the double/triple cell contribution. -/
theorem balancedProduct_cellContribution (c : MixedCellCounts) :
    ((bal (c.1 + 2 * c.2) (mixedCellLevel c)).map (· + 1)).prod =
      mixedCellContribution c := by
  unfold mixedCellLevel mixedCellContribution
  by_cases hz : c.1 + c.2 = 0
  · have h₁ : c.1 = 0 := by omega
    have h₂ : c.2 = 0 := by omega
    simp [h₁, h₂, bal]
  · rw [bal_prod_two (by omega) (by omega) (by omega),
      show c.1 + 2 * c.2 - (c.1 + c.2) = c.2 by omega,
      show 2 * (c.1 + c.2) - (c.1 + 2 * c.2) = c.1 by omega]

/-- Every doubled-site catalog entry has the advertised balanced contribution. -/
theorem doubledSiteCellCatalog_balanced (n : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ doubledSiteCellCatalog n) :
    ((bal (mixedWeight c.1).toNat (mixedCellLevel c.2)).map (· + 1)).prod =
      mixedCellContribution c.2 := by
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hw := doubledSitePrepend_weight p d (mixedCellCatalog_count_weight 0 n d hd)
  have hn : (mixedWeight (doubledSitePrepend p d).1).toNat =
      (doubledSitePrepend p d).2.1 + 2 * (doubledSitePrepend p d).2.2 := by omega
  rw [hn]
  exact balancedProduct_cellContribution _

/-- The sum of balanced bounds over every doubled-site block is the required all-site count. -/
theorem doubledSite_balanced_sum (B : ℕ) :
    ((doubledSiteCellCatalog (B - 2)).map (fun c =>
      ((bal (mixedWeight c.1).toNat (mixedCellLevel c.2)).map (· + 1)).prod)).sum =
        20 * 6 ^ (B - 2) := by
  rw [← doubledSiteCellCatalog_mass (B - 2)]
  unfold mixedCatalogMass
  congr 1
  apply List.map_congr_left
  exact doubledSiteCellCatalog_balanced (B - 2)

/-- The weighted doubled-site cells belonging to one specified mixed block. -/
def doubledSiteBlockBound (B : ℕ) (q : MixedParams) : ℕ :=
  ((mixedCatalogFiber q (doubledSiteCellCatalog (B - 2))).map mixedCellContribution).sum

/-- Partitioning the doubled-site catalog by every valid block preserves its total mass. -/
theorem doubledSiteBlockBound_sum_all_valid (B : ℕ) (hB : 2 ≤ B) :
    (∑ q ∈ mixedValidBlocks 0 B, doubledSiteBlockBound B q) = 20 * 6 ^ (B - 2) := by
  rw [← doubledSiteCellCatalog_mass (B - 2)]
  apply mixedCatalogFiber_mass_sum
  intro c hc
  obtain ⟨hv, hA, hsites⟩ := doubledSiteCellCatalog_valid (B - 2) c hc
  apply (mem_mixedValidBlocks 0 B c.1).mpr
  exact ⟨hv, hA, by rw [hsites]; omega⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doubledSite_counts
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_doubledSitePrepend
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_mass
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_count_weight
#print axioms VOA.DeligneAudit.SL4T.doubledSitePrepend_weight
#print axioms VOA.DeligneAudit.SL4T.balancedProduct_cellContribution
#print axioms VOA.DeligneAudit.SL4T.doubledSiteCellCatalog_balanced
#print axioms VOA.DeligneAudit.SL4T.doubledSite_balanced_sum
#print axioms VOA.DeligneAudit.SL4T.doubledSiteBlockBound_sum_all_valid

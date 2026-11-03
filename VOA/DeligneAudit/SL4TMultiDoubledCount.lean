import VOA.DeligneAudit.SL4TDoubledSiteCount

/-! The weighted word count with arbitrary doubled and simple middle-weight sites. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.CVsl2

/-- The word catalog with `k` doubled sites followed by `n` simple sites. -/
def multiDoubledSiteCellCatalog : ℕ → ℕ → List (MixedParams × MixedCellCounts)
  | 0, n => mixedCellCatalog 0 n
  | k + 1, n => doubledSitePairs.flatMap
      (fun p => (multiDoubledSiteCellCatalog k n).map (doubledSitePrepend p))

/-- Each doubled site contributes twenty and each simple site contributes six. -/
theorem multiDoubledSiteCellCatalog_mass (k n : ℕ) :
    mixedCatalogMass (multiDoubledSiteCellCatalog k n) = 20 ^ k * 6 ^ n := by
  induction k with
  | zero => simp [multiDoubledSiteCellCatalog, mixedCellCatalog_mass]
  | succ k ih =>
      rw [multiDoubledSiteCellCatalog, mixedCatalogMass_flatMap]
      simp [doubledSitePairs, mixedCatalogMass_doubledSitePrepend, ih,
        doubledSiteTripleCount, doubledSiteDoubleCount, doubledSiteRootCount,
        mixedBZeroRoots, pow_succ]
      ring

/-- All catalog words have valid content and exactly the prescribed number of roots. -/
theorem multiDoubledSiteCellCatalog_valid (k n : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ multiDoubledSiteCellCatalog k n) :
    MixedValid c.1 ∧ c.1.A = 0 ∧ c.1.B = n + 2 * k := by
  induction k generalizing c with
  | zero => simpa [multiDoubledSiteCellCatalog] using mixedCellCatalog_valid 0 n c hc
  | succ k ih =>
      obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hv, hA, hB⟩ := ih d hd
      refine ⟨mixedBPrevious_valid _ (mixedBPrevious_valid _ hv p.2) p.1, ?_, ?_⟩
      · rcases p with ⟨i, j⟩
        cases i <;> cases j <;> simp [doubledSitePrepend, mixedBPrevious, hA]
      · rcases p with ⟨i, j⟩
        cases i <;> cases j <;>
          simp [doubledSitePrepend, mixedBPrevious, hB, Nat.cast_add] <;> ring

/-- The retained root count is one per single contribution and two per triple. -/
theorem multiDoubledSiteCellCatalog_weight (k n : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ multiDoubledSiteCellCatalog k n) :
    mixedWeight c.1 = (c.2.1 : ℤ) + 2 * c.2.2 := by
  induction k generalizing c with
  | zero => exact mixedCellCatalog_count_weight 0 n c hc
  | succ k ih =>
      obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact doubledSitePrepend_weight p d (ih d hd)

/-- The balanced rank-one bound equals the product of the local word contributions. -/
theorem multiDoubledSiteCellCatalog_balanced (k n : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ multiDoubledSiteCellCatalog k n) :
    ((bal (mixedWeight c.1).toNat (mixedCellLevel c.2)).map (· + 1)).prod =
      mixedCellContribution c.2 := by
  have hw := multiDoubledSiteCellCatalog_weight k n c hc
  have hn : (mixedWeight c.1).toNat = c.2.1 + 2 * c.2.2 := by omega
  rw [hn]
  exact balancedProduct_cellContribution _

/-- Summing the balanced bounds over all words gives the uniform multi-site count. -/
theorem multiDoubledSite_balanced_sum (k n : ℕ) :
    ((multiDoubledSiteCellCatalog k n).map (fun c =>
      ((bal (mixedWeight c.1).toNat (mixedCellLevel c.2)).map (· + 1)).prod)).sum =
        20 ^ k * 6 ^ n := by
  rw [← multiDoubledSiteCellCatalog_mass k n]
  unfold mixedCatalogMass
  congr 1
  apply List.map_congr_left
  exact multiDoubledSiteCellCatalog_balanced k n

/-- The sum of word contributions with prescribed multiplicity-ring content. -/
def multiDoubledSiteBlockBound (B k : ℕ) (q : MixedParams) : ℕ :=
  ((mixedCatalogFiber q (multiDoubledSiteCellCatalog k (B - 2 * k))).map
    mixedCellContribution).sum

/-- Partitioning all words by their valid blocks preserves the weighted count. -/
theorem multiDoubledSiteBlockBound_sum_all_valid (B k : ℕ) (hk : 2 * k ≤ B) :
    (∑ q ∈ mixedValidBlocks 0 B, multiDoubledSiteBlockBound B k q) =
      20 ^ k * 6 ^ (B - 2 * k) := by
  rw [← multiDoubledSiteCellCatalog_mass k (B - 2 * k)]
  apply mixedCatalogFiber_mass_sum
  intro c hc
  obtain ⟨hv, hA, hB⟩ := multiDoubledSiteCellCatalog_valid k (B - 2 * k) c hc
  apply (mem_mixedValidBlocks 0 B c.1).mpr
  exact ⟨hv, hA, by rw [hB]; omega⟩

/-- The balanced bounds within one block equal its weighted word count. -/
theorem multiDoubledSiteFiber_balanced_sum (B k : ℕ) (q : MixedParams) :
    let ns := (mixedCatalogFiber q
      (multiDoubledSiteCellCatalog k (B - 2 * k))).map mixedCellLevel
    (∑ i ∈ Finset.range ns.length,
      ((bal (mixedWeight q).toNat (ns.getD i 0)).map (· + 1)).prod) =
        multiDoubledSiteBlockBound B k q := by
  dsimp only
  rw [list_sum_getD _ (fun n => ((bal (mixedWeight q).toNat n).map (· + 1)).prod)]
  unfold multiDoubledSiteBlockBound
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  obtain ⟨d, hd, he⟩ := List.mem_filterMap.mp hc
  by_cases hq : d.1 = q
  · simp only [hq, if_true, Option.some.injEq] at he
    rw [← he, ← hq]
    exact multiDoubledSiteCellCatalog_balanced k (B - 2 * k) d hd
  · simp [hq] at he

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_mass
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_weight
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_balanced
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSite_balanced_sum
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteBlockBound
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteBlockBound_sum_all_valid
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteFiber_balanced_sum

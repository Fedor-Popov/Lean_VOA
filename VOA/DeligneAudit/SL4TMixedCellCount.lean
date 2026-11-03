import VOA.DeligneAudit.SL4TMixedCellPartition

/-! # The weighted mixed-cell count with site factors fifteen and six -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Total dimension contribution of an ordered catalog, retaining repeated cell counts. -/
def mixedCatalogMass (l : List (MixedParams × MixedCellCounts)) : ℕ :=
  (l.map (fun c => mixedCellContribution c.2)).sum

theorem mixedCellContribution_shift (d t : ℕ) (c : MixedCellCounts) :
    mixedCellContribution (mixedCellShift d t c) =
      (3 ^ t * 2 ^ d) * mixedCellContribution c := by
  simp only [mixedCellContribution, mixedCellShift, pow_add]
  ring

theorem mixedCatalogMass_flatMap {ι : Type*} (l : List ι)
    (f : ι → List (MixedParams × MixedCellCounts)) :
    mixedCatalogMass (l.flatMap f) = (l.map (fun i => mixedCatalogMass (f i))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simpa [mixedCatalogMass, List.sum_append] using
        (congrArg (fun n => mixedCatalogMass (f a) + n) ih)

theorem mixedCatalogMass_b_prepend (s : MixedBState)
    (l : List (MixedParams × MixedCellCounts)) :
    mixedCatalogMass (l.map (mixedBPrepend s)) =
      2 ^ mixedBZeroRoots s * mixedCatalogMass l := by
  simp [mixedCatalogMass, mixedBPrepend, List.map_map, Function.comp_def,
    mixedCellContribution_shift, List.sum_map_mul_left]

theorem mixedCatalogMass_a_prepend (s : MixedAState)
    (l : List (MixedParams × MixedCellCounts)) :
    mixedCatalogMass (l.map (mixedAPrepend s)) =
      (3 ^ mixedATripleCount s * 2 ^ mixedADoubleCount s) * mixedCatalogMass l := by
  simp [mixedCatalogMass, mixedAPrepend, List.map_map, Function.comp_def,
    mixedCellContribution_shift, List.sum_map_mul_left]

/-- Each unrestricted a-site multiplies the total cell contribution by fifteen. -/
theorem mixedACellCatalog_mass (A : ℕ) : mixedCatalogMass (mixedACellCatalog A) = 15 ^ A := by
  induction A with
  | zero => simp [mixedACellCatalog, mixedCatalogMass, mixedCellContribution]
  | succ A ih =>
      rw [mixedACellCatalog, mixedCatalogMass_flatMap]
      simp [List.range_succ, mixedCatalogMass_a_prepend, mixedAOrder,
        mixedATripleCount, mixedADoubleCount, mixedAZeroRoots, ih, pow_succ]
      ring

/-- The weighted sum of all mixed-site words is fifteen to the a-sites times six to the b-sites. -/
theorem mixedCellCatalog_mass (A B : ℕ) :
    mixedCatalogMass (mixedCellCatalog A B) = 15 ^ A * 6 ^ B := by
  induction B with
  | zero => simpa [mixedCellCatalog] using mixedACellCatalog_mass A
  | succ B ih =>
      rw [mixedCellCatalog, mixedCatalogMass_flatMap]
      simp [List.range_succ, mixedCatalogMass_b_prepend, mixedBOrder,
        mixedBZeroRoots, ih, pow_succ]
      ring

/-- Summing the contributions of all fibers partitions the catalog's contribution. -/
theorem mixedCatalogFiber_mass_sum (l : List (MixedParams × MixedCellCounts))
    (S : Finset MixedParams) (hS : ∀ c ∈ l, c.1 ∈ S) :
    (∑ q ∈ S, ((mixedCatalogFiber q l).map mixedCellContribution).sum) =
      mixedCatalogMass l := by
  induction l with
  | nil => simp [mixedCatalogFiber, mixedCatalogMass]
  | cons c l ih =>
      have hc : c.1 ∈ S := hS c (by simp)
      have ht : ∀ d ∈ l, d.1 ∈ S := fun d hd => hS d (List.mem_cons_of_mem _ hd)
      calc
        _ = ∑ q ∈ S, ((if c.1 = q then mixedCellContribution c.2 else 0) +
            ((mixedCatalogFiber q l).map mixedCellContribution).sum) := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases he : c.1 = q <;> simp [mixedCatalogFiber, he]
        _ = mixedCellContribution c.2 +
            ∑ q ∈ S, ((mixedCatalogFiber q l).map mixedCellContribution).sum := by
          rw [Finset.sum_add_distrib]
          simp [eq_comm, hc]
        _ = mixedCatalogMass (c :: l) := by rw [ih ht]; rfl

/-- The represented blocks exhaust the weighted cell sum; omitted blocks contribute zero. -/
theorem mixedBlockBound_total (A B : ℕ) :
    (∑ q ∈ mixedRepresentedBlocks A B, mixedBlockBound q) = 15 ^ A * 6 ^ B := by
  rw [← mixedCellCatalog_mass A B]
  calc
    _ = ∑ q ∈ mixedRepresentedBlocks A B,
        ((mixedCatalogFiber q (mixedCellCatalog A B)).map mixedCellContribution).sum := by
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨_, hA, hB⟩ := mixedRepresentedBlocks_valid A B q hq
      rw [mixedCellCatalog_fiber A B q hA hB]
      have hn : (q.A + q.B).toNat = A + B := by omega
      simp only [mixedBlockBound, hn]
    _ = _ := mixedCatalogFiber_mass_sum _ _ (by
      intro c hc
      simp only [mixedRepresentedBlocks, List.mem_toFinset, List.mem_map]
      exact ⟨c, hc, rfl⟩)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedCellContribution_shift
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_flatMap
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_b_prepend
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogMass_a_prepend
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_mass
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_mass
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_mass_sum
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_total

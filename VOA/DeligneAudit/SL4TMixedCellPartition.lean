import VOA.DeligneAudit.SL4TMixedCellCatalog

/-! # Partition of the mixed-site words into parameter-block cells -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

theorem mixedValid_zero_params (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : q.B = 0) : q = mixedEmptyParams := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  cases q
  dsimp [mixedEmptyParams] at *
  congr <;> omega

/-- The a-word fiber is exactly the recursively ordered cell list of its block. -/
theorem mixedACellCatalog_fiber (A : ℕ) (q : MixedParams) (hA : q.A = A) (hB : q.B = 0) :
    mixedCatalogFiber q (mixedACellCatalog A) = mixedCellData A q := by
  induction A generalizing q with
  | zero =>
      by_cases hq : MixedValid q
      · have he := mixedValid_zero_params q hq hA hB
        subst q
        simp [mixedCatalogFiber, mixedACellCatalog, mixedCellData, hq]
      · rw [mixedCellData_invalid _ _ hq]
        exact mixedCatalogFiber_nil_of_invalid q hq _
          (fun c hc => (mixedACellCatalog_valid 0 c hc).1)
  | succ A ih =>
      by_cases hq : MixedValid q
      · have hB' : ¬ 1 ≤ q.B := by omega
        rw [mixedACellCatalog, mixedCatalogFiber_flatMap, mixedCellData,
          if_pos hq, if_neg hB']
        congr 1
        funext i
        split_ifs with hi
        · change mixedCatalogFiber q
            ((mixedACellCatalog A).map (fun c =>
              (mixedAPrevious c.1 (mixedAOrder ⟨i, hi⟩),
                mixedCellShift (mixedADoubleCount (mixedAOrder ⟨i, hi⟩))
                  (mixedATripleCount (mixedAOrder ⟨i, hi⟩)) c.2))) = _
          rw [mixedCatalogFiber_map q (mixedACellCatalog A)
            (fun x => mixedAPrevious x (mixedAOrder ⟨i, hi⟩))
            (fun x => mixedANext x (mixedAOrder ⟨i, hi⟩))
            (mixedCellShift (mixedADoubleCount (mixedAOrder ⟨i, hi⟩))
              (mixedATripleCount (mixedAOrder ⟨i, hi⟩)))
            (fun x => mixedAPrevious_next x _) (fun x => mixedANext_previous x _)]
          rw [ih _ (by simp [mixedANext, hA, Nat.cast_add, Nat.cast_one])
            (by simpa [mixedANext] using hB)]
        · rfl
      · rw [mixedCellData_invalid _ _ hq]
        exact mixedCatalogFiber_nil_of_invalid q hq _
          (fun c hc => (mixedACellCatalog_valid (A + 1) c hc).1)

/-- Every mixed-site word belongs to its unique block, and every recursive cell occurs. -/
theorem mixedCellCatalog_fiber (A B : ℕ) (q : MixedParams) (hA : q.A = A) (hB : q.B = B) :
    mixedCatalogFiber q (mixedCellCatalog A B) = mixedCellData (A + B) q := by
  induction B generalizing q with
  | zero => simpa [mixedCellCatalog] using mixedACellCatalog_fiber A q hA hB
  | succ B ih =>
      by_cases hq : MixedValid q
      · have hB' : 1 ≤ q.B := by omega
        rw [mixedCellCatalog, mixedCatalogFiber_flatMap, Nat.add_succ, mixedCellData,
          if_pos hq, if_pos hB']
        congr 1
        funext i
        split_ifs with hi
        · change mixedCatalogFiber q
            ((mixedCellCatalog A B).map (fun c =>
              (mixedBPrevious c.1 (mixedBOrder ⟨i, hi⟩),
                mixedCellShift (mixedBZeroRoots (mixedBOrder ⟨i, hi⟩)) 0 c.2))) = _
          rw [mixedCatalogFiber_map q (mixedCellCatalog A B)
            (fun x => mixedBPrevious x (mixedBOrder ⟨i, hi⟩))
            (fun x => mixedBNext x (mixedBOrder ⟨i, hi⟩))
            (mixedCellShift (mixedBZeroRoots (mixedBOrder ⟨i, hi⟩)) 0)
            (fun x => mixedBPrevious_next x _) (fun x => mixedBNext_previous x _)]
          rw [ih _ (by cases mixedBOrder ⟨i, hi⟩ <;> simpa [mixedBNext] using hA)
            (by cases mixedBOrder ⟨i, hi⟩ <;>
              simp [mixedBNext, hB, Nat.cast_add, Nat.cast_one])]
        · rfl
      · rw [mixedCellData_invalid _ _ hq]
        exact mixedCatalogFiber_nil_of_invalid q hq _
          (fun c hc => (mixedCellCatalog_valid A (B + 1) c hc).1)

/-- Exactly the blocks represented by site words; all other blocks have zero contribution. -/
def mixedRepresentedBlocks (A B : ℕ) : Finset MixedParams :=
  ((mixedCellCatalog A B).map Prod.fst).toFinset

theorem mixedRepresentedBlocks_valid (A B : ℕ) (q : MixedParams)
    (hq : q ∈ mixedRepresentedBlocks A B) : MixedValid q ∧ q.A = A ∧ q.B = B := by
  simp only [mixedRepresentedBlocks, List.mem_toFinset, List.mem_map] at hq
  obtain ⟨c, hc, he⟩ := hq
  simpa only [he] using mixedCellCatalog_valid A B c hc

/-- A block omitted from the word catalog contributes no cells. -/
theorem mixedBlockBound_zero_of_unrepresented (A B : ℕ) (q : MixedParams)
    (hA : q.A = A) (hB : q.B = B) (hq : q ∉ mixedRepresentedBlocks A B) :
    mixedBlockBound q = 0 := by
  have hn : (q.A + q.B).toNat = A + B := by omega
  unfold mixedBlockBound
  rw [hn, ← mixedCellCatalog_fiber A B q hA hB]
  have he : mixedCatalogFiber q (mixedCellCatalog A B) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro c hc
    have hne : c.1 ≠ q := by
      intro he
      apply hq
      simp only [mixedRepresentedBlocks, List.mem_toFinset, List.mem_map]
      exact ⟨c, hc, he⟩
    simp [hne]
  rw [he]
  rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedValid_zero_params
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_fiber
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_fiber
#print axioms VOA.DeligneAudit.SL4T.mixedRepresentedBlocks_valid
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_zero_of_unrepresented

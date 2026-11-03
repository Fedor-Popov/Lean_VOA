import VOA.DeligneAudit.SL4TMixedCellBound

/-! # Site words and their uniquely determined mixed parameter blocks -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The unique terminal parameter tuple. -/
def mixedEmptyParams : MixedParams := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Reinsert a b-site with its chosen state. -/
def mixedBPrevious (q : MixedParams) : MixedBState → MixedParams
  | .s1 => {q with B := q.B + 1}
  | .d1 => {q with B := q.B + 1, e1 := q.e1 + 1}
  | .s2 => {q with B := q.B + 1, d2 := q.d2 + 1, e2 := q.e2 + 1}
  | .d2 => {q with B := q.B + 1, d2 := q.d2 + 1}

/-- Reinsert an a-site with its two node choices. -/
def mixedAPrevious (q : MixedParams) (s : MixedAState) : MixedParams :=
  {q with
    A := q.A + 1
    d1 := q.d1 + (if s.1 = .outside then 0 else 1)
    d3 := q.d3 + (if s.2 = .original then 1 else 0)
    e1 := q.e1 + (if s.1 = .chosen then 1 else 0)
    e2 := q.e2 + (if s.2 = .chosen then 1 else 0)}

theorem mixedBNext_previous (q : MixedParams) (s : MixedBState) :
    mixedBNext (mixedBPrevious q s) s = q := by
  cases s <;> cases q <;> simp [mixedBNext, mixedBPrevious]

theorem mixedBPrevious_next (q : MixedParams) (s : MixedBState) :
    mixedBPrevious (mixedBNext q s) s = q := by
  cases s <;> cases q <;> simp [mixedBNext, mixedBPrevious]

theorem mixedANext_previous (q : MixedParams) (s : MixedAState) :
    mixedANext (mixedAPrevious q s) s = q := by
  cases q
  simp [mixedANext, mixedAPrevious]

theorem mixedAPrevious_next (q : MixedParams) (s : MixedAState) :
    mixedAPrevious (mixedANext q s) s = q := by
  cases q
  simp [mixedANext, mixedAPrevious]

theorem mixedBPrevious_valid (q : MixedParams) (hq : MixedValid q) (s : MixedBState) :
    MixedValid (mixedBPrevious q s) := by
  cases s <;> simp only [MixedValid, mixedBPrevious, mixedP, mixedQ] at * <;> omega

theorem mixedAPrevious_valid (q : MixedParams) (hq : MixedValid q) (s : MixedAState) :
    MixedValid (mixedAPrevious q s) := by
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [MixedValid, mixedAPrevious, mixedP, mixedQ] at * <;> omega

/-- Prefix a b-letter to a cell, retaining the block determined by the word. -/
def mixedBPrepend (s : MixedBState) (c : MixedParams × MixedCellCounts) :
    MixedParams × MixedCellCounts :=
  (mixedBPrevious c.1 s, mixedCellShift (mixedBZeroRoots s) 0 c.2)

/-- Prefix an a-letter to a cell, retaining the block determined by the word. -/
def mixedAPrepend (s : MixedAState) (c : MixedParams × MixedCellCounts) :
    MixedParams × MixedCellCounts :=
  (mixedAPrevious c.1 s, mixedCellShift (mixedADoubleCount s) (mixedATripleCount s) c.2)

/-- All a-site words, including their block parameters and cell counts. -/
def mixedACellCatalog : ℕ → List (MixedParams × MixedCellCounts)
  | 0 => [(mixedEmptyParams, (0, 0))]
  | A + 1 => (List.range 9).flatMap (fun i => if hi : i < 9 then
      (mixedACellCatalog A).map (mixedAPrepend (mixedAOrder ⟨i, hi⟩)) else [])

/-- All mixed words in the same state order used by the ideal filtration. -/
def mixedCellCatalog (A : ℕ) : ℕ → List (MixedParams × MixedCellCounts)
  | 0 => mixedACellCatalog A
  | B + 1 => (List.range 4).flatMap (fun i => if hi : i < 4 then
      (mixedCellCatalog A B).map (mixedBPrepend (mixedBOrder ⟨i, hi⟩)) else [])

theorem mixedACellCatalog_valid (A : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ mixedACellCatalog A) : MixedValid c.1 ∧ c.1.A = A ∧ c.1.B = 0 := by
  induction A generalizing c with
  | zero =>
      simp only [mixedACellCatalog, List.mem_singleton] at hc
      subst c
      norm_num [mixedEmptyParams, MixedValid, mixedP, mixedQ]
  | succ A ih =>
      simp only [mixedACellCatalog, List.mem_flatMap] at hc
      obtain ⟨i, hi, hc⟩ := hc
      have hi' : i < 9 := List.mem_range.mp hi
      rw [dif_pos hi'] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hv, hA, hB⟩ := ih d hd
      refine ⟨mixedAPrevious_valid _ hv _, ?_, ?_⟩ <;>
        simp [mixedAPrepend, mixedAPrevious, hA, hB, Nat.cast_add, Nat.cast_one]

theorem mixedCellCatalog_valid (A B : ℕ) (c : MixedParams × MixedCellCounts)
    (hc : c ∈ mixedCellCatalog A B) : MixedValid c.1 ∧ c.1.A = A ∧ c.1.B = B := by
  induction B generalizing c with
  | zero => exact mixedACellCatalog_valid A c hc
  | succ B ih =>
      simp only [mixedCellCatalog, List.mem_flatMap] at hc
      obtain ⟨i, hi, hc⟩ := hc
      have hi' : i < 4 := List.mem_range.mp hi
      rw [dif_pos hi'] at hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hv, hA, hB⟩ := ih d hd
      refine ⟨mixedBPrevious_valid _ hv _, ?_, ?_⟩ <;>
        cases mixedBOrder ⟨i, hi'⟩ <;>
          simp [mixedBPrepend, mixedBPrevious, hA, hB, Nat.cast_add, Nat.cast_one]

/-- Extract the cells belonging to a fixed parameter block, preserving order and multiplicity. -/
def mixedCatalogFiber (q : MixedParams) (l : List (MixedParams × MixedCellCounts)) :
    List MixedCellCounts := l.filterMap (fun c => if c.1 = q then some c.2 else none)

theorem mixedCatalogFiber_flatMap {ι : Type*} (q : MixedParams)
    (l : List ι) (f : ι → List (MixedParams × MixedCellCounts)) :
    mixedCatalogFiber q (l.flatMap f) = l.flatMap (fun i => mixedCatalogFiber q (f i)) := by
  simp [mixedCatalogFiber, List.filterMap_flatMap]

/-- Fibers commute with an invertible parameter update and a cell-count update. -/
theorem mixedCatalogFiber_map (q : MixedParams) (l : List (MixedParams × MixedCellCounts))
    (prev next : MixedParams → MixedParams) (shift : MixedCellCounts → MixedCellCounts)
    (hp : ∀ x, prev (next x) = x) (hn : ∀ x, next (prev x) = x) :
    mixedCatalogFiber q (l.map (fun c => (prev c.1, shift c.2))) =
      (mixedCatalogFiber (next q) l).map shift := by
  have he (x : MixedParams) : prev x = q ↔ x = next q := by
    constructor
    · intro h
      rw [← h, hn]
    · rintro rfl
      exact hp q
  induction l with
  | nil => rfl
  | cons c l ih =>
      by_cases hc : c.1 = next q <;>
        simp [mixedCatalogFiber, he, hc] at ih ⊢ <;> exact ih

theorem mixedCatalogFiber_nil_of_invalid (q : MixedParams) (hq : ¬ MixedValid q)
    (l : List (MixedParams × MixedCellCounts)) (hl : ∀ c ∈ l, MixedValid c.1) :
    mixedCatalogFiber q l = [] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      have hne : c.1 ≠ q := by rintro rfl; exact hq (hl c (by simp))
      simp only [mixedCatalogFiber, List.filterMap_cons, if_neg hne]
      exact ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedBNext_previous
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious_next
#print axioms VOA.DeligneAudit.SL4T.mixedANext_previous
#print axioms VOA.DeligneAudit.SL4T.mixedAPrevious_next
#print axioms VOA.DeligneAudit.SL4T.mixedBPrevious_valid
#print axioms VOA.DeligneAudit.SL4T.mixedAPrevious_valid
#print axioms VOA.DeligneAudit.SL4T.mixedACellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.mixedCellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_flatMap
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_map
#print axioms VOA.DeligneAudit.SL4T.mixedCatalogFiber_nil_of_invalid

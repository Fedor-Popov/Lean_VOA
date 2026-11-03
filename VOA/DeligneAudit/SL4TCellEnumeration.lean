import VOA.DeligneAudit.SL4TCellCatalog
import Mathlib.Data.List.Nodup

/-! # Completeness and uniqueness of the site-cell enumeration -/

namespace VOA.DeligneAudit.SL4T

def cellRemove (M : ℕ) (c : SiteCell) : SiteCell := (c.1.erase M, c.2.erase M)

def cellLast (M : ℕ) (c : SiteCell) : Bool × Bool :=
  (decide (M ∈ c.1), decide (M ∈ c.2))

theorem erase_last_subset {M : ℕ} {G : Finset ℕ} (h : G ⊆ Finset.range (M + 1)) :
    G.erase M ⊆ Finset.range M := by
  intro i hi
  have he := Finset.mem_erase.mp hi
  have hr := Finset.mem_range.mp (h he.2)
  exact Finset.mem_range.mpr (by omega)

theorem cellRemove_valid {M a b : ℕ} {c : SiteCell} (h : CellValid (M + 1) a b c) :
    CellValid M (a - if M ∈ c.1 then 1 else 0) (b - if M ∈ c.2 then 1 else 0)
      (cellRemove M c) := by
  refine ⟨erase_last_subset h.1, ?_, erase_last_subset h.2.2.1, ?_⟩
  · by_cases hc : M ∈ c.1
    · simp only [cellRemove, if_pos hc, Finset.card_erase_of_mem hc, h.2.1]
    · simp only [cellRemove, if_neg hc, Finset.erase_eq_of_notMem hc, Nat.sub_zero, h.2.1]
  · by_cases hc : M ∈ c.2
    · simp only [cellRemove, if_pos hc, Finset.card_erase_of_mem hc, h.2.2.2]
    · simp only [cellRemove, if_neg hc, Finset.erase_eq_of_notMem hc, Nat.sub_zero, h.2.2.2]

theorem cellLift_remove (M : ℕ) (c : SiteCell) :
    cellLift M (cellLast M c).1 (cellLast M c).2 (cellRemove M c) = c := by
  rcases c with ⟨G, H⟩
  by_cases hg : M ∈ G <;> by_cases hh : M ∈ H <;>
    simp [cellLift, cellLast, cellRemove, hg, hh, Finset.insert_erase]

theorem cellRemove_lift {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c)
    (l r : Bool) : cellRemove M (cellLift M l r c) = c := by
  have hn := cell_not_mem_last h
  rcases c with ⟨G, H⟩
  cases l <;> cases r <;> simp [cellLift, cellRemove, hn.1, hn.2]

theorem cellLast_lift {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c)
    (l r : Bool) : cellLast M (cellLift M l r c) = (l, r) := by
  have hn := cell_not_mem_last h
  cases l <;> cases r <;> simp [cellLast, cellLift, hn.1, hn.2]

theorem cellCatalog_complete (M a b : ℕ) (c : SiteCell) (h : CellValid M a b c) :
    c ∈ cellCatalog M a b := by
  induction M generalizing a b c with
  | zero =>
      have hg : c.1 = ∅ := Finset.subset_empty.mp (by simpa using h.1)
      have hh : c.2 = ∅ := Finset.subset_empty.mp (by simpa using h.2.2.1)
      have ha : a = 0 := by simpa only [hg, Finset.card_empty] using h.2.1.symm
      have hb : b = 0 := by simpa only [hh, Finset.card_empty] using h.2.2.2.symm
      have hc : c = (∅, ∅) := Prod.ext hg hh
      simp [cellCatalog, ha, hb, hc]
  | succ M ih =>
      have he := cellRemove_valid h
      have ha : a ≤ M + 1 := by
        simpa only [Finset.card_range, h.2.1] using (Finset.card_le_card h.1)
      have hb : b ≤ M + 1 := by
        simpa only [Finset.card_range, h.2.2.2] using (Finset.card_le_card h.2.2.1)
      have hrestore := cellLift_remove M c
      simp only [cellCatalog, List.mem_append]
      by_cases hg : M ∈ c.1 <;> by_cases hh : M ∈ c.2
      · have ha0 : 0 < a := by rw [← h.2.1]; exact Finset.card_pos.mpr ⟨M, hg⟩
        have hb0 : 0 < b := by rw [← h.2.2.2]; exact Finset.card_pos.mpr ⟨M, hh⟩
        apply Or.inl ∘ Or.inr
        rw [if_pos ⟨ha0, ha, hb0, hb⟩]
        apply List.mem_map.mpr
        refine ⟨cellRemove M c, ih (a - 1) (b - 1) _ ?_, ?_⟩
        · simpa only [if_pos hg, if_pos hh] using he
        · simpa only [cellLast, decide_eq_true hg, decide_eq_true hh] using hrestore
      · have ha0 : 0 < a := by rw [← h.2.1]; exact Finset.card_pos.mpr ⟨M, hg⟩
        have hbM : b ≤ M := by
          have hs := erase_last_subset h.2.2.1
          rw [Finset.erase_eq_of_notMem hh] at hs
          simpa only [Finset.card_range, h.2.2.2] using Finset.card_le_card hs
        apply Or.inr
        rw [if_pos ⟨ha0, ha, hbM⟩]
        apply List.mem_map.mpr
        refine ⟨cellRemove M c, ih (a - 1) b _ ?_, ?_⟩
        · simpa only [if_pos hg, if_neg hh, Nat.sub_zero] using he
        · simpa only [cellLast, decide_eq_true hg, decide_eq_false hh] using hrestore
      · have hb0 : 0 < b := by rw [← h.2.2.2]; exact Finset.card_pos.mpr ⟨M, hh⟩
        have haM : a ≤ M := by
          have hs := erase_last_subset h.1
          rw [Finset.erase_eq_of_notMem hg] at hs
          simpa only [Finset.card_range, h.2.1] using Finset.card_le_card hs
        apply Or.inl ∘ Or.inl ∘ Or.inr
        rw [if_pos ⟨haM, hb0, hb⟩]
        apply List.mem_map.mpr
        refine ⟨cellRemove M c, ih a (b - 1) _ ?_, ?_⟩
        · simpa only [if_neg hg, if_pos hh, Nat.sub_zero] using he
        · simpa only [cellLast, decide_eq_false hg, decide_eq_true hh] using hrestore
      · have he' : CellValid M a b c := by
          simpa only [if_neg hg, if_neg hh, Nat.sub_zero, cellRemove,
            Finset.erase_eq_of_notMem hg, Finset.erase_eq_of_notMem hh, Prod.eta] using he
        have haM : a ≤ M := by
          simpa only [Finset.card_range, h.2.1] using (Finset.card_le_card he'.1)
        have hbM : b ≤ M := by
          simpa only [Finset.card_range, h.2.2.2] using (Finset.card_le_card he'.2.2.1)
        apply Or.inl ∘ Or.inl ∘ Or.inl
        rw [if_pos ⟨haM, hbM⟩]
        exact ih a b c he'

theorem mem_cellCatalog (M a b : ℕ) (c : SiteCell) :
    c ∈ cellCatalog M a b ↔ CellValid M a b c :=
  ⟨cellCatalog_valid M a b c, cellCatalog_complete M a b c⟩

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellRemove_valid
#print axioms VOA.DeligneAudit.SL4T.cellLift_remove
#print axioms VOA.DeligneAudit.SL4T.cellRemove_lift
#print axioms VOA.DeligneAudit.SL4T.cellLast_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_complete
#print axioms VOA.DeligneAudit.SL4T.mem_cellCatalog

import VOA.DeligneAudit.SL4TCellUniqueness
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff

/-! # The all-parameter cell count in Finset form -/

namespace VOA.DeligneAudit.SL4T

open scoped symmDiff

def cellSet (M a b : ℕ) : Finset SiteCell :=
  ((Finset.range M).powersetCard a).product ((Finset.range M).powersetCard b)

theorem mem_cellSet (M a b : ℕ) (c : SiteCell) : c ∈ cellSet M a b ↔ CellValid M a b c := by
  rcases c with ⟨G, H⟩
  simp only [cellSet, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_powersetCard, CellValid]
  tauto

theorem cellCatalog_toFinset (M a b : ℕ) : (cellCatalog M a b).toFinset = cellSet M a b := by
  ext c
  simp only [List.mem_toFinset, mem_cellCatalog, mem_cellSet]

def cellWeight (c : SiteCell) : ℕ := 3 ^ (c.1 ∩ c.2).card * 2 ^ (c.1 ∆ c.2).card

/-- The coefficient count `u_M(a,b)`, kept as a finite sum over all cells. -/
def u (M a b : ℕ) : ℕ := ∑ c ∈ cellSet M a b, cellWeight c

theorem cell_card_identities (c : SiteCell) :
    cellCutoff c + (c.1 ∩ c.2).card = c.1.card + c.2.card ∧
      (c.1 ∆ c.2).card + (c.1 ∩ c.2).card = cellCutoff c := by
  refine ⟨Finset.card_union_add_card_inter _ _, ?_⟩
  have hd : Disjoint (c.1 ∆ c.2) (c.1 ∩ c.2) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at hx hy
    tauto
  rw [← Finset.card_union_of_disjoint hd]
  exact congrArg Finset.card (symmDiff_sup_inf c.1 c.2)

theorem cellCutoff_bounds {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c) :
    cellCutoff c ≤ a + b ∧ a + b ≤ 2 * cellCutoff c := by
  obtain ⟨hu, hd⟩ := cell_card_identities c
  rw [h.2.1, h.2.2.2] at hu
  omega

theorem cellCutoff_pos {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c)
    (hr : 0 < a + b) : 0 < cellCutoff c := by
  have hb := cellCutoff_bounds h
  omega

theorem cellWeight_closed {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c) :
    cellWeight c = 3 ^ (a + b - cellCutoff c) * 2 ^ (2 * cellCutoff c - (a + b)) := by
  obtain ⟨hu, hd⟩ := cell_card_identities c
  rw [h.2.1, h.2.2.2] at hu
  have hi : a + b - cellCutoff c = (c.1 ∩ c.2).card := by omega
  have hs : 2 * cellCutoff c - (a + b) = (c.1 ∆ c.2).card := by omega
  rw [hi, hs]
  rfl

theorem cell_count_list (M a b : ℕ) :
    ((cellLevels M a b).map (fun n => 3 ^ (a + b - n) * 2 ^ (2 * n - (a + b)))).sum =
      u M a b := by
  rw [← cellCatalog_levels, List.map_map, u, ← cellCatalog_toFinset,
    List.sum_toFinset _ (cellCatalog_nodup M a b)]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact (cellWeight_closed (cellCatalog_valid M a b c hc)).symm

theorem list_sum_getD (ns : List ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range ns.length, f (ns.getD i 0)) = (ns.map f).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons,
        ih, add_comm]

/-- The exact sum used by `cellFlag_bound_two`, in natural-indexed form. -/
theorem cell_count_formula (M a b : ℕ) :
    (∑ i ∈ Finset.range (cellLevels M a b).length,
      3 ^ (a + b - (cellLevels M a b).getD i 0) *
        2 ^ (2 * (cellLevels M a b).getD i 0 - (a + b))) =
      ∑ c ∈ cellSet M a b, 3 ^ (c.1 ∩ c.2).card * 2 ^ (c.1 ∆ c.2).card := by
  rw [list_sum_getD (cellLevels M a b)
    (fun n => 3 ^ (a + b - n) * 2 ^ (2 * n - (a + b)))]
  exact cell_count_list M a b

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mem_cellSet
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_toFinset
#print axioms VOA.DeligneAudit.SL4T.cell_card_identities
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_bounds
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_pos
#print axioms VOA.DeligneAudit.SL4T.cellWeight_closed
#print axioms VOA.DeligneAudit.SL4T.cell_count_list
#print axioms VOA.DeligneAudit.SL4T.list_sum_getD
#print axioms VOA.DeligneAudit.SL4T.cell_count_formula

import VOA.DeligneAudit.SL4TK1

/-! # The ordered subset cells behind the recursive K1 cutoffs -/

namespace VOA.DeligneAudit.SL4T

abbrev SiteCell := Finset ℕ × Finset ℕ

def CellValid (M a b : ℕ) (c : SiteCell) : Prop :=
  c.1 ⊆ Finset.range M ∧ c.1.card = a ∧ c.2 ⊆ Finset.range M ∧ c.2.card = b

def cellLift (M : ℕ) (l r : Bool) (c : SiteCell) : SiteCell :=
  (if l then insert M c.1 else c.1, if r then insert M c.2 else c.2)

def cellCatalog : ℕ → ℕ → ℕ → List SiteCell
  | 0, a, b => if a = 0 ∧ b = 0 then [(∅, ∅)] else []
  | M + 1, a, b =>
      (if a ≤ M ∧ b ≤ M then cellCatalog M a b else []) ++
      (if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
        (cellCatalog M a (b - 1)).map (cellLift M false true) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
        (cellCatalog M (a - 1) (b - 1)).map (cellLift M true true) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
        (cellCatalog M (a - 1) b).map (cellLift M true false) else [])

theorem cell_not_mem_last {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c) :
    M ∉ c.1 ∧ M ∉ c.2 := by
  exact ⟨fun hc => Nat.lt_irrefl M (Finset.mem_range.mp (h.1 hc)),
    fun hc => Nat.lt_irrefl M (Finset.mem_range.mp (h.2.2.1 hc))⟩

theorem cellValid_mono {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c) :
    CellValid (M + 1) a b c := by
  exact ⟨h.1.trans (Finset.range_mono (by omega)), h.2.1,
    h.2.2.1.trans (Finset.range_mono (by omega)), h.2.2.2⟩

theorem cellValid_lift {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c)
    (l r : Bool) :
    CellValid (M + 1) (a + if l then 1 else 0) (b + if r then 1 else 0)
      (cellLift M l r c) := by
  have hn := cell_not_mem_last h
  have hmono := cellValid_mono h
  have hM : M ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  cases l <;> cases r <;>
    simp only [cellLift, CellValid, Bool.false_eq_true, if_false, if_true,
      Nat.add_zero, Finset.insert_subset_iff, Finset.card_insert_of_notMem hn.1,
      Finset.card_insert_of_notMem hn.2]
  · exact hmono
  · exact ⟨hmono.1, h.2.1, ⟨hM, hmono.2.2.1⟩, congrArg (· + 1) h.2.2.2⟩
  · exact ⟨⟨hM, hmono.1⟩, congrArg (· + 1) h.2.1, hmono.2.2.1, h.2.2.2⟩
  · exact ⟨⟨hM, hmono.1⟩, congrArg (· + 1) h.2.1,
      ⟨hM, hmono.2.2.1⟩, congrArg (· + 1) h.2.2.2⟩

theorem cellCatalog_valid (M a b : ℕ) : ∀ c ∈ cellCatalog M a b, CellValid M a b c := by
  induction M generalizing a b with
  | zero =>
      intro c hc
      simp only [cellCatalog] at hc
      split_ifs at hc with h
      · rcases h with ⟨rfl, rfl⟩
        simp only [List.mem_singleton] at hc
        subst c
        simp [CellValid]
      · simp only [List.not_mem_nil] at hc
  | succ M ih =>
      intro c hc
      simp only [cellCatalog, List.mem_append] at hc
      rcases hc with ((hc | hc) | hc) | hc
      · split_ifs at hc with h
        · exact cellValid_mono (ih a b c hc)
        · simp only [List.not_mem_nil] at hc
      · split_ifs at hc with h
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          simpa only [Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            Nat.sub_add_cancel (show 1 ≤ b by omega)] using
            cellValid_lift (ih a (b - 1) d hd) false true
        · simp only [List.not_mem_nil] at hc
      · split_ifs at hc with h
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          simpa only [if_true, Nat.sub_add_cancel (show 1 ≤ a by omega),
            Nat.sub_add_cancel (show 1 ≤ b by omega)] using
            cellValid_lift (ih (a - 1) (b - 1) d hd) true true
        · simp only [List.not_mem_nil] at hc
      · split_ifs at hc with h
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          simpa only [Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            Nat.sub_add_cancel (show 1 ≤ a by omega)] using
            cellValid_lift (ih (a - 1) b d hd) true false
        · simp only [List.not_mem_nil] at hc

def cellCutoff (c : SiteCell) : ℕ := (c.1 ∪ c.2).card

theorem cellCutoff_lift {M a b : ℕ} {c : SiteCell} (h : CellValid M a b c)
    (l r : Bool) :
    cellCutoff (cellLift M l r c) = cellCutoff c + if l || r then 1 else 0 := by
  have hn : M ∉ c.1 ∪ c.2 := by
    simpa only [Finset.mem_union, not_or] using cell_not_mem_last h
  cases l <;> cases r <;>
    simp [cellCutoff, cellLift, Finset.insert_union, Finset.union_insert,
      Finset.card_insert_of_notMem hn]

theorem cellCatalog_levels (M a b : ℕ) :
    (cellCatalog M a b).map cellCutoff = cellLevels M a b := by
  induction M generalizing a b with
  | zero =>
      simp only [cellCatalog, cellLevels]
      split_ifs <;> simp [cellCutoff]
  | succ M ih =>
      simp only [cellCatalog, cellLevels, List.map_append]
      congr 1
      · congr 1
        · congr 1
          · split_ifs <;> simp only [ih, List.map_nil]
          · split_ifs
            · rw [List.map_map, ← ih, List.map_map]
              apply List.map_congr_left
              intro c hc
              exact cellCutoff_lift (cellCatalog_valid M a (b - 1) c hc) false true
            · rfl
        · split_ifs
          · rw [List.map_map, ← ih, List.map_map]
            apply List.map_congr_left
            intro c hc
            exact cellCutoff_lift (cellCatalog_valid M (a - 1) (b - 1) c hc) true true
          · rfl
      · split_ifs
        · rw [List.map_map, ← ih, List.map_map]
          apply List.map_congr_left
          intro c hc
          exact cellCutoff_lift (cellCatalog_valid M (a - 1) b c hc) true false
        · rfl

theorem k1_catalog (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    SpanningChain (S_relationIdeal M a b) ⊥ ⊤ ((cellCatalog M a b).map cellCutoff) := by
  rw [cellCatalog_levels]
  exact k1_recursive M a b ha hb

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellValid_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.cellCutoff_lift
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_levels
#print axioms VOA.DeligneAudit.SL4T.k1_catalog

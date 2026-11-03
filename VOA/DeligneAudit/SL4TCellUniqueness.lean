import VOA.DeligneAudit.SL4TCellEnumeration
import VOA.DeligneAudit.SL4TFlagExport

/-! # No repeated cells, and the natural-indexed spanning statement of K1 -/

namespace VOA.DeligneAudit.SL4T

theorem cellCatalog_lift_nodup (M a b : ℕ) (l r : Bool)
    (h : (cellCatalog M a b).Nodup) :
    ((cellCatalog M a b).map (cellLift M l r)).Nodup := by
  apply List.Nodup.map_on _ h
  intro c hc d hd heq
  have he := congrArg (cellRemove M) heq
  simpa only [cellRemove_lift (cellCatalog_valid M a b c hc),
    cellRemove_lift (cellCatalog_valid M a b d hd)] using he

theorem cellCatalog_nodup (M a b : ℕ) : (cellCatalog M a b).Nodup := by
  induction M generalizing a b with
  | zero => simp only [cellCatalog]; split_ifs <;> simp
  | succ M ih =>
      let L0 := if a ≤ M ∧ b ≤ M then cellCatalog M a b else []
      let L1 := if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
        (cellCatalog M a (b - 1)).map (cellLift M false true) else []
      let L2 := if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
        (cellCatalog M (a - 1) (b - 1)).map (cellLift M true true) else []
      let L3 := if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
        (cellCatalog M (a - 1) b).map (cellLift M true false) else []
      have h0 : L0.Nodup := by
        dsimp only [L0]
        split_ifs
        · exact ih a b
        · exact List.nodup_nil
      have h1 : L1.Nodup := by
        dsimp only [L1]
        split_ifs
        · exact cellCatalog_lift_nodup M a (b - 1) false true (ih _ _)
        · exact List.nodup_nil
      have h2 : L2.Nodup := by
        dsimp only [L2]
        split_ifs
        · exact cellCatalog_lift_nodup M (a - 1) (b - 1) true true (ih _ _)
        · exact List.nodup_nil
      have h3 : L3.Nodup := by
        dsimp only [L3]
        split_ifs
        · exact cellCatalog_lift_nodup M (a - 1) b true false (ih _ _)
        · exact List.nodup_nil
      have hs0 : ∀ c ∈ L0, cellLast M c = (false, false) := by
        intro c hc
        dsimp only [L0] at hc
        split_ifs at hc
        · exact cellLast_lift (cellCatalog_valid M a b c hc) false false
        · simp only [List.not_mem_nil] at hc
      have hs1 : ∀ c ∈ L1, cellLast M c = (false, true) := by
        intro c hc
        dsimp only [L1] at hc
        split_ifs at hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact cellLast_lift (cellCatalog_valid M a (b - 1) d hd) false true
        · simp only [List.not_mem_nil] at hc
      have hs2 : ∀ c ∈ L2, cellLast M c = (true, true) := by
        intro c hc
        dsimp only [L2] at hc
        split_ifs at hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact cellLast_lift (cellCatalog_valid M (a - 1) (b - 1) d hd) true true
        · simp only [List.not_mem_nil] at hc
      have hs3 : ∀ c ∈ L3, cellLast M c = (true, false) := by
        intro c hc
        dsimp only [L3] at hc
        split_ifs at hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact cellLast_lift (cellCatalog_valid M (a - 1) b d hd) true false
        · simp only [List.not_mem_nil] at hc
      have h01 : (L0 ++ L1).Nodup := h0.append h1 (by
        rw [List.disjoint_left]
        intro c hc hd
        have he := (hs0 c hc).symm.trans (hs1 c hd)
        cases he)
      have h012 : ((L0 ++ L1) ++ L2).Nodup := h01.append h2 (by
        rw [List.disjoint_left]
        intro c hc hd
        rcases List.mem_append.mp hc with hc | hc
        · have he := (hs0 c hc).symm.trans (hs2 c hd)
          cases he
        · have he := (hs1 c hc).symm.trans (hs2 c hd)
          cases he)
      exact h012.append h3 (by
        rw [List.disjoint_left]
        intro c hc hd
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · have he := (hs0 c hc).symm.trans (hs3 c hd)
            cases he
          · have he := (hs1 c hc).symm.trans (hs3 c hd)
            cases he
        · have he := (hs2 c hc).symm.trans (hs3 c hd)
          cases he)

/-- K1 with one natural-indexed generator and cutoff for each ordered subset cell. -/
theorem k1_spanning (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    ∃ (σ : ℕ → S M a b) (F : ℕ → Ideal (S M a b)),
      (∀ k ≤ (cellCatalog M a b).length,
        (F k).restrictScalars ℂ = generatorPrefix σ k) ∧
      F (cellCatalog M a b).length = ⊤ ∧
      (∀ i < (cellCatalog M a b).length,
        Polynomial.C (σ i) * Polynomial.X ^
          (((cellCatalog M a b).map cellCutoff).getD i 0) ∈
            (F i).map Polynomial.C ⊔ S_relationIdeal M a b) := by
  simpa only [List.length_map] using (k1_catalog M a b ha hb).prefix_export

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellCatalog_lift_nodup
#print axioms VOA.DeligneAudit.SL4T.cellCatalog_nodup
#print axioms VOA.DeligneAudit.SL4T.k1_spanning

import VOA.DeligneAudit.D4LevelReductionCommonRootPieces

/-! A two-Grassmannian cell flag with simultaneous union and common-root relations. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open Polynomial
open VOA.DeligneAudit.SL4T

/-- The recursive list of union sizes and adjoint-site differences. -/
def commonRootCellDegrees : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, b => if a = 0 ∧ b = 0 then [(0, 0)] else []
  | M + 1, a, b =>
      (if a ≤ M ∧ b ≤ M then commonRootCellDegrees M a b else []) ++
      (if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
        (commonRootCellDegrees M a (b - 1)).map (fun n => (n.1 + 1, n.2 + 1)) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
        (commonRootCellDegrees M (a - 1) (b - 1)).map (fun n => (n.1 + 1, n.2)) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
        (commonRootCellDegrees M (a - 1) b).map (fun n => (n.1 + 1, n.2)) else [])

/-- The zero-site flag has both characteristic relations. -/
theorem commonRootCellChain_zero :
    TwoRelationChain (S_relationIdeal 0 0 0) (grassmannianCommonRootIdeal 0 0 0)
      ⊥ ⊤ [(0, 0)] := by
  refine .cons 1 0 0 ?_ ?_ ?_ (.nil ⊤)
  · simp only [Submodule.restrictScalars_top, Submodule.restrictScalars_bot,
      bot_sup_eq, S_zero_span_one]
  · simp only [map_one, pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    exact relationIdeal_power (leftP 0 0 0) (rightP 0 0 0) 0
  · simp only [map_one, pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    have h := commonRootIdeal_left (rightP 0 0 0) (leftPbar 0 0 0)
    simpa [grassmannianCommonRootIdeal, rightP_eq_sum, rightE_zero_index] using h

/-- Every site count and every pair of valid alphabet sizes has a simultaneous flag. -/
theorem commonRootCellChain (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    TwoRelationChain (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
      ⊥ ⊤ (commonRootCellDegrees M a b) := by
  induction M generalizing a b with
  | zero =>
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst a
      subst b
      simpa only [commonRootCellDegrees, and_self, if_true] using commonRootCellChain_zero
  | succ M ih =>
      have hnn : TwoRelationChain (S_relationIdeal (M + 1) a b)
          (grassmannianCommonRootIdeal (M + 1) a b) ⊥ (thomI1 (M + 1) a b)
          (if a ≤ M ∧ b ≤ M then commonRootCellDegrees M a b else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            commonRootFlag_emptySite (M + 1) a b (by omega) (by omega) (ih a b h.1 h.2)
        · have heq : thomI1 (M + 1) a b = ⊥ := by
            by_cases haM : a = M + 1
            · subst a
              exact thomI1_top_left _ _ (by omega)
            · have hbM : b = M + 1 := by omega
              subst b
              exact thomI1_top_right _ _ (by omega)
          rw [heq]
          exact .nil _
      have hng : TwoRelationChain (S_relationIdeal (M + 1) a b)
          (grassmannianCommonRootIdeal (M + 1) a b)
          (thomI1 (M + 1) a b) (thomI2 (M + 1) a b)
          (if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
            (commonRootCellDegrees M a (b - 1)).map (fun n => (n.1 + 1, n.2 + 1)) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            commonRootFlag_adjointSite (M + 1) a b (by omega) hb h.2.1 (ih a (b - 1) h.1 (by omega))
        · have heq : thomI1 (M + 1) a b = thomI2 (M + 1) a b := by
            by_cases hb0 : b = 0
            · subst b
              exact thomI1_zero_right _ _
            · have haM : a = M + 1 := by omega
              subst a
              rw [thomI1_top_left _ _ (by omega), thomI2_top_left _ _ (by omega)]
          rw [heq]
          exact .nil _
      have hboth : TwoRelationChain (S_relationIdeal (M + 1) a b)
          (grassmannianCommonRootIdeal (M + 1) a b)
          (thomI2 (M + 1) a b) (thomI3 (M + 1) a b)
          (if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
            (commonRootCellDegrees M (a - 1) (b - 1)).map (fun n => (n.1 + 1, n.2)) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            commonRootFlag_intersectionSite (M + 1) a b ha hb h.1 h.2.2.1
              (ih (a - 1) (b - 1) (by omega) (by omega))
        · have heq : thomI3 (M + 1) a b = thomI2 (M + 1) a b := by
            by_cases ha0 : a = 0
            · subst a
              rw [thomI3_zero_left, thomI2_zero_left]
            · have hb0 : b = 0 := by omega
              subst b
              exact thomI3_zero_right _ _ (by omega)
          rw [heq]
          exact .nil _
      have hgn : TwoRelationChain (S_relationIdeal (M + 1) a b)
          (grassmannianCommonRootIdeal (M + 1) a b) (thomI3 (M + 1) a b) ⊤
          (if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
            (commonRootCellDegrees M (a - 1) b).map (fun n => (n.1 + 1, n.2)) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            commonRootFlag_complementSite (M + 1) a b ha h.1 (by omega)
              (ih (a - 1) b (by omega) h.2.2)
        · have heq : thomI3 (M + 1) a b = ⊤ := by
            by_cases ha0 : a = 0
            · subst a
              exact thomI3_zero_left _ _
            · have hbM : b = M + 1 := by omega
              subst b
              exact thomI3_top_right _ _
          rw [heq]
          exact .nil _
      exact ((hnn.append hng).append hboth).append hgn


/-- The cell records its union size and the number of adjoint sites outside the other alphabet. -/
def commonRootCellDegree (c : SiteCell) : ℕ × ℕ :=
  (cellCutoff c, (c.2 \ c.1).card)

/-- Adding a site changes the two recorded degrees by their respective membership rules. -/
theorem commonRootCellDegree_lift {M A a : ℕ} {c : SiteCell} (h : CellValid M A a c)
    (l r : Bool) :
    commonRootCellDegree (cellLift M l r c) =
      ((commonRootCellDegree c).1 + if l || r then 1 else 0,
        (commonRootCellDegree c).2 + if !l && r then 1 else 0) := by
  apply Prod.ext
  · exact cellCutoff_lift h l r
  · have hv := cellValid_lift h l r
    have hc := cellCutoff_lift h l r
    have he := Finset.card_sdiff_add_card c.2 c.1
    have hf := Finset.card_sdiff_add_card (cellLift M l r c).2 (cellLift M l r c).1
    rw [Finset.union_comm c.2, h.2.1] at he
    rw [Finset.union_comm (cellLift M l r c).2, hv.2.1] at hf
    change _ + A = cellCutoff c at he
    change _ + _ = cellCutoff (cellLift M l r c) at hf
    dsimp only [commonRootCellDegree]
    rw [hc] at hf
    cases l <;> cases r <;> simp only [Bool.false_eq_true, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true, Bool.true_and,
      Bool.false_and, if_true, if_false] at * <;> omega

/-- The recursively generated degrees are exactly those of the ordered honest-pair cells. -/
theorem commonRootCellDegrees_catalog (M a b : ℕ) :
    (cellCatalog M a b).map commonRootCellDegree = commonRootCellDegrees M a b := by
  induction M generalizing a b with
  | zero =>
      simp only [cellCatalog, commonRootCellDegrees]
      split_ifs <;> simp [commonRootCellDegree, cellCutoff]
  | succ M ih =>
      simp only [cellCatalog, commonRootCellDegrees, List.map_append]
      congr 1
      · congr 1
        · congr 1
          · split_ifs <;> simp only [ih, List.map_nil]
          · split_ifs
            · rw [List.map_map, ← ih, List.map_map]
              apply List.map_congr_left
              intro c hc
              exact commonRootCellDegree_lift (cellCatalog_valid M a (b - 1) c hc)
                false true
            · rfl
        · split_ifs
          · rw [List.map_map, ← ih, List.map_map]
            apply List.map_congr_left
            intro c hc
            simpa using commonRootCellDegree_lift
              (cellCatalog_valid M (a - 1) (b - 1) c hc) true true
          · rfl
      · split_ifs
        · rw [List.map_map, ← ih, List.map_map]
          apply List.map_congr_left
          intro c hc
          simpa using commonRootCellDegree_lift
            (cellCatalog_valid M (a - 1) b c hc) true false
        · rfl

/-- There exists a core coefficient flag satisfying the common-root identity on every cell. -/
theorem coreCellFlag_commonRoot_exists (a b c : ℕ) :
    ∃ F : CoreCellFlag a b c, ∀ i (hi : i < (coreCellCatalog a b c).length),
      Polynomial.C (F.generator i) * X ^ ((coreCellCatalog a b c)[i].2 \
        (coreCellCatalog a b c)[i].1).card ∈
          (F.ideal i).map Polynomial.C ⊔ grassmannianCommonRootIdeal (a + b + c) (a + b) a := by
  have hc := commonRootCellChain (a + b + c) (a + b) a (by omega) (by omega)
  rw [← commonRootCellDegrees_catalog] at hc
  obtain ⟨σ, I, hfirst, hlast, hstep, hunion, hcommon⟩ := hc.export
  simp only [List.length_map] at hlast hstep hunion hcommon
  have hu : ∀ i < (coreCellCatalog a b c).length,
      Polynomial.C (σ i) * X ^ coreCellCutoff a b c i ∈
        (I i).map Polynomial.C ⊔ S_relationIdeal (a + b + c) (a + b) a := by
    intro i hi
    have he := hunion i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at he
    rw [coreCellCutoff, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    exact he
  refine ⟨⟨σ, I, hfirst, hlast, hstep, hu⟩, ?_⟩
  intro i hi
  have he := hcommon i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at he
  exact he

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootCellChain_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootCellChain
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootCellDegree_lift
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootCellDegrees_catalog
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellFlag_commonRoot_exists

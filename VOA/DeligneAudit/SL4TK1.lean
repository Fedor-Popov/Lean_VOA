import VOA.DeligneAudit.SL4TFlagPieces

/-! # The recursive spanning form of K1 -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- Cell cutoffs, ordered by the last site as `nn < ng < both < gn`. -/
def cellLevels : ℕ → ℕ → ℕ → List ℕ
  | 0, a, b => if a = 0 ∧ b = 0 then [0] else []
  | M + 1, a, b =>
      (if a ≤ M ∧ b ≤ M then cellLevels M a b else []) ++
      (if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
        (cellLevels M a (b - 1)).map (fun n => n + 1) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
        (cellLevels M (a - 1) (b - 1)).map (fun n => n + 1) else []) ++
      (if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
        (cellLevels M (a - 1) b).map (fun n => n + 1) else [])

theorem S_zero_algebraMap_surjective (M : ℕ) :
    Function.Surjective (algebraMap ℂ (S M 0 0)) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hX (v : Bool × ℕ) :
      Ideal.Quotient.mk (biGrassIdeal 0 (M - 0) 0 (M - 0)) (MvPolynomial.X v) = 0 := by
    rcases v with ⟨s, i⟩
    cases s with
    | false =>
        simpa only [leftE, eClass, biLeft_mk, elementary_succ, alphabetIn,
          MvPolynomial.rename_X] using leftE_eq_zero M 0 0 (i + 1) (by omega)
    | true =>
        simpa only [rightE, eClass, biRight_mk, elementary_succ, alphabetIn,
          MvPolynomial.rename_X] using rightE_eq_zero M 0 0 (i + 1) (by omega)
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨c, rfl⟩
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      exact ⟨c + d, by rw [map_add, map_add, hc, hd]⟩
  | mul_X p v hp => exact ⟨0, by rw [map_zero, map_mul, hX, mul_zero]⟩

theorem S_zero_span_one (M : ℕ) : (ℂ ∙ (1 : S M 0 0)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨c, rfl⟩ := S_zero_algebraMap_surjective M x
  exact Submodule.mem_span_singleton.mpr ⟨c, by simp [Algebra.smul_def]⟩

theorem spanningChain_zero : SpanningChain (S_relationIdeal 0 0 0) ⊥ ⊤ [0] := by
  refine .cons 1 0 ?_ ?_ (.nil ⊤)
  · simp only [Submodule.restrictScalars_top, Submodule.restrictScalars_bot,
      bot_sup_eq, S_zero_span_one]
  · simp only [map_one, pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    exact relationIdeal_power (leftP 0 0 0) (rightP 0 0 0) 0

theorem thomI2_top_left (M b : ℕ) (hM : 0 < M) : thomI2 M M b = ⊥ := by
  rw [thomI2, leftE_top M b hM, Ideal.span_singleton_zero]

theorem thomI3_zero_right (M a : ℕ) (hM : 0 < M) : thomI3 M a 0 = thomI2 M a 0 := by
  change thomI2 M a 0 ⊔ Ideal.span {rightH M a 0 M} = thomI2 M a 0
  rw [rightH_empty M a hM, Ideal.span_singleton_zero, sup_bot_eq]

/-- K1's ideal flag with its recursively ordered list of cell cutoffs. -/
theorem k1_recursive (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    SpanningChain (S_relationIdeal M a b) ⊥ ⊤ (cellLevels M a b) := by
  induction M generalizing a b with
  | zero =>
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst a
      subst b
      simpa only [cellLevels, and_self, if_true] using spanningChain_zero
  | succ M ih =>
      have hnn : SpanningChain (S_relationIdeal (M + 1) a b) ⊥ (thomI1 (M + 1) a b)
          (if a ≤ M ∧ b ≤ M then cellLevels M a b else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            flagPiece_nn (M + 1) a b (by omega) (by omega) (ih a b h.1 h.2)
        · have heq : thomI1 (M + 1) a b = ⊥ := by
            by_cases haM : a = M + 1
            · subst a
              exact thomI1_top_left _ _ (by omega)
            · have hbM : b = M + 1 := by omega
              subst b
              exact thomI1_top_right _ _ (by omega)
          rw [heq]
          exact .nil _
      have hng : SpanningChain (S_relationIdeal (M + 1) a b)
          (thomI1 (M + 1) a b) (thomI2 (M + 1) a b)
          (if a ≤ M ∧ 0 < b ∧ b ≤ M + 1 then
            (cellLevels M a (b - 1)).map (fun n => n + 1) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            flagPiece_ng (M + 1) a b (by omega) hb h.2.1 (ih a (b - 1) h.1 (by omega))
        · have heq : thomI1 (M + 1) a b = thomI2 (M + 1) a b := by
            by_cases hb0 : b = 0
            · subst b
              exact thomI1_zero_right _ _
            · have haM : a = M + 1 := by omega
              subst a
              rw [thomI1_top_left _ _ (by omega), thomI2_top_left _ _ (by omega)]
          rw [heq]
          exact .nil _
      have hboth : SpanningChain (S_relationIdeal (M + 1) a b)
          (thomI2 (M + 1) a b) (thomI3 (M + 1) a b)
          (if 0 < a ∧ a ≤ M + 1 ∧ 0 < b ∧ b ≤ M + 1 then
            (cellLevels M (a - 1) (b - 1)).map (fun n => n + 1) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            flagPiece_both (M + 1) a b ha hb h.1 h.2.2.1
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
      have hgn : SpanningChain (S_relationIdeal (M + 1) a b) (thomI3 (M + 1) a b) ⊤
          (if 0 < a ∧ a ≤ M + 1 ∧ b ≤ M then
            (cellLevels M (a - 1) b).map (fun n => n + 1) else []) := by
        split_ifs with h
        · simpa only [Nat.add_sub_cancel] using
            flagPiece_gn (M + 1) a b ha h.1 (by omega) (ih (a - 1) b (by omega) h.2.2)
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

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.S_zero_algebraMap_surjective
#print axioms VOA.DeligneAudit.SL4T.S_zero_span_one
#print axioms VOA.DeligneAudit.SL4T.spanningChain_zero
#print axioms VOA.DeligneAudit.SL4T.thomI2_top_left
#print axioms VOA.DeligneAudit.SL4T.thomI3_zero_right
#print axioms VOA.DeligneAudit.SL4T.k1_recursive

import VOA.DeligneAudit.D4LevelReductionTail

/-! Descending high-mode elimination by a Levi Cartan current. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

theorem radicalPrefix_current (spectators : List (Fin 6 × ℕ))
    (j : Fin 6) (s : ℕ) (v : V) :
    pairRadicalOp ρ spectators (ρ.op (radicalColour j) s v) =
      pairRadicalOp ρ (spectators ++ [(j, s)]) v := by
  simp only [pairRadicalOp_apply, radicalWord, List.map_append, wordOp_append,
    List.map_singleton, wordOp]

theorem radicalPrefix_word (spectators suffix : List (Fin 6 × ℕ)) :
    pairRadicalOp ρ spectators (radicalWord ρ w suffix) =
      radicalWord ρ w (spectators ++ suffix) := by
  simp only [pairRadicalOp_apply, radicalWord, List.map_append, wordOp_append]

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- Modulo larger highest-root modes, a high Cartan current counts zero-mode letters. -/
theorem cartan_high_radical_spectators (q : V →ₗ[ℂ] W) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (hmr : m ≤ r)
    (hhigher : ∀ s, r < s → ∀ l : List (Fin 6 × ℕ),
      q (radicalWord ρ w ((5, s) :: l)) = 0)
    (suffix spectators : List (Fin 6 × ℕ)) :
    q (pairRadicalOp ρ ((5, 0) :: spectators)
        (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
          (radicalWord ρ w suffix))) =
      -(suffix.count (5, 0) : ℂ) •
        q (radicalWord ρ w ((5, r) :: spectators ++ suffix)) := by
  induction suffix generalizing spectators with
  | nil =>
      simp only [radicalWord, List.map_nil, wordOp]
      rw [source_cartan_pos ρ w m h 1 r hr]
      simp
  | cons a suffix ih =>
      rcases a with ⟨j, s⟩
      have hshift :
          q (pairRadicalOp ρ ((5, 0) :: spectators)
            (ρ.op (radicalColour j) (r + s) (radicalWord ρ w suffix))) =
          if j = 5 ∧ s = 0 then
            q (radicalWord ρ w ((5, r) :: spectators ++ (j, s) :: suffix)) else 0 := by
        rw [radicalPrefix_current, radicalPrefix_word]
        by_cases hj : j = 5
        · subst j
          by_cases hs : s = 0
          · subst s
            simp only [and_self, if_true, Nat.add_zero]
            congr 1
            apply radicalWord_perm ρ w
            simpa only [List.cons_append, List.singleton_append, List.append_assoc] using
              ((List.perm_middle.cons (5, 0)).trans
                ((List.Perm.swap (5, r) (5, 0) (spectators ++ suffix)).trans
                  (List.perm_middle.cons (5, r)).symm))
          · simp only [hs, and_false, if_false]
            have hp :
                ((((5, 0) :: spectators) ++ [(5, r + s)]) ++ suffix).Perm
                  ((5, r + s) :: (5, 0) :: spectators ++ suffix) := by
              simpa only [List.append_assoc, List.singleton_append,
                List.cons_append] using
                (List.perm_middle (a := (5, r + s))
                  (l₁ := (5, 0) :: spectators) (l₂ := suffix))
            rw [radicalWord_perm ρ w hp]
            exact hhigher (r + s) (by omega) _
        · simp only [hj, false_and, if_false]
          rw [radical_word_high_zero ρ w m h]
          · exact map_zero q
          · refine ⟨(j, r + s), ?_, ?_⟩
            · simp
            · have hcolour : radicalColour j ≠ 27 := by
                fin_cases j <;> simp_all [radicalColour]
              simp only [rootModeBound, hcolour, if_false]
              omega
      change q (pairRadicalOp ρ ((5, 0) :: spectators)
        (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
          (ρ.op (radicalColour j) s (radicalWord ρ w suffix)))) = _
      rw [sub_eq_iff_eq_add.mp (cartan_radical_comm ρ 1 j r s _)]
      rw [map_add, map_add, map_smul, map_smul, hshift,
        radicalPrefix_current]
      simp only [List.cons_append]
      rw [ih]
      simp only [List.cons_append, List.append_assoc, List.singleton_append]
      by_cases hj : j = 5
      · subst j
        by_cases hs : s = 0
        · subst s
          simp [letterWeight, keyLabel, wordKey, List.count_cons_self,
            add_smul, neg_add, sub_smul]
        · simp [hs, List.count_cons, show (5, s) ≠ (5, 0) by simp [hs]]
      · simp [hj, List.count_cons, show (j, s) ≠ (5, 0) by simp [hj]]

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.radicalPrefix_current
#print axioms VOA.DeligneAudit.D4LevelReduction.radicalPrefix_word
#print axioms VOA.DeligneAudit.D4LevelReduction.cartan_high_radical_spectators

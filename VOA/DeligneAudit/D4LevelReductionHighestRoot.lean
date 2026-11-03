import VOA.DeligneAudit.D4LevelReductionDescent

/-! High highest-root words belong to the Levi truncation image. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Descending from mode `2m` eliminates every high highest-root radical word. -/
theorem highestRoot_radical_mem_leviTail (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : N ≤ r) (l : List (Fin 6 × ℕ)) :
    radicalWord ρ w ((5, r) :: l) ∈ leviCurrentTail ρ w N := by
  let q := (leviCurrentTail ρ w N).mkQ
  suffices hall : ∀ d r, 2 * m - r = d → N ≤ r →
      ∀ l : List (Fin 6 × ℕ), q (radicalWord ρ w ((5, r) :: l)) = 0 by
    exact (Submodule.Quotient.mk_eq_zero _).mp (hall _ r rfl hr l)
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro r hd hr l
      by_cases htop : 2 * m ≤ r
      · rw [radical_word_high_zero ρ w m h]
        · exact map_zero q
        · exact ⟨(5, r), by simp, by simpa [rootModeBound, radicalColour] using htop⟩
      have hhigher : ∀ s, r < s → ∀ t : List (Fin 6 × ℕ),
          q (radicalWord ρ w ((5, s) :: t)) = 0 := by
        intro s hs t
        exact ih (2 * m - s) (by omega) s rfl (by omega) t
      have hcart : q (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
          (radicalWord ρ w ((5, 0) :: l))) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact currentTail_contains ρ _ _ N
          (leviColour_isLevi _) hr (wordOp_mem_cycSubG ρ w _)
      have hcount := cartan_high_radical_spectators ρ w q m h r
        (by omega) (by omega) hhigher l []
      have hcomm := congrArg q
        (sub_eq_iff_eq_add.mp
          (cartan_radical_comm ρ 1 5 r 0 (radicalWord ρ w l)))
      change q (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
          (radicalWord ρ w ((5, 0) :: l))) = _ at hcomm
      rw [hcart, map_add, map_smul] at hcomm
      change q (ρ.op (radicalColour 5) 0
        (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
          (radicalWord ρ w l))) = _ at hcount
      rw [hcount] at hcomm
      have hz : (-(1 + (l.count (5, 0) : ℂ))) •
          q (radicalWord ρ w ((5, r) :: l)) = 0 := by
        simpa [letterWeight, keyLabel, wordKey, neg_add, add_smul,
          radicalWord, wordOp, add_comm] using hcomm.symm
      have hne : (1 + (l.count (5, 0) : ℂ)) ≠ 0 := by
        exact_mod_cast (show 1 + l.count (5, 0) ≠ 0 by omega)
      exact (smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hne)

/-- Above mode `m`, only the highest negative root can act on the generator. -/
theorem source_high_current_zero (m : ℕ) (hm : 1 ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (c : Fin 28) (hc : c ≠ 27) (r : ℕ) (hr : m ≤ r) : ρ.op c r w = 0 := by
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  by_cases hcart : c.val < 4
  · exact rs_cartan_pos hs hcart r (by omega)
  by_cases hraise : c.val < 16
  · exact rs_raising hs (by change 4 ≤ c.val ∧ c.val < 16; omega) r
  exact source_root_mode_zero ρ w m h c (by omega) r
    (by simpa [rootModeBound, hc] using hr)

/-- The positive radical kills a high highest-root vector. -/
theorem positive_radical_highestRoot_zero (m : ℕ) (hm : 1 ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : m ≤ r) (a : Fin 28) (s : ℕ) (ha : IsPositive a) :
    ρ.op a s (ρ.op (27 : Fin 28) r w) = 0 := by
  obtain ⟨i, rfl⟩ := ha
  have hs : Sat D4sector.f ρ w (ravSpec D4sector m (2 * m)) := by
    simpa [ravFam] using h
  have hraise : D4sector.raising (positiveColour i) := by
    change 4 ≤ (positiveColour i).val ∧ (positiveColour i).val < 16
    fin_cases i <;> decide
  rw [sub_eq_iff_eq_add.mp (ρ.comm (positiveColour i) (27 : Fin 28) s r w),
    rs_raising hs hraise s, map_zero, add_zero]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c = (27 : Fin 28)
  · subst c
    have hz : D4sector.f (positiveColour i) (27 : Fin 28) (27 : Fin 28) = 0 := by
      have hi : VOA.DeligneAudit.DeligneSector.Sparse.sget
          (br (positiveColour i) 27) 27 = 0 := by
        fin_cases i <;> decide
      simpa [D4sector, fD4,
        VOA.DeligneAudit.DeligneSector.Sparse.fC,
        VOA.DeligneAudit.DeligneSector.Sparse.fZ] using
          congrArg (fun n : ℤ => (n : ℂ)) hi
    rw [hz, zero_smul]
  · rw [source_high_current_zero ρ w m hm h c hc (s + r) (by omega), smul_zero]

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.highestRoot_radical_mem_leviTail
#print axioms VOA.DeligneAudit.D4LevelReduction.source_high_current_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.positive_radical_highestRoot_zero

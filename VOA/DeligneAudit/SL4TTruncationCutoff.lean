import VOA.DeligneAudit.SL4TMixedLabelUniversal

/-! The single-mode and current-ideal presentations of truncated local Weyl modules agree. -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

/-- Vanishing at the cutoff implies vanishing at every higher current mode. -/
theorem current_cutoff_of_single_mode {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (weight : Fin 3 → ℕ) (M : ℕ)
    (h : LocalWeylRel ρ w weight) (hcut : ∀ x, ρ.op x M w = 0) :
    ∀ x s, M ≤ s → ρ.op x s w = 0 := by
  intro x s hs
  by_cases he : s = M
  · subst s
    exact hcut x
  have hpos : 0 < s := by omega
  by_cases hx : x.val < 6
  · exact h.raising x hx s
  by_cases hh : 12 ≤ x.val
  · have hc : x = 12 ∨ x = 13 ∨ x = 14 := by omega
    rcases hc with rfl | rfl | rfl
    · exact h.cartan_pos 0 s hpos
    · exact h.cartan_pos 1 s hpos
    · exact h.cartan_pos 2 s hpos
  let i : Fin 3 := if x = 11 then 1 else 0
  let k : ℤ := if x = 6 then -2 else if x = 7 ∨ x = 8 then -1 else 1
  have hk : (k : ℂ) ≠ 0 := by
    dsimp [k]
    split_ifs <;> norm_num
  have ht (z : Fin 15) : bracketTable (simpleH i) x z =
      if z = x then (k : ℂ) else 0 := by
    have hz : bracketInt (simpleH i) x z = if z = x then k else 0 := by
      fin_cases x <;> simp at hx hh
      all_goals fin_cases z <;> decide
    simp only [bracketTable, hz, Int.cast_ite, Int.cast_zero]
  have hc := ρ.comm (simpleH i) x (s - M) M w
  rw [hcut, h.cartan_pos i (s - M) (by omega), map_zero, map_zero, sub_self] at hc
  simp only [ht, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Nat.sub_add_cancel hs] at hc
  exact (smul_eq_zero.mp hc.symm).resolve_left hk

/-- The universal presentation is exactly local Weyl relations plus the cutoff mode. -/
theorem truncatedWeylSpec_sat_iff_cutoff {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (weight : Fin 3 → ℕ) (M : ℕ) :
    UnivG.Sat bracketTable ρ w (truncatedWeylSpec weight M) ↔
      LocalWeylRel ρ w weight ∧ ∀ x, ρ.op x M w = 0 := by
  rw [truncatedWeylSpec_sat_iff]
  exact ⟨fun h => ⟨h.1, fun x => h.2 x M le_rfl⟩,
    fun h => ⟨h.1, current_cutoff_of_single_mode ρ w weight M h.1 h.2⟩⟩

/-- The mixed-label target stated only with the requested generator cutoff relations. -/
theorem mixedLabelTruncatedRank_iff_generator_cutoff : MixedLabelTruncatedRank ↔
    ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule bracketTable V) (w : V),
      LocalWeylRel ρ w (weightABC a b a) →
      (∀ x, ρ.op x (a + b) w = 0) →
      FiniteDimensional ℂ (UnivG.cycSubG ρ w) ∧
        Module.finrank ℂ (UnivG.cycSubG ρ w) ≤ 15 ^ a * 6 ^ b := by
  rw [mixedLabelTruncatedRank_iff_cyclic]
  constructor
  · intro h a b V _ _ ρ w hw ht
    exact h a b V ρ w hw (current_cutoff_of_single_mode ρ w _ _ hw ht)
  · intro h a b V _ _ ρ w hw ht
    exact h a b V ρ w hw (fun x => ht x (a + b) le_rfl)

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.current_cutoff_of_single_mode
#print axioms VOA.DeligneAudit.SL4T.truncatedWeylSpec_sat_iff_cutoff
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank_iff_generator_cutoff

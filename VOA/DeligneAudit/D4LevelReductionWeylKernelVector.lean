import VOA.DeligneAudit.D4LevelReductionWeylRootModes

/-! The highest-root kernel vector of a consecutive truncation of a local Weyl module. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- At the next-to-top quadratic degree only the two top adjacent modes survive. -/
theorem commutingModes_top_adjacent_zero (F : ℕ → Module.End ℂ V)
    (hFF : ∀ r s, F r * F s = F s * F r) (v : V) (n : ℕ)
    (ht : ∀ s, n + 2 ≤ s → F s v = 0)
    (hq : ∑ x ∈ Finset.antidiagonal (2 * n + 1), F x.1 (F x.2 v) = 0) :
    F n (F (n + 1) v) = 0 := by
  classical
  let t : Finset (ℕ × ℕ) := {(n, n + 1), (n + 1, n)}
  have hc (r s : ℕ) : F r (F s v) = F s (F r v) :=
    congrArg (fun T : Module.End ℂ V => T v) (hFF r s)
  have htmem : t ⊆ Finset.antidiagonal (2 * n + 1) := by
    intro x hx
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_antidiagonal] <;> omega
  have he : (∑ x ∈ t, F x.1 (F x.2 v)) =
      ∑ x ∈ Finset.antidiagonal (2 * n + 1), F x.1 (F x.2 v) := by
    apply Finset.sum_subset htmem
    intro x hx hnot
    have hxsum := Finset.mem_antidiagonal.mp hx
    have hlarge : n + 2 ≤ x.1 ∨ n + 2 ≤ x.2 := by
      by_contra hn
      have hfirst : ¬ n + 2 ≤ x.1 := fun h => hn (Or.inl h)
      have hsecond : ¬ n + 2 ≤ x.2 := fun h => hn (Or.inr h)
      apply hnot
      simp only [t, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      omega
    rcases hlarge with hfirst | hsecond
    · rw [hc, ht x.1 hfirst, map_zero]
    · rw [ht x.2 hsecond, map_zero]
  have hne : (n, n + 1) ≠ (n + 1, n) := by
    intro heq
    have := congrArg Prod.fst heq
    omega
  simp only [t, Finset.sum_pair hne] at he
  rw [hc (n + 1) n, hq] at he
  have hz : (2 : ℂ) • F n (F (n + 1) v) = 0 := by
    simpa only [two_smul] using he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

variable [FiniteDimensional ℂ V]
variable (Q : CurrentModule bracketTable V) (v : V) (a b n : ℕ)
variable (hw : LocalWeylRel Q v (weightABC a b a))
variable (ha : 1 ≤ a) (hn : a + b ≤ n + 1)
variable (ht : ∀ e s, n + 2 ≤ s → Q.op e s v = 0)

include hw hn

/-- All positive currents annihilate the last retained highest-root descendant. -/
theorem sl4Highest_descendant_raising (e : Fin 15) (he : e.val < 6) (r : ℕ) :
    Q.op e r (Q.op 8 (n + 1) v) = 0 := by
  have htable : ∀ e : Fin 15, e.val < 6 → bracketInt e 8 8 = 0 := by
    decide +kernel
  have hc := Q.comm e 8 r (n + 1) v
  rw [hw.raising e he r, map_zero, sub_zero] at hc
  rw [hc]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = 8
  · subst k
    simp [bracketTable, htable e he]
  · rw [sl4_nonHighest_mode_zero Q v a b hw k hk _ (by omega), smul_zero]

omit hn
include hw ht

omit [FiniteDimensional ℂ V] in
/-- Positive Cartan modes annihilate the last retained highest-root descendant. -/
theorem sl4Highest_descendant_cartan (i : Fin 3) (r : ℕ) (hr : 0 < r) :
    Q.op (simpleH i) r (Q.op 8 (n + 1) v) = 0 := by
  have hc := Q.comm (simpleH i) 8 r (n + 1) v
  rw [hw.cartan_pos i r hr, map_zero, sub_zero] at hc
  rw [hc]
  apply Finset.sum_eq_zero
  intro k _
  rw [ht k _ (by omega), smul_zero]

omit ht
include hw ha

omit [FiniteDimensional ℂ V] in
/-- The last retained highest-root descendant has both outer labels reduced by one. -/
theorem sl4Highest_descendant_weight (i : Fin 3) :
    Q.op (simpleH i) 0 (Q.op 8 (n + 1) v) =
      (weightABC (a - 1) b (a - 1) i : ℂ) • Q.op 8 (n + 1) v := by
  have htable : ∀ i : Fin 3, ∀ k : Fin 15, bracketTable (simpleH i) 8 k =
      if k = 8 then (if i = 1 then 0 else -1) else 0 := by
    have hi : ∀ i : Fin 3, ∀ k : Fin 15, bracketInt (simpleH i) 8 k =
        if k = 8 then (if i = 1 then 0 else -1) else 0 := by decide +kernel
    unfold bracketTable
    exact_mod_cast hi
  have hc := Q.comm (simpleH i) 8 0 (n + 1) v
  rw [hw.cartan_zero, map_smul, sub_eq_iff_eq_add] at hc
  rw [hc]
  simp only [htable, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Nat.zero_add]
  have ha' : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  fin_cases i <;> simp [weightABC, ha', sub_smul] <;> module

include hw ha hn ht

/-- The last retained highest-root descendant satisfies the smaller local Weyl presentation. -/
theorem sl4Highest_descendant_localWeyl :
    LocalWeylRel Q (Q.op 8 (n + 1) v) (weightABC (a - 1) b (a - 1)) := by
  refine ⟨sl4Highest_descendant_raising Q v a b n hw hn,
    sl4Highest_descendant_cartan Q v a b n hw ht,
    sl4Highest_descendant_weight Q v a b n hw ha, ?_⟩
  intro i
  exact coreFinite_simple_lowering Q _ i _
    (sl4Highest_descendant_raising Q v a b n hw hn _ (simpleE_raising i) 0)
    (sl4Highest_descendant_weight Q v a b n hw ha i)

/-- Quadratic Garland improves the descendant cutoff by two relative to its parent module. -/
theorem sl4Highest_descendant_cutoff (hquad : 2 * a + b + 1 ≤ 2 * n + 3)
    (e : Fin 15) : Q.op e n (Q.op 8 (n + 1) v) = 0 := by
  by_cases he : e = 8
  · subst e
    apply commutingModes_top_adjacent_zero (Q.op 8)
      (coreHighest_currentRelations Q).hFF v n (ht 8)
    exact sl4Highest_quadratic_relation Q v a b hw (2 * n + 1) (by omega)
  · exact sl4_nonHighest_mode_zero Q _ (a - 1) b
      (sl4Highest_descendant_localWeyl Q v a b n hw ha hn ht) e he n (by omega)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.commutingModes_top_adjacent_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_descendant_raising
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_descendant_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_descendant_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_descendant_localWeyl
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4Highest_descendant_cutoff

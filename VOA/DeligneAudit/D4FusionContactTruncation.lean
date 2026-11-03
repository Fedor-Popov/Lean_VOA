import VOA.DeligneAudit.D4FusionContactTruncationTable
import VOA.DeligneAudit.D4FusionContactSector
import VOA.DeligneAudit.D4FusionContactSource

/-!
# Actual D₄ current truncation and multiplicity-one degree reduction

The source fusion relations imply that every current mode at least m
kills the whole cyclic module. Combined with contact PBW, only nine
colors in modes below m remain. At m=1 every positive degree vanishes,
and degree zero lies in the contact length-two piece.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem negative_high_zero (h : HighestRel R w m)
    (hf : ∀ i, R.op (negativeIndex i) m w = 0)
    (i : Fin 12) (r : ℕ) (hr : m ≤ r) : R.op (negativeIndex i) r w = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = m + k := ⟨r - m, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hf i
  have hc := R.comm (negativeCartan i) (negativeIndex i) k m w
  rw [hf i, map_zero, h.cartan_pos _ (negativeCartan_lt_four i) k hk,
    map_zero, sub_zero] at hc
  have hs : (∑ c : Fin 28, contactF (negativeCartan i) (negativeIndex i) c •
      R.op c (k + m) w) = (negativeWeight i : ℂ) • R.op (negativeIndex i) (m + k) w := by
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, add_comm k m]
  rw [hs] at hc
  exact (smul_eq_zero.mp hc.symm).resolve_left (negativeWeight_ne_zero i)

theorem high_kills_generator (hm : 1 ≤ m) (h : HighestRel R w m)
    (hf : ∀ i, R.op (negativeIndex i) m w = 0) :
    ∀ (c : Fin 28) r, m ≤ r → R.op c r w = 0 := by
  intro c r hr
  by_cases hh : c.val < 4
  · exact h.cartan_pos c hh r (by omega)
  by_cases he : c.val < 16
  · exact h.raising c (by omega) r
  obtain ⟨i, rfl⟩ := negativeIndex_covers c (by omega)
  exact negative_high_zero h hf i r hr

theorem contact_truncIdeal (m : ℕ) : IsLoopIdeal contactF (fun _ r => m ≤ r) :=
  fun _ _ h _ _ _ _ => le_trans h (Nat.le_add_right _ _)

variable {R : CurrentModule D4sector.f V}

theorem localWeyl_high_kills (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    ∀ (c : Fin 28) r, m ≤ r → R.op c r w = 0 := by
  apply high_kills_generator hm (highestRel_of_localWeyl h)
  intro i
  exact h.fusion (negativeIndex i) (negativeIndex_range i)

theorem localWeyl_high_kills_word (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (l : List (Fin 28 × ℕ)) (c : Fin 28) (r : ℕ) (hr : m ≤ r) :
    R.op c r (wordOp R l w) = 0 :=
  op_wordOp_of_ideal R (contact_truncIdeal m) (localWeyl_high_kills hm h) l c r hr

/-- Actual finite-current, nine-color sorted spanning, for every m≥1. -/
theorem localWeyl_cycDeg_contact_truncated (hm : 1 ≤ m)
    (h : LocalWeylRelG D4sector R w m) (d : ℕ) :
    cycDeg R w d ≤ Submodule.span ℂ {u | ∃ l : List (Fin 28 × ℕ),
      l.IsChain (fun a b => contactKey a ≤ contactKey b) ∧
      (∀ x ∈ l, active x.1) ∧ (∀ x ∈ l, x.2 < m) ∧
      VOA.DeligneAudit.SectorGraded.wordDeg l = d ∧ u = wordOp R l w} := by
  apply (localWeyl_cycDeg_contact h d).trans
  rw [Submodule.span_le]
  rintro _ ⟨l, hsort, ha, hd, rfl⟩
  by_cases ht : ∀ x ∈ l, x.2 < m
  · exact Submodule.subset_span ⟨l, hsort, ha, ht, hd, rfl⟩
  · push Not at ht
    rw [wordOp_eq_zero_of_mem R (contact_truncIdeal m) (localWeyl_high_kills hm h) l ht]
    exact Submodule.zero_mem _

private theorem word_indices : ∀ (l : List (Fin 28 × ℕ)),
    (∀ x ∈ l, active x.1) → (∀ x ∈ l, x.2 < 1) →
    ∃ t : List (Fin 9), l = t.map (fun i => (radIndex i, 0))
  | [], _, _ => ⟨[], rfl⟩
  | (c, r) :: l, ha, ht => by
      obtain ⟨i, hi⟩ := (active_iff_index c).mp (ha (c,r) (by simp))
      have hr : r = 0 := by have := ht (c,r) (by simp); dsimp at this; omega
      obtain ⟨t, htl⟩ := word_indices l (fun x hx => ha x (by simp [hx]))
        (fun x hx => ht x (by simp [hx]))
      exact ⟨i :: t, by simp only [List.map_cons, ← hi, hr, ← htl]⟩

private theorem word_degree_zero : ∀ (l : List (Fin 28 × ℕ)),
    (∀ x ∈ l, x.2 < 1) → VOA.DeligneAudit.SectorGraded.wordDeg l = 0
  | [], _ => rfl
  | (c,r) :: l, ht => by
      have hr : r = 0 := by have := ht (c,r) (by simp); dsimp at this; omega
      have hl := word_degree_zero l (fun x hx => ht x (by simp [hx]))
      simpa [VOA.DeligneAudit.SectorGraded.wordDeg, hr] using hl

/-- Every positive current degree of the actual m=1 source is zero. -/
theorem localWeyl_one_cycDeg_eq_bot (h : LocalWeylRelG D4sector R w 1)
    (d : ℕ) (hd : 1 ≤ d) : cycDeg R w d = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply (localWeyl_cycDeg_contact_truncated (by omega) h d).trans
  rw [Submodule.span_le]
  rintro _ ⟨l, _, _, ht, hdeg, _⟩
  have hz := word_degree_zero l ht
  omega

/-- The entire surviving degree lies in the actual contact length-two piece. -/
theorem localWeyl_one_cycDeg_le_piece (h : LocalWeylRelG D4sector R w 1) :
    cycDeg R w 0 ≤ piece R w 2 := by
  apply (localWeyl_cycDeg_contact_truncated (by omega) h 0).trans
  rw [Submodule.span_le]
  rintro _ ⟨l, _, ha, ht, _, rfl⟩
  obtain ⟨t, rfl⟩ := word_indices l ha ht
  exact localWeyl_radicalWord_two h t

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_cycDeg_contact_truncated
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_one_cycDeg_eq_bot
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_one_cycDeg_le_piece

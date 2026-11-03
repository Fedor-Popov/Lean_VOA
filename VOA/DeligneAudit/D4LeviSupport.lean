import VOA.DeligneAudit.D4LeviModes

/-! Mode support of every six-letter radical key. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem radical_ops_comm (i j : Fin 6) (r s : ℕ) (v : V) :
    ρ.op (radicalColour i) r (ρ.op (radicalColour j) s v) =
      ρ.op (radicalColour j) s (ρ.op (radicalColour i) r v) := by
  have hc := ρ.comm (radicalColour i) (radicalColour j) r s v
  have hz : (∑ e : Fin 28,
      D4sector.f (radicalColour i) (radicalColour j) e •
        ρ.op e (r + s) v) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    change fD4 (radicalColour i) (radicalColour j) e •
      ρ.op e (r + s) v = 0
    rw [radical_abelian]
    simp
  exact sub_eq_zero.mp (hc.trans hz)

theorem radical_op_word_comm (i : Fin 6) (r : ℕ)
    (l : List (Fin 6 × ℕ)) (v : V) :
    ρ.op (radicalColour i) r
      (wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) v) =
    wordOp ρ (l.map fun p => (radicalColour p.1, p.2))
      (ρ.op (radicalColour i) r v) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      simp only [List.map_cons, wordOp]
      rw [radical_ops_comm ρ i j r s, ih]

private theorem radical_word_zero (l : List (Fin 6 × ℕ)) :
    wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) (0 : V) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [List.map_cons, wordOp]
      rw [ih, map_zero]

theorem radical_word_high_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (l : List (Fin 6 × ℕ))
    (hl : ∃ p ∈ l, rootModeBound m (radicalColour p.1) ≤ p.2) :
    radicalWord ρ w l = 0 := by
  induction l with
  | nil => simp at hl
  | cons p l ih =>
      rcases p with ⟨i, s⟩
      obtain ⟨q, hq, hbound⟩ := hl
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        change ρ.op (radicalColour i) s
          (wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) w) = 0
        rw [radical_op_word_comm ρ i s l w,
          source_radical_mode_zero ρ w m h i s hbound]
        exact radical_word_zero ρ l
      · change ρ.op (radicalColour i) s (radicalWord ρ w l) = 0
        rw [ih ⟨q, hq, hbound⟩, map_zero]

private theorem sum_modes_le (B : ℕ) (l : List (Fin 6 × ℕ))
    (h : ∀ p ∈ l, p.2 < B) : (l.map Prod.snd).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hp : p.2 < B := h p (by simp)
      have ht : ∀ q ∈ l, q.2 < B := by
        intro q hq
        exact h q (by simp [hq])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := ih ht
      rw [Nat.succ_mul]
      omega

/-- A key of too large total mode degree has zero radical layer. -/
theorem keyLayer_eq_bot_of_degree_gt
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hk : 2 * m * keyDepth k < k.degree) :
    keyLayer ρ w k = ⊥ := by
  rw [keyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hkey, rfl⟩ := hz
  have hbad : ∃ p ∈ l, rootModeBound m (radicalColour p.1) ≤ p.2 := by
    by_contra hn
    have hall : ∀ p ∈ l, p.2 < 2 * m := by
      intro p hp
      have hnot : ¬ rootModeBound m (radicalColour p.1) ≤ p.2 := by
        intro hle
        exact hn ⟨p, hp, hle⟩
      have hroot : rootModeBound m (radicalColour p.1) ≤ 2 * m := by
        simp only [rootModeBound]
        split_ifs <;> omega
      omega
    have hs := sum_modes_le (2 * m) l hall
    have hlen : l.length = keyDepth k := by
      simpa [← hkey] using (wordKey_depth l).symm
    have hdegree : (l.map Prod.snd).sum = k.degree := by
      simpa [wordKey] using congrArg RadicalKey.degree hkey
    rw [hlen, hdegree] at hs
    rw [Nat.mul_comm (keyDepth k) (2 * m)] at hs
    omega
  rw [radical_word_high_zero ρ w m h l hbad]
  exact Submodule.zero_mem _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radical_ops_comm
#print axioms VOA.DeligneAudit.D4Levi.radical_op_word_comm
#print axioms VOA.DeligneAudit.D4Levi.radical_word_high_zero
#print axioms VOA.DeligneAudit.D4Levi.keyLayer_eq_bot_of_degree_gt

import VOA.DeligneAudit.SL4TStratumConfigurationRecursion

/-! # Symmetry and unrestricted counts of paired configurations -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Relabeling positions preserves the prescribed cardinality of every site fiber. -/
def fullFlagConfiguration_relabel (B k : ℕ) (e : Equiv.Perm (Fin B)) :
    FullFlagConfiguration B k ≃ FullFlagConfiguration B k where
  toFun f := ⟨fun i => f.val (e.symm i), by
    intro a
    calc
      _ = (Finset.univ.filter fun i => f.val i = a).card := by
        symm
        apply Finset.card_equiv e
        intro i
        simp
      _ = _ := f.property a⟩
  invFun f := ⟨fun i => f.val (e i), by
    intro a
    calc
      _ = (Finset.univ.filter fun i => f.val i = a).card := by
        symm
        apply Finset.card_equiv e.symm
        intro i
        simp
      _ = _ := f.property a⟩
  left_inv f := by apply Subtype.ext; funext i; simp
  right_inv f := by apply Subtype.ext; funext i; simp

/-- Permuting positions and the selected subalphabet preserves the double statistic. -/
theorem fullFlagDoublesIn_relabel (B k : ℕ) (Y : Finset (Fin B))
    (e : Equiv.Perm (Fin B)) (f : FullFlagConfiguration B k) :
    fullFlagDoublesIn (Y.map e.toEmbedding) (fullFlagConfiguration_relabel B k e f) =
      fullFlagDoublesIn Y f := by
  classical
  unfold fullFlagDoublesIn
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply and_congr_right
  intro ha
  constructor
  · intro h i hi
    have hs := h (e i) (by simpa [fullFlagConfiguration_relabel] using hi)
    simpa using hs
  · intro h i hi
    have hs := h (e.symm i) hi
    simpa using hs

/-- The configuration stratum is invariant under permutation of its positions. -/
def fullFlagStratumConfiguration_relabel (B k j : ℕ) (Y : Finset (Fin B))
    (e : Equiv.Perm (Fin B)) :
    FullFlagStratumConfiguration B k j Y ≃
      FullFlagStratumConfiguration B k j (Y.map e.toEmbedding) :=
  (fullFlagConfiguration_relabel B k e).subtypeEquiv (fun f => by
    rw [fullFlagDoublesIn_relabel])

/-- No selected set contains more than the total number of doubled labels. -/
theorem fullFlagDoublesIn_le (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) : fullFlagDoublesIn Y f ≤ k := by
  classical
  calc
    _ ≤ (Finset.univ.filter fun a : Fin (B - k) => a.val < k).card := by
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
    _ ≤ k := by rw [Fin.card_filter_val_lt]; exact min_le_right _ _

/-- A threshold larger than the total number of doubles imposes no configuration condition. -/
def fullFlagStratumConfiguration_allEquiv (B k j : ℕ) (Y : Finset (Fin B))
    (hj : k < j) : FullFlagStratumConfiguration B k j Y ≃ FullFlagConfiguration B k :=
  Equiv.subtypeUnivEquiv (fun f => lt_of_le_of_lt (fullFlagDoublesIn_le B k Y f) hj)

/-- The unrestricted configuration count satisfies the same deletion recursion. -/
theorem fullFlagConfiguration_card_recursion (B k : ℕ) (hk : 2 * k ≤ B + 1) :
    Nat.card (FullFlagConfiguration (B + 1) k) =
      k * Nat.card (FullFlagConfiguration B (k - 1)) +
        (B + 1 - k - k) * Nat.card (FullFlagConfiguration B k) := by
  have h := fullFlagStratumConfiguration_card_recursion B k (k + 1) ∅ hk
  rw [Nat.card_congr (fullFlagStratumConfiguration_allEquiv (B + 1) k (k + 1)
      ((∅ : Finset (Fin B)).map (Fin.succEmb B)) (by omega)),
    Nat.card_congr (fullFlagStratumConfiguration_allEquiv B (k - 1) (k + 1) ∅ (by omega)),
    Nat.card_congr (fullFlagStratumConfiguration_allEquiv B k (k + 1) ∅ (by omega))] at h
  exact h

/-- The empty configuration has exactly one labeling. -/
theorem fullFlagConfiguration_empty_card : Nat.card (FullFlagConfiguration 0 0) = 1 := by
  letI : Nonempty (FullFlagConfiguration 0 0) := ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩⟩
  exact Nat.card_unique

/-- The unrefined root-power recursion is bounded by the actual configuration count. -/
theorem fullFlag_finrank_le_configurations (B k : ℕ) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagRing B (B - k)) ≤ Nat.card (FullFlagConfiguration B k) := by
  induction B generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      rw [fullFlagConfiguration_empty_card]
      exact fullFlag_empty_rank_le 0
  | succ B ih =>
      let N := B + 1 - k
      have hN : 0 < N := by dsimp [N]; omega
      have hlen : B + 1 = N + k := by dsimp [N]; omega
      have hkN : k ≤ N := by dsimp [N]; omega
      have h := fullFlag_finrank_recursion B N k hN hlen hkN
      rw [fullFlagConfiguration_card_recursion B k hk]
      apply h.trans
      apply Nat.add_le_add
      · by_cases hk0 : k = 0
        · simp only [hk0, zero_mul, le_refl]
        · have hn : N = B - (k - 1) := by dsimp [N]; omega
          rw [hn]
          exact Nat.mul_le_mul_left k (ih (k - 1) (by omega))
      · by_cases hvalid : 2 * k ≤ B
        · have hn : N - 1 = B - k := by dsimp [N]; omega
          rw [hn]
          exact Nat.mul_le_mul_left (N - k) (ih k hvalid)
        · have hn : N - k = 0 := by dsimp [N]; omega
          change (N - k) * _ ≤ (N - k) * _
          rw [hn, zero_mul, zero_mul]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_relabel
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_relabel
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_relabel
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_le
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_allEquiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_card_recursion
#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_empty_card
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_le_configurations

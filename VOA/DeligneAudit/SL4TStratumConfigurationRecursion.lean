import VOA.DeligneAudit.SL4TStratumSingleDeletion

/-! # The two-term recursion for the number of full-flag stratum configurations -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Swapping labels in the same multiplicity class preserves that class. -/
theorem labelSwap_preserves_cutoff {N : ℕ} (k : ℕ) (a b : Fin N)
    (hab : a.val < k ↔ b.val < k) (c : Fin N) :
    (Equiv.swap a b c).val < k ↔ c.val < k := by
  classical
  by_cases hca : c = a
  · subst c
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hcb : c = b
  · subst c
    simpa only [Equiv.swap_apply_right] using hab
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- Every doubled-label deletion fiber has the smaller paired-configuration cardinality. -/
theorem deletedLabelStratumConfiguration_double_card (B N k j : ℕ)
    (Y : Finset (Fin B)) (hk : k < N) (a : Fin N) (ha : a.val < k + 1) :
    Nat.card (DeletedLabelStratumConfiguration B N (k + 1) j Y a) =
      Nat.card (LabelStratumConfiguration B N k j Y) := by
  classical
  let b : Fin N := ⟨k, hk⟩
  have he := labelSwap_preserves_cutoff (k + 1) a b (by simp only [b]; omega)
  have h := Nat.card_congr
    (deletedLabelStratumConfiguration_relabel B N (k + 1) j Y a (Equiv.swap a b) he)
  rw [Equiv.swap_apply_left] at h
  exact h.trans (Nat.card_congr
    (deletedLabelStratumConfiguration_doubleEquiv B N k j Y hk))

/-- Every single-label deletion fiber removes exactly one label. -/
theorem deletedLabelStratumConfiguration_single_card (B N k j : ℕ)
    (Y : Finset (Fin B)) (hk : k < N) (a : Fin N) (ha : k ≤ a.val) :
    Nat.card (DeletedLabelStratumConfiguration B N k j Y a) =
      Nat.card (LabelStratumConfiguration B (N - 1) k j Y) := by
  classical
  cases N with
  | zero => omega
  | succ N =>
      have he := labelSwap_preserves_cutoff k a (Fin.last N) (by simp only [Fin.val_last]; omega)
      have h := Nat.card_congr
        (deletedLabelStratumConfiguration_relabel B (N + 1) k j Y a
          (Equiv.swap a (Fin.last N)) he)
      rw [Equiv.swap_apply_left] at h
      exact h.trans (Nat.card_congr
        (deletedLabelStratumConfiguration_singleEquiv B N k j Y (by omega)))

/-- The double-site deletion fiber has precisely the original smaller configuration type. -/
theorem fullFlagDeletedConfiguration_double_card (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B + 1) (a : Fin (B + 1 - k)) (ha : a.val < k) :
    Nat.card (FullFlagDeletedConfiguration B k j Y a) =
      Nat.card (FullFlagStratumConfiguration B (k - 1) j Y) := by
  cases k with
  | zero => omega
  | succ k =>
      change Nat.card (DeletedLabelStratumConfiguration B (B + 1 - (k + 1))
        (k + 1) j Y a) = _
      rw [deletedLabelStratumConfiguration_double_card B _ k j Y (by omega) a ha]
      have h := Nat.card_congr (labelStratumConfiguration_equiv B k j Y)
      simpa only [show B + 1 - (k + 1) = B - k by omega, Nat.add_sub_cancel] using h

/-- The single-site deletion fiber has precisely the original smaller configuration type. -/
theorem fullFlagDeletedConfiguration_single_card (B k j : ℕ) (Y : Finset (Fin B))
    (a : Fin (B + 1 - k)) (ha : k ≤ a.val) :
    Nat.card (FullFlagDeletedConfiguration B k j Y a) =
      Nat.card (FullFlagStratumConfiguration B k j Y) := by
  change Nat.card (DeletedLabelStratumConfiguration B (B + 1 - k) k j Y a) = _
  rw [deletedLabelStratumConfiguration_single_card B _ k j Y (by omega) a ha]
  have h := Nat.card_congr (labelStratumConfiguration_equiv B k j Y)
  simpa only [show B + 1 - k - 1 = B - k by omega] using h

/-- Summing a constant weight over doubled and single labels gives their multiplicities. -/
theorem labelClasses_sum (N k d s : ℕ) (hk : k ≤ N) :
    (∑ a : Fin N, if a.val < k then d else s) = k * d + (N - k) * s := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_filter_val_lt, min_eq_right hk]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun a : Fin N => a.val < k)
  rw [Fin.card_filter_val_lt, min_eq_right hk, Finset.card_univ, Fintype.card_fin] at hc
  rw [show (Finset.univ.filter fun a : Fin N => ¬a.val < k).card = N - k by omega]
  simp only [Nat.cast_id]

/-- The selected-stratum count has the same two deletion coefficients as the algebra bound. -/
theorem fullFlagStratumConfiguration_card_recursion (B k j : ℕ) (Y : Finset (Fin B))
    (hk : 2 * k ≤ B + 1) :
    Nat.card (FullFlagStratumConfiguration (B + 1) k j (Y.map (Fin.succEmb B))) =
      k * Nat.card (FullFlagStratumConfiguration B (k - 1) j Y) +
        (B + 1 - k - k) * Nat.card (FullFlagStratumConfiguration B k j Y) := by
  rw [fullFlagStratumConfiguration_card_delete]
  calc
    _ = ∑ a : Fin (B + 1 - k), if a.val < k then
        Nat.card (FullFlagStratumConfiguration B (k - 1) j Y)
        else Nat.card (FullFlagStratumConfiguration B k j Y) := by
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs with hak
      · exact fullFlagDeletedConfiguration_double_card B k j Y hk a hak
      · exact fullFlagDeletedConfiguration_single_card B k j Y a (by omega)
    _ = _ := labelClasses_sum _ _ _ _ (by omega)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.labelSwap_preserves_cutoff
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_double_card
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_single_card
#print axioms VOA.DeligneAudit.SL4T.fullFlagDeletedConfiguration_double_card
#print axioms VOA.DeligneAudit.SL4T.fullFlagDeletedConfiguration_single_card
#print axioms VOA.DeligneAudit.SL4T.labelClasses_sum
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_card_recursion

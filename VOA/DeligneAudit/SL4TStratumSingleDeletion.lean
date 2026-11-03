import VOA.DeligneAudit.SL4TStratumLabelCount

/-! # Removing an empty label after deletion at a single site -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Appending an unused last label does not change the selected-double statistic. -/
theorem deletedConfigurationDoublesIn_castSucc {B N : ℕ} (k : ℕ)
    (Y : Finset (Fin B)) (g : Fin B → Fin N) (hk : k ≤ N) :
    deletedConfigurationDoublesIn k Y (Fin.last N) (fun i => (g i).castSucc) =
      configurationSelectedDoubles k Y g := by
  classical
  symm
  apply Finset.card_bij (fun b _ => b.castSucc)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨hb.1, Fin.castSucc_ne_last b, by simpa only [Fin.castSucc_inj] using hb.2⟩
  · intro a ha b hb hab
    exact Fin.castSucc_injective _ hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hbN : b.val < N := lt_of_lt_of_le hb.1 hk
    let a : Fin N := ⟨b.val, hbN⟩
    have ha : a.castSucc = b := Fin.ext rfl
    refine ⟨a, ?_, ha⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hb.1, ?_⟩
    intro i hi
    apply hb.2.2 i
    rw [hi, ha]

/-- The last single label is empty after its only position is deleted. -/
theorem deletedLabelStratumConfiguration_ne_last {B N k j : ℕ}
    (Y : Finset (Fin B)) (hk : k ≤ N)
    (f : DeletedLabelStratumConfiguration B (N + 1) k j Y (Fin.last N))
    (i : Fin B) : f.val i ≠ Fin.last N := by
  intro hi
  have h := f.property.1 (Fin.last N)
  change (Finset.univ.filter fun a => f.val a = Fin.last N).card +
    (if (Fin.last N) = Fin.last N then 1 else 0) = (if N < k then 2 else 1) at h
  simp only [ite_true, if_neg (Nat.not_lt.mpr hk)] at h
  have hz : (Finset.univ.filter fun a => f.val a = Fin.last N).card = 0 := by omega
  have hm : i ∈ Finset.univ.filter fun a => f.val a = Fin.last N := by simp [hi]
  rw [Finset.card_eq_zero.mp hz] at hm
  exact Finset.notMem_empty i hm

/-- Shrink the label set once its last fiber is empty. -/
def deletedLabelStratumConfiguration_shrink {B N k j : ℕ}
    (Y : Finset (Fin B)) (hk : k ≤ N)
    (f : DeletedLabelStratumConfiguration B (N + 1) k j Y (Fin.last N))
    (i : Fin B) : Fin N :=
  ⟨(f.val i).val, by
    have hn := deletedLabelStratumConfiguration_ne_last Y hk f i
    have hv := (f.val i).isLt
    have he : (f.val i).val ≠ N := fun h => hn (Fin.ext h)
    omega⟩

theorem deletedLabelStratumConfiguration_shrink_castSucc {B N k j : ℕ}
    (Y : Finset (Fin B)) (hk : k ≤ N)
    (f : DeletedLabelStratumConfiguration B (N + 1) k j Y (Fin.last N))
    (i : Fin B) : (deletedLabelStratumConfiguration_shrink Y hk f i).castSucc = f.val i :=
  Fin.ext rfl

/-- Deleting at the last single site removes that label from the remaining configuration. -/
def deletedLabelStratumConfiguration_singleEquiv (B N k j : ℕ)
    (Y : Finset (Fin B)) (hk : k ≤ N) :
    DeletedLabelStratumConfiguration B (N + 1) k j Y (Fin.last N) ≃
      LabelStratumConfiguration B N k j Y where
  toFun f := ⟨deletedLabelStratumConfiguration_shrink Y hk f, by
    constructor
    · intro b
      have hf : (Finset.univ.filter fun i =>
          deletedLabelStratumConfiguration_shrink Y hk f i = b) =
          (Finset.univ.filter fun i => f.val i = b.castSucc) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← deletedLabelStratumConfiguration_shrink_castSucc Y hk f i,
          Fin.castSucc_inj]
      rw [hf]
      have h := f.property.1 b.castSucc
      simpa only [Fin.castSucc_ne_last, if_false, add_zero, Fin.val_castSucc] using h
    · have h := deletedConfigurationDoublesIn_castSucc k Y
        (deletedLabelStratumConfiguration_shrink Y hk f) hk
      simp only [deletedLabelStratumConfiguration_shrink_castSucc] at h
      rw [← h]
      exact f.property.2⟩
  invFun f := ⟨fun i => (f.val i).castSucc, by
    constructor
    · intro b
      refine Fin.lastCases ?_ (fun b => ?_) b
      · simp [Nat.not_lt.mpr hk]
      · simpa only [Fin.castSucc_inj, Fin.castSucc_ne_last, if_false, add_zero,
          Fin.val_castSucc] using f.property.1 b
    · rw [deletedConfigurationDoublesIn_castSucc k Y f.val hk]
      exact f.property.2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact deletedLabelStratumConfiguration_shrink_castSucc Y hk f i
  right_inv f := by
    apply Subtype.ext
    funext i
    exact Fin.ext rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.deletedConfigurationDoublesIn_castSucc
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_ne_last
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_shrink_castSucc
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_singleEquiv

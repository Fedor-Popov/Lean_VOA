import VOA.DeligneAudit.SL4TStratumBoundary

/-! # Deleting a position from a labeled paired configuration -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Deleting the first position removes one element from precisely its label fiber. -/
theorem configurationFiber_card_delete {B N : ℕ} (f : Fin (B + 1) → Fin N) (a : Fin N) :
    (Finset.univ.filter fun i => f i = a).card =
      (Finset.univ.filter fun i : Fin B => f i.succ = a).card +
        if a = f 0 then 1 else 0 := by
  classical
  simp only [Finset.card_filter, Fin.sum_univ_succ]
  simp only [eq_comm, add_comm]

/-- The deleted label cannot be a doubled site wholly inside the surviving positions. -/
def deletedConfigurationDoublesIn {B N : ℕ} (k : ℕ) (Y : Finset (Fin B))
    (a : Fin N) (g : Fin B → Fin N) : ℕ :=
  (Finset.univ.filter fun b => b.val < k ∧ b ≠ a ∧ ∀ i, g i = b → i ∈ Y).card

/-- The selected-double statistic is unchanged when deleting an outside position. -/
theorem fullFlagDoublesIn_delete (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration (B + 1) k) :
    fullFlagDoublesIn (Y.map (Fin.succEmb B)) f =
      deletedConfigurationDoublesIn k Y (f.val 0) (fun i => f.val i.succ) := by
  classical
  unfold fullFlagDoublesIn deletedConfigurationDoublesIn
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_, ?_⟩
    · intro he
      have hz := h 0 he.symm
      simpa using hz
    · intro i hi
      have hs := h i.succ hi
      simpa using hs
  · rintro ⟨ha, hne, h⟩
    refine ⟨ha, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hi
      exact (hne hi.symm).elim
    · intro hi
      simpa using h i hi

/-- A configuration after deleting the first position, retaining all original site labels. -/
abbrev FullFlagDeletedConfiguration (B k j : ℕ) (Y : Finset (Fin B))
    (a : Fin (B + 1 - k)) :=
  {g : Fin B → Fin (B + 1 - k) //
    (∀ b, (Finset.univ.filter fun i => g i = b).card + (if b = a then 1 else 0) =
      if b.val < k then 2 else 1) ∧ deletedConfigurationDoublesIn k Y a g < j}

/-- Deletion records the first label and the residual labeled configuration. -/
def fullFlagStratumConfiguration_deleteEquiv (B k j : ℕ) (Y : Finset (Fin B)) :
    FullFlagStratumConfiguration (B + 1) k j (Y.map (Fin.succEmb B)) ≃
      (a : Fin (B + 1 - k)) × FullFlagDeletedConfiguration B k j Y a where
  toFun f := ⟨f.val.val 0, ⟨fun i => f.val.val i.succ, by
    constructor
    · intro b
      rw [← configurationFiber_card_delete]
      exact f.val.property b
    · rw [← fullFlagDoublesIn_delete]
      exact f.property⟩⟩
  invFun f := by
    let g : FullFlagConfiguration (B + 1) k := ⟨Fin.cons f.1 f.2.val, by
      intro b
      rw [configurationFiber_card_delete]
      simpa only [Fin.cons_zero, Fin.cons_succ] using f.2.property.1 b⟩
    exact ⟨g, by
      rw [fullFlagDoublesIn_delete]
      exact f.2.property.2⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv f := by
    rcases f with ⟨a, g⟩
    apply Sigma.ext rfl
    exact heq_of_eq (Subtype.ext rfl)

/-- The exact count splits into fibers indexed by the label of the deleted position. -/
theorem fullFlagStratumConfiguration_card_delete (B k j : ℕ) (Y : Finset (Fin B)) :
    Nat.card (FullFlagStratumConfiguration (B + 1) k j (Y.map (Fin.succEmb B))) =
      ∑ a : Fin (B + 1 - k), Nat.card (FullFlagDeletedConfiguration B k j Y a) := by
  rw [Nat.card_congr (fullFlagStratumConfiguration_deleteEquiv B k j Y), Nat.card_sigma]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.configurationFiber_card_delete
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_delete
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_deleteEquiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumConfiguration_card_delete

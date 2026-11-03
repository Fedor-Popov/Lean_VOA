import VOA.DeligneAudit.SL4TStratumConfigurationDeletion

/-! # Relabeling the sites remaining after deletion of a position -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The selected-double statistic for a function with an explicit label set. -/
def configurationSelectedDoubles {B N : ℕ} (k : ℕ) (Y : Finset (Fin B))
    (g : Fin B → Fin N) : ℕ :=
  (Finset.univ.filter fun b => b.val < k ∧ ∀ i, g i = b → i ∈ Y).card

/-- A stratum configuration with the number of labels kept as an independent parameter. -/
abbrev LabelStratumConfiguration (B N k j : ℕ) (Y : Finset (Fin B)) :=
  {g : Fin B → Fin N //
    (∀ b, (Finset.univ.filter fun i => g i = b).card = if b.val < k then 2 else 1) ∧
      configurationSelectedDoubles k Y g < j}

/-- A deleted configuration with an independent label count. -/
abbrev DeletedLabelStratumConfiguration (B N k j : ℕ) (Y : Finset (Fin B)) (a : Fin N) :=
  {g : Fin B → Fin N //
    (∀ b, (Finset.univ.filter fun i => g i = b).card + (if b = a then 1 else 0) =
      if b.val < k then 2 else 1) ∧ deletedConfigurationDoublesIn k Y a g < j}

/-- The explicit-label presentation is the original configuration type at its prescribed size. -/
def labelStratumConfiguration_equiv (B k j : ℕ) (Y : Finset (Fin B)) :
    LabelStratumConfiguration B (B - k) k j Y ≃ FullFlagStratumConfiguration B k j Y where
  toFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Label permutations preserve the cardinality of each corresponding fiber. -/
theorem configurationFiber_card_relabel {B N : ℕ} (g : Fin B → Fin N)
    (e : Equiv.Perm (Fin N)) (b : Fin N) :
    (Finset.univ.filter fun i => e (g i) = e b).card =
      (Finset.univ.filter fun i => g i = b).card := by
  simp only [Equiv.apply_eq_iff_eq]

/-- Relabeling within the two multiplicity classes preserves the deleted-double statistic. -/
theorem deletedConfigurationDoublesIn_relabel {B N : ℕ} (k : ℕ) (Y : Finset (Fin B))
    (a : Fin N) (g : Fin B → Fin N) (e : Equiv.Perm (Fin N))
    (he : ∀ b, (e b).val < k ↔ b.val < k) :
    deletedConfigurationDoublesIn k Y (e a) (fun i => e (g i)) =
      deletedConfigurationDoublesIn k Y a g := by
  classical
  symm
  apply Finset.card_equiv e
  intro b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he, ne_eq, Equiv.apply_eq_iff_eq]

/-- Residual configurations are equivalent under any permutation preserving the multiplicities. -/
def deletedLabelStratumConfiguration_relabel (B N k j : ℕ) (Y : Finset (Fin B))
    (a : Fin N) (e : Equiv.Perm (Fin N))
    (he : ∀ b, (e b).val < k ↔ b.val < k) :
    DeletedLabelStratumConfiguration B N k j Y a ≃
      DeletedLabelStratumConfiguration B N k j Y (e a) where
  toFun f := ⟨fun i => e (f.val i), by
    constructor
    · intro b
      obtain ⟨b, rfl⟩ := e.surjective b
      simpa only [configurationFiber_card_relabel, Equiv.apply_eq_iff_eq, he] using
        f.property.1 b
    · rw [deletedConfigurationDoublesIn_relabel k Y a f.val e he]
      exact f.property.2⟩
  invFun f := ⟨fun i => e.symm (f.val i), by
    constructor
    · intro b
      have h := f.property.1 (e b)
      have hf : (Finset.univ.filter fun i => e.symm (f.val i) = b) =
          (Finset.univ.filter fun i => f.val i = e b) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_eq]
      rw [hf]
      simpa only [Equiv.apply_eq_iff_eq, he] using h
    · have hs : ∀ b, (e.symm b).val < k ↔ b.val < k := by
        intro b
        simpa only [Equiv.apply_symm_apply] using (he (e.symm b)).symm
      have h := deletedConfigurationDoublesIn_relabel k Y (e a) f.val e.symm hs
      simp only [Equiv.symm_apply_apply] at h
      rw [h]
      exact f.property.2⟩
  left_inv f := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv f := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

/-- Removing one position at the last doubled label converts that label into a single site. -/
def deletedLabelStratumConfiguration_doubleEquiv (B N k j : ℕ) (Y : Finset (Fin B))
    (hk : k < N) :
    DeletedLabelStratumConfiguration B N (k + 1) j Y ⟨k, hk⟩ ≃
      LabelStratumConfiguration B N k j Y := by
  classical
  apply Equiv.subtypeEquivRight
  intro g
  have hc (b : Fin N) :
      ((Finset.univ.filter fun i => g i = b).card +
        (if b = (⟨k, hk⟩ : Fin N) then 1 else 0) = if b.val < k + 1 then 2 else 1) ↔
      ((Finset.univ.filter fun i => g i = b).card = if b.val < k then 2 else 1) := by
    have hb : b = (⟨k, hk⟩ : Fin N) ↔ b.val = k := Fin.ext_iff
    simp only [hb]
    split_ifs <;> omega
  have hs : deletedConfigurationDoublesIn (k + 1) Y ⟨k, hk⟩ g =
      configurationSelectedDoubles k Y g := by
    unfold deletedConfigurationDoublesIn configurationSelectedDoubles
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hb : b = (⟨k, hk⟩ : Fin N) ↔ b.val = k := Fin.ext_iff
    simp only [ne_eq, hb]
    have hn : b.val < k + 1 ∧ b.val ≠ k ↔ b.val < k := by omega
    rw [← and_assoc, hn]
  simp only [hc, hs]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.labelStratumConfiguration_equiv
#print axioms VOA.DeligneAudit.SL4T.configurationFiber_card_relabel
#print axioms VOA.DeligneAudit.SL4T.deletedConfigurationDoublesIn_relabel
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_relabel
#print axioms VOA.DeligneAudit.SL4T.deletedLabelStratumConfiguration_doubleEquiv

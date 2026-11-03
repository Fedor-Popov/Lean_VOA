import VOA.DeligneAudit.LeviTypeA2CertPrefixCore

/-! A finite Levi filtration from an ordered list of radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- The first `i` key spaces in an enumeration. -/
def a2KeyPrefixSpan {n : ℕ} (k : Fin n → A2RadicalKey)
    (i : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin n, ⨆ _ : j.val < i, a2KeyLayer ρ w (k j)

/-- The Levi closure of the first `i` key spaces. -/
def a2KeyPrefix {n : ℕ} (k : Fin n → A2RadicalKey)
    (i : ℕ) : Submodule ℂ V :=
  a2LeviClosure ρ (a2KeyPrefixSpan ρ w k i)

theorem a2KeyPrefixSpan_zero {n : ℕ} (k : Fin n → A2RadicalKey) :
    a2KeyPrefixSpan ρ w k 0 = ⊥ := by
  simp [a2KeyPrefixSpan]

theorem a2KeyPrefix_zero {n : ℕ} (k : Fin n → A2RadicalKey) :
    a2KeyPrefix ρ w k 0 = ⊥ := by
  rw [a2KeyPrefix, a2KeyPrefixSpan_zero, a2LeviClosure_bot]

theorem a2KeyPrefixSpan_step {n i : ℕ} (hi : i < n)
    (k : Fin n → A2RadicalKey) :
    a2KeyPrefixSpan ρ w k (i + 1) =
      a2KeyPrefixSpan ρ w k i ⊔ a2KeyLayer ρ w (k ⟨i, hi⟩) := by
  apply le_antisymm
  · rw [a2KeyPrefixSpan, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    have hjlt : j.val < i + 1 := hj
    by_cases hlt : j.val < i
    · exact le_sup_of_le_left
        (le_iSup_of_le j (le_iSup_of_le hlt le_rfl))
    · have heq : j = ⟨i, hi⟩ := Fin.ext (show j.val = i by omega)
      subst j
      exact le_sup_right
  · apply sup_le
    · rw [a2KeyPrefixSpan, iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro hj
      exact le_iSup_of_le j
        (le_iSup_of_le (by omega : j.val < i + 1) le_rfl)
    · exact le_iSup_of_le (⟨i, hi⟩ : Fin n)
        (le_iSup_of_le (by omega : i < i + 1) le_rfl)

theorem a2KeyPrefix_step {n i : ℕ} (hi : i < n)
    (k : Fin n → A2RadicalKey) :
    a2KeyPrefix ρ w k (i + 1) =
      a2KeyPrefix ρ w k i ⊔
        a2LeviClosure ρ (a2KeyLayer ρ w (k ⟨i, hi⟩)) := by
  rw [a2KeyPrefix, a2KeyPrefixSpan_step ρ w hi k,
    a2LeviClosure_sup]
  rfl

theorem a2KeyPrefix_mono {n i : ℕ} (hi : i < n)
    (k : Fin n → A2RadicalKey) :
    a2KeyPrefix ρ w k i ≤ a2KeyPrefix ρ w k (i + 1) := by
  rw [a2KeyPrefix_step ρ w hi k]
  exact le_sup_left

/-- An enumeration of the finite box gives a terminal filtration equal to
the cyclic module. -/
theorem a2KeyPrefix_top {n : ℕ} (k : Fin n → A2RadicalKey)
    (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (hmem : ∀ j, k j ∈ a2KeyBox p q)
    (hcover : ∀ x ∈ a2KeyBox p q, ∃ j, k j = x) :
    a2KeyPrefix ρ w k n = VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  have hspan : a2KeyPrefixSpan ρ w k n =
      ⨆ x ∈ a2KeyBox p q, a2KeyLayer ρ w x := by
    apply le_antisymm
    · rw [a2KeyPrefixSpan, iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro _
      exact le_iSup_of_le (k j) (le_iSup_of_le (hmem j) le_rfl)
    · rw [iSup_le_iff]
      intro x
      rw [iSup_le_iff]
      intro hx
      obtain ⟨j, hj⟩ := hcover x hx
      rw [← hj]
      exact le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl)
  rw [a2KeyPrefix, hspan]
  exact (a2_cycSubG_eq_leviClosure_keyBox ρ w p q h).symm

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefixSpan_zero
#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefix_zero
#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefixSpan_step
#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefix_step
#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefix_mono
#print axioms VOA.DeligneAudit.A3Sector.a2KeyPrefix_top

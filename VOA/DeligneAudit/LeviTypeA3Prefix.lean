import VOA.DeligneAudit.LeviTypeA3PrefixCore

/-! A finite Levi filtration from an ordered list of radical keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3KeyPrefixSpan {n : ℕ} (k : Fin n → A3RadicalKey)
    (i : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin n, ⨆ _ : j.val < i, a3KeyLayer ρ w (k j)

def a3KeyPrefix {n : ℕ} (k : Fin n → A3RadicalKey)
    (i : ℕ) : Submodule ℂ V :=
  a3LeviClosure ρ (a3KeyPrefixSpan ρ w k i)

theorem a3KeyPrefixSpan_zero {n : ℕ} (k : Fin n → A3RadicalKey) :
    a3KeyPrefixSpan ρ w k 0 = ⊥ := by
  simp [a3KeyPrefixSpan]

theorem a3KeyPrefix_zero {n : ℕ} (k : Fin n → A3RadicalKey) :
    a3KeyPrefix ρ w k 0 = ⊥ := by
  rw [a3KeyPrefix, a3KeyPrefixSpan_zero, a3LeviClosure_bot]

theorem a3KeyPrefixSpan_step {n i : ℕ} (hi : i < n)
    (k : Fin n → A3RadicalKey) :
    a3KeyPrefixSpan ρ w k (i + 1) =
      a3KeyPrefixSpan ρ w k i ⊔ a3KeyLayer ρ w (k ⟨i, hi⟩) := by
  apply le_antisymm
  · rw [a3KeyPrefixSpan, iSup_le_iff]
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
    · rw [a3KeyPrefixSpan, iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro hj
      exact le_iSup_of_le j
        (le_iSup_of_le (by omega : j.val < i + 1) le_rfl)
    · exact le_iSup_of_le (⟨i, hi⟩ : Fin n)
        (le_iSup_of_le (by omega : i < i + 1) le_rfl)

theorem a3KeyPrefix_step {n i : ℕ} (hi : i < n)
    (k : Fin n → A3RadicalKey) :
    a3KeyPrefix ρ w k (i + 1) =
      a3KeyPrefix ρ w k i ⊔
        a3LeviClosure ρ (a3KeyLayer ρ w (k ⟨i, hi⟩)) := by
  rw [a3KeyPrefix, a3KeyPrefixSpan_step ρ w hi k, a3LeviClosure_sup]
  rfl

theorem a3KeyPrefix_mono {n i : ℕ} (hi : i < n)
    (k : Fin n → A3RadicalKey) :
    a3KeyPrefix ρ w k i ≤ a3KeyPrefix ρ w k (i + 1) := by
  rw [a3KeyPrefix_step ρ w hi k]
  exact le_sup_left

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefixSpan_zero
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefix_zero
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefixSpan_step
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefix_step
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefix_mono

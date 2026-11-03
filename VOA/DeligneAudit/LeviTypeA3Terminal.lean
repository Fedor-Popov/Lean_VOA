import VOA.DeligneAudit.LeviTypeA3AllKeys

/-! The ordered finite key filtration reaches the entire cyclic module. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_cycSubG_eq_leviClosure_keyBox (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    VOA.DeligneAudit.UnivG.cycSubG ρ w =
      a3LeviClosure ρ
        (⨆ k ∈ a3KeyBox a b c, a3KeyLayer ρ w k) := by
  have hspan : a3AllKeySpan ρ w =
      ⨆ k ∈ a3KeyBox a b c, a3KeyLayer ρ w k := by
    apply le_antisymm
    · rw [a3AllKeySpan, iSup_le_iff]
      intro k
      by_cases hk : a3KeyLayer ρ w k = ⊥
      · simp [hk]
      · exact le_iSup_of_le k
          (le_iSup_of_le
            (a3KeyBox_contains_nonzero_global ρ w a b c h k hk) le_rfl)
    · rw [iSup_le_iff]
      intro k
      rw [iSup_le_iff]
      intro _
      exact le_iSup (fun j => a3KeyLayer ρ w j) k
  rw [← hspan]
  exact a3_cycSubG_eq_leviClosure_allKeys ρ w a b c h

theorem a3KeyPrefix_top {n : ℕ} (key : Fin n → A3RadicalKey)
    (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
    (hmem : ∀ j, key j ∈ a3KeyBox a b c)
    (hcover : ∀ x ∈ a3KeyBox a b c, ∃ j, key j = x) :
    a3KeyPrefix ρ w key n = VOA.DeligneAudit.UnivG.cycSubG ρ w := by
  have hspan : a3KeyPrefixSpan ρ w key n =
      ⨆ x ∈ a3KeyBox a b c, a3KeyLayer ρ w x := by
    apply le_antisymm
    · rw [a3KeyPrefixSpan, iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro _
      exact le_iSup_of_le (key j) (le_iSup_of_le (hmem j) le_rfl)
    · rw [iSup_le_iff]
      intro x
      rw [iSup_le_iff]
      intro hx
      obtain ⟨j, hj⟩ := hcover x hx
      rw [← hj]
      exact le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl)
  rw [a3KeyPrefix, hspan]
  exact (a3_cycSubG_eq_leviClosure_keyBox ρ w a b c h).symm

theorem a3OrderedPrefix_top (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    a3KeyPrefix ρ w (a3KeyEnum a b c) (a3KeyBox a b c).card =
      VOA.DeligneAudit.UnivG.cycSubG ρ w :=
  a3KeyPrefix_top ρ w (a3KeyEnum a b c) a b c h
    (a3KeyEnum_mem a b c) (a3KeyEnum_cover a b c)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_cycSubG_eq_leviClosure_keyBox
#print axioms VOA.DeligneAudit.A3Sector.a3KeyPrefix_top
#print axioms VOA.DeligneAudit.A3Sector.a3OrderedPrefix_top

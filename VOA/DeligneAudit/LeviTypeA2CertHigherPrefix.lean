import VOA.DeligneAudit.LeviTypeA2CertOrderedPrefix

/-! The ordered prefix is exactly the Levi closure of the strictly higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

theorem a2OrderedPrefix_eq_higher (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (i : ℕ) (hi : i < (a2KeyBox p q).card) :
    a2KeyPrefix ρ w (a2KeyEnum p q) i =
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q (a2KeyEnum p q ⟨i, hi⟩)) := by
  apply congrArg (a2LeviClosure ρ)
  apply le_antisymm
  · rw [a2KeyPrefixSpan, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    have hless := a2KeyEnum_descending p q j ⟨i, hi⟩ hj
    exact le_iSup_of_le (a2KeyEnum p q j)
      (le_iSup_of_le hless le_rfl)
  · rw [a2HigherKeySpan, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    by_cases hbot : a2KeyLayer ρ w j = ⊥
    · simp [hbot]
    have hmem := a2KeyBox_contains_nonzero_unconditional ρ w p q h j hbot
    obtain ⟨m, hm⟩ := a2KeyEnum_cover p q j hmem
    have hmi : m.val < i := by
      rcases lt_trichotomy m.val i with hlt | heq | hgt
      · exact hlt
      · have hmeq : m = ⟨i, hi⟩ := Fin.ext heq
        exact False.elim ((a2KeyLess_irrefl q j) (by simpa [← hm, hmeq] using hj))
      · have hless := a2KeyEnum_descending p q ⟨i, hi⟩ m hgt
        exact False.elim ((a2KeyLess_irrefl q j)
          (a2KeyLess_trans q (by simpa [hm] using hless) hj))
    rw [← hm]
    exact le_iSup_of_le m (le_iSup_of_le hmi le_rfl)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2OrderedPrefix_eq_higher

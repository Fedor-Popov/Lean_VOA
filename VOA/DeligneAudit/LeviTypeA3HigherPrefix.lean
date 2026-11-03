import VOA.DeligneAudit.LeviTypeA3OrderedKeys

/-! The ordered prefix agrees with the Levi closure of strictly higher keys. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3OrderedPrefix_eq_higher (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : ℕ) (hi : i < (a3KeyBox a b c).card) :
    a3KeyPrefix ρ w (a3KeyEnum a b c) i =
      a3HigherLeviClosure ρ w b c (a3KeyEnum a b c ⟨i, hi⟩) := by
  apply congrArg (a3LeviClosure ρ)
  apply le_antisymm
  · rw [a3KeyPrefixSpan, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    have hless := a3KeyEnum_descending a b c j ⟨i, hi⟩ hj
    exact le_iSup_of_le (a3KeyEnum a b c j)
      (le_iSup_of_le hless le_rfl)
  · rw [a3HigherKeySpan, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    by_cases hbot : a3KeyLayer ρ w j = ⊥
    · simp [hbot]
    have hmem := a3KeyBox_contains_nonzero_global ρ w a b c h j hbot
    obtain ⟨m, hm⟩ := a3KeyEnum_cover a b c j hmem
    have hmi : m.val < i := by
      rcases lt_trichotomy m.val i with hlt | heq | hgt
      · exact hlt
      · have hmeq : m = ⟨i, hi⟩ := Fin.ext heq
        exact False.elim ((a3KeyLess_irrefl b c j)
          (by simpa [← hm, hmeq] using hj))
      · have hless := a3KeyEnum_descending a b c ⟨i, hi⟩ m hgt
        exact False.elim ((a3KeyLess_irrefl b c j)
          (a3KeyLess_trans b c (by simpa [hm] using hless) hj))
    rw [← hm]
    exact le_iSup_of_le m (le_iSup_of_le hmi le_rfl)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3OrderedPrefix_eq_higher

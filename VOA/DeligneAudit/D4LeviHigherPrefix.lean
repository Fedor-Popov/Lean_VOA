import VOA.DeligneAudit.D4LeviPrefix

/-! The descending prefix consists of exactly the higher key orbits. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem keyPrefix_eq_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (i : ℕ) (hi : i < (globalKeyBox m).card) :
    keyPrefix ρ w m i = higherOrbit ρ w m (keyEnum m ⟨i, hi⟩) := by
  apply le_antisymm
  · rw [keyPrefix, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    exact keyOrbit_le_higher ρ w m _ _
      (keyEnum_descending m j ⟨i, hi⟩ hj)
  · rw [higherOrbit, iSup_le_iff]
    intro j
    by_cases hbot : keyLayer ρ w j.val = ⊥
    · rw [keyOrbit_eq_bot_of_keyLayer_bot ρ w j.val hbot]
      exact bot_le
    have hmem : j.val ∈ globalKeyBox m :=
      keyBox_contains_nonzero_global ρ w m h j.val hbot
    obtain ⟨q, hq⟩ := keyEnum_cover m j.val hmem
    have hqi : q.val < i := by
      rcases lt_trichotomy q.val i with hlt | heq | hgt
      · exact hlt
      · have hqe : q = ⟨i, hi⟩ := Fin.ext heq
        exact False.elim ((keyLess_irrefl m j.val)
          (by simpa [← hq, hqe] using j.property))
      · have hless := keyEnum_descending m ⟨i, hi⟩ q hgt
        exact False.elim ((keyLess_irrefl m j.val)
          (keyLess_trans m (by simpa [hq] using hless) j.property))
    rw [← hq]
    exact le_iSup_of_le q (le_iSup_of_le hqi le_rfl)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_eq_higher

import VOA.DeligneAudit.D4LeviOrderedKeys

/-! The finite descending prefix of full gl₄ key orbits. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def keyPrefix (i : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (globalKeyBox m).card,
    ⨆ _ : j.val < i, keyOrbit ρ w (keyEnum m j)

theorem keyPrefix_zero : keyPrefix ρ w m 0 = ⊥ := by
  simp [keyPrefix]

theorem keyPrefix_step (i : ℕ) (hi : i < (globalKeyBox m).card) :
    keyPrefix ρ w m (i + 1) =
      keyPrefix ρ w m i ⊔ keyOrbit ρ w (keyEnum m ⟨i, hi⟩) := by
  apply le_antisymm
  · rw [keyPrefix, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro hj
    by_cases hlt : j.val < i
    · exact le_sup_of_le_left
        (le_iSup_of_le j (le_iSup_of_le hlt le_rfl))
    · have heq : j = ⟨i, hi⟩ := Fin.ext (show j.val = i by omega)
      subst j
      exact le_sup_right
  · apply sup_le
    · rw [keyPrefix, iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro hj
      exact le_iSup_of_le j
        (le_iSup_of_le (by omega : j.val < i + 1) le_rfl)
    · exact le_iSup_of_le (⟨i, hi⟩ : Fin (globalKeyBox m).card)
        (le_iSup_of_le (by omega : i < i + 1) le_rfl)

theorem keyPrefix_mono (i : ℕ) (hi : i < (globalKeyBox m).card) :
    keyPrefix ρ w m i ≤ keyPrefix ρ w m (i + 1) := by
  rw [keyPrefix_step ρ w m i hi]
  exact le_sup_left

private theorem keyVectorOrbit_zero :
    keyVectorOrbit ρ (0 : V) = ⊥ := by
  rw [keyVectorOrbit, Submodule.span_eq_bot]
  rintro z ⟨l, _, rfl⟩
  exact VOA.DeligneAudit.SectorWeyl.wordOp_zero ρ l

theorem keyOrbit_eq_bot_of_keyLayer_bot (k : RadicalKey)
    (hk : keyLayer ρ w k = ⊥) : keyOrbit ρ w k = ⊥ := by
  rw [keyOrbit_eq_iSup_vectorOrbit]
  apply le_antisymm
  · apply iSup_le
    intro v
    have hv : (v : V) = 0 := (Submodule.mem_bot ℂ).mp (hk ▸ v.property)
    simp [hv, keyVectorOrbit_zero ρ]
  · exact bot_le

theorem keyPrefix_top
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    keyPrefix ρ w m (globalKeyBox m).card = cycSubG ρ w := by
  rw [source_cyc_eq_iSup_keyOrbit ρ w m h]
  apply le_antisymm
  · rw [keyPrefix, iSup_le_iff]
    intro j
    rw [iSup_le_iff]
    intro _
    exact le_iSup (fun k => keyOrbit ρ w k) (keyEnum m j)
  · apply iSup_le
    intro k
    by_cases hk : keyLayer ρ w k = ⊥
    · rw [keyOrbit_eq_bot_of_keyLayer_bot ρ w k hk]
      exact bot_le
    · have hmem : k ∈ globalKeyBox m :=
        keyBox_contains_nonzero_global ρ w m h k hk
      obtain ⟨j, rfl⟩ := keyEnum_cover m k hmem
      exact le_iSup_of_le j
        (le_iSup_of_le j.isLt le_rfl)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_zero
#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_step
#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_mono
#print axioms VOA.DeligneAudit.D4Levi.keyOrbit_eq_bot_of_keyLayer_bot
#print axioms VOA.DeligneAudit.D4Levi.keyPrefix_top

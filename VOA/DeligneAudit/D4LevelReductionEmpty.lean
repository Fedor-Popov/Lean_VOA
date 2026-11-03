import VOA.DeligneAudit.D4LevelReductionAssembly

/-! Empty levels of the descending D4 Levi filtration. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- A level with no key at its threshold agrees with the next filtration term. -/
theorem levelFiltration_eq_next_of_no_key (m : ℕ) (κ p : ℤ)
    (h : ∀ k ∈ globalKeyBox m, keyAlphaGrade m k = κ → keyLeviLevel m k ≠ p) :
    levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    apply iSup_le
    intro hκ
    apply iSup_le
    intro hp
    exact keyOrbit_le_levelFiltration ρ w m κ (p + 1) k hk hκ
      (by have := h k hk hκ; omega)
  · exact levelFiltration_antitone ρ w m κ (by omega)

/-- No associated level piece occurs outside the finite key-index set. -/
theorem levelFiltration_eq_next_of_outside (m : ℕ) (κ p : ℤ)
    (h : (κ, p) ∉ levelIndices m) :
    levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1) := by
  apply levelFiltration_eq_next_of_no_key
  intro k hk hκ hp
  exact h (Finset.mem_image.mpr ⟨k, hk, by simp [hκ, hp]⟩)

/-- Every key has nonnegative twice-adjoint count. -/
theorem keyAlphaGrade_le_leviLevel (m : ℕ) (k : RadicalKey) :
    keyAlphaGrade m k ≤ keyLeviLevel m k := by
  simp only [keyAlphaGrade, keyLeviLevel, keyDepth, Nat.cast_add]
  omega

/-- Every key has nonnegative twice-central count. -/
theorem keyAlphaGrade_add_leviLevel_le (m : ℕ) (k : RadicalKey) :
    keyAlphaGrade m k + keyLeviLevel m k ≤ 2 * (m : ℤ) := by
  simp only [keyAlphaGrade, keyLeviLevel, keyDepth, Nat.cast_add]
  omega

/-- A negative adjoint count leaves no key at the level threshold. -/
theorem levelFiltration_eq_next_of_negative_adjoint (m : ℕ) (κ p : ℤ)
    (h : p < κ) :
    levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1) := by
  apply levelFiltration_eq_next_of_no_key
  intro k _ hκ hp
  have := keyAlphaGrade_le_leviLevel m k
  omega

/-- A negative central count leaves no key at the level threshold. -/
theorem levelFiltration_eq_next_of_negative_central (m : ℕ) (κ p : ℤ)
    (h : 2 * (m : ℤ) < p + κ) :
    levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1) := by
  apply levelFiltration_eq_next_of_no_key
  intro k _ hκ hp
  have := keyAlphaGrade_add_leviLevel_le m k
  omega

/-- An unchanged filtration term has zero-dimensional level coinvariants. -/
theorem truncatedLevel_finrank_zero_of_eq_next (m : ℕ) (κ p : ℤ)
    (h : levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1)) :
    Module.finrank ℂ (TruncatedLevelPiece ρ w m κ p) = 0 := by
  have heq : (levelFiltration ρ w m κ (p + 1) ⊔
      currentTail ρ (levelFiltration ρ w m κ p) {c | IsLevi c} m).comap
        (levelFiltration ρ w m κ p).subtype = ⊤ := by
    apply top_unique
    intro v _
    exact Submodule.mem_sup_left (h ▸ v.property)
  haveI : Subsingleton (TruncatedLevelPiece ρ w m κ p) :=
    Submodule.Quotient.subsingleton_iff.mpr heq
  exact Module.finrank_zero_of_subsingleton

/-- All universal level bounds outside the key-index set hold. -/
theorem levelTruncationBound_of_outside (m : ℕ) (κ p : ℤ)
    (h : (κ, p) ∉ levelIndices m) : LevelTruncationBound m κ p := by
  change Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ _
  rw [truncatedLevel_finrank_zero_of_eq_next _ _ m κ p
    (levelFiltration_eq_next_of_outside _ _ m κ p h)]
  exact Nat.zero_le _

/-- All universal level bounds with negative adjoint count hold. -/
theorem levelTruncationBound_of_negative_adjoint (m : ℕ) (κ p : ℤ)
    (h : p < κ) : LevelTruncationBound m κ p := by
  change Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ _
  rw [truncatedLevel_finrank_zero_of_eq_next _ _ m κ p
    (levelFiltration_eq_next_of_negative_adjoint _ _ m κ p h)]
  exact Nat.zero_le _

/-- All universal level bounds with negative central count hold. -/
theorem levelTruncationBound_of_negative_central (m : ℕ) (κ p : ℤ)
    (h : 2 * (m : ℤ) < p + κ) : LevelTruncationBound m κ p := by
  change Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ _
  rw [truncatedLevel_finrank_zero_of_eq_next _ _ m κ p
    (levelFiltration_eq_next_of_negative_central _ _ m κ p h)]
  exact Nat.zero_le _

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_next_of_no_key
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_next_of_outside
#print axioms VOA.DeligneAudit.D4LevelReduction.keyAlphaGrade_le_leviLevel
#print axioms VOA.DeligneAudit.D4LevelReduction.keyAlphaGrade_add_leviLevel_le
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_next_of_negative_adjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelFiltration_eq_next_of_negative_central
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedLevel_finrank_zero_of_eq_next
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_outside
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_negative_adjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_negative_central

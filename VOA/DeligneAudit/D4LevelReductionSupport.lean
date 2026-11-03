import VOA.DeligneAudit.D4LevelReductionParity

/-! Vanishing of the D4 universal level pieces and their combinatorial targets. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- Odd level differences support no four-colour configuration. -/
theorem levelTarget_zero_of_odd (m : ℕ) (κ p : ℤ) (hodd : (p - κ) % 2 ≠ 0) :
    levelTarget m κ p = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨_, hκ, hp⟩ := Finset.mem_filter.mp ht
  simp only [multiplicityGrade, multiplicityLevel] at hκ hp
  omega

/-- A negative adjoint count supports no four-colour configuration. -/
theorem levelTarget_zero_of_negative_adjoint (m : ℕ) (κ p : ℤ) (h : p < κ) :
    levelTarget m κ p = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨_, hκ, hp⟩ := Finset.mem_filter.mp ht
  simp only [multiplicityGrade, multiplicityLevel] at hκ hp
  omega

/-- A negative central count supports no four-colour configuration. -/
theorem levelTarget_zero_of_negative_central (m : ℕ) (κ p : ℤ)
    (h : 2 * (m : ℤ) < p + κ) : levelTarget m κ p = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨ht, hκ, hp⟩ := Finset.mem_filter.mp ht
  have hs := siteMultiplicity_sum m t ht
  simp only [multiplicityGrade, multiplicityLevel] at hκ hp
  omega

/-- An unchanged level has only the zero vector, even before taking coinvariants. -/
theorem levelPiece_subsingleton_of_eq_next {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ) (κ p : ℤ)
    (h : levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1)) :
    Subsingleton (LevelPiece ρ w m κ p) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro v _
  exact h ▸ v.property

/-- An unchanged level has only the zero vector after taking coinvariants. -/
theorem truncatedLevel_subsingleton_of_eq_next {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule D4sector.f V) (w : V)
    (m : ℕ) (κ p : ℤ)
    (h : levelFiltration ρ w m κ p = levelFiltration ρ w m κ (p + 1)) :
    Subsingleton (TruncatedLevelPiece ρ w m κ p) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro v _
  exact Submodule.mem_sup_left (h ▸ v.property)

/-- Every excluded, odd, or negative-count universal level is the zero module. -/
theorem universalLevel_subsingleton_of_empty (m : ℕ) (κ p : ℤ)
    (h : (κ, p) ∉ levelIndices m ∨ (p - κ) % 2 ≠ 0 ∨
      p < κ ∨ 2 * (m : ℤ) < p + κ) : Subsingleton (UniversalLevelPiece m κ p) := by
  apply truncatedLevel_subsingleton_of_eq_next
  rcases h with h | h | h | h
  · exact levelFiltration_eq_next_of_outside _ _ m κ p h
  · exact levelFiltration_eq_next_of_odd _ _ m
      (univG_sat D4sector.f (ravFam D4sector m 0)) κ p h
  · exact levelFiltration_eq_next_of_negative_adjoint _ _ m κ p h
  · exact levelFiltration_eq_next_of_negative_central _ _ m κ p h

/-- The universal dimension bound holds for every empty level and every multiplicity. -/
theorem levelTruncationBound_of_empty (m : ℕ) (κ p : ℤ)
    (h : (κ, p) ∉ levelIndices m ∨ (p - κ) % 2 ≠ 0 ∨
      p < κ ∨ 2 * (m : ℤ) < p + κ) : LevelTruncationBound m κ p := by
  haveI := universalLevel_subsingleton_of_empty m κ p h
  change Module.finrank ℂ (UniversalLevelPiece m κ p) ≤ _
  rw [Module.finrank_zero_of_subsingleton]
  exact Nat.zero_le _

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_zero_of_odd
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_zero_of_negative_adjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_zero_of_negative_central
#print axioms VOA.DeligneAudit.D4LevelReduction.levelPiece_subsingleton_of_eq_next
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedLevel_subsingleton_of_eq_next
#print axioms VOA.DeligneAudit.D4LevelReduction.universalLevel_subsingleton_of_empty
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_empty

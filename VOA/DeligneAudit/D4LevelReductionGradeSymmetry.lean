import VOA.DeligneAudit.D4LevelReductionCoreCoverage

/-! Grade reflection of the four-colour targets and the remaining negative-grade transfer. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- Exchange the positive and negative exterior-square colours. -/
def reflectSiteMultiplicity (t : SiteMultiplicity) : SiteMultiplicity :=
  ![t 0, t 2, t 1, t 3]

theorem reflectSiteMultiplicity_involutive : Function.Involutive reflectSiteMultiplicity := by
  intro t
  funext i
  fin_cases i <;> rfl

theorem reflectSiteMultiplicity_mem (m : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities m) : reflectSiteMultiplicity t ∈ siteMultiplicities m := by
  have hs := siteMultiplicity_sum m t ht
  simp only [siteMultiplicities, Finset.mem_piAntidiag]
  constructor
  · simpa [reflectSiteMultiplicity, Fin.sum_univ_four, add_assoc, add_comm, add_left_comm]
      using hs
  · simp

theorem multiplicityGrade_reflect (t : SiteMultiplicity) :
    multiplicityGrade (reflectSiteMultiplicity t) = -multiplicityGrade t := by
  simp [multiplicityGrade, reflectSiteMultiplicity]

theorem multiplicityLevel_reflect (t : SiteMultiplicity) :
    multiplicityLevel (reflectSiteMultiplicity t) = multiplicityLevel t := by
  simp [multiplicityLevel, reflectSiteMultiplicity]
  ring

theorem configurationDimension_reflect (t : SiteMultiplicity) :
    configurationDimension (reflectSiteMultiplicity t) = configurationDimension t := by
  simp [configurationDimension, Nat.multinomial, reflectSiteMultiplicity,
    Fin.sum_univ_four, Fin.prod_univ_four, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc]

/-- The target dimensions are unchanged by reversing the vector-node grade. -/
theorem levelTarget_neg_grade (m : ℕ) (κ p : ℤ) :
    levelTarget m (-κ) p = levelTarget m κ p := by
  classical
  unfold levelTarget
  apply Finset.sum_bij (fun t _ => reflectSiteMultiplicity t)
  · intro t ht
    obtain ⟨ht, hg, hp⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨reflectSiteMultiplicity_mem m t ht,
      by rw [multiplicityGrade_reflect, hg, neg_neg],
      by rw [multiplicityLevel_reflect, hp]⟩
  · intro t _ u _ he
    exact reflectSiteMultiplicity_involutive.injective he
  · intro t ht
    obtain ⟨ht, hg, hp⟩ := Finset.mem_filter.mp ht
    refine ⟨reflectSiteMultiplicity t, Finset.mem_filter.mpr
      ⟨reflectSiteMultiplicity_mem m t ht, ?_, ?_⟩,
      reflectSiteMultiplicity_involutive t⟩
    · rw [multiplicityGrade_reflect, hg]
    · rw [multiplicityLevel_reflect, hp]
  · intro t _
    exact (configurationDimension_reflect t).symm

/-- The missing representation-theoretic transfer concerns the actual universal coinvariants. -/
def NegativeGradeRankTransfer : Prop :=
  ∀ (m : ℕ) (κ p : ℤ), κ < 0 →
    Module.finrank ℂ (UniversalLevelPiece m κ p) ≤
      Module.finrank ℂ (UniversalLevelPiece m (-κ) p)

/-- Grade transfer and the interior core estimates cover every integer grade and level. -/
theorem levelTruncationBound_of_coreBounds_and_negativeGradeTransfer
    (h : ∀ a b c : ℕ, 1 ≤ a → 1 ≤ c → TruncatedCoreRankBound a b c)
    (htransfer : NegativeGradeRankTransfer) (m : ℕ) (κ p : ℤ) :
    LevelTruncationBound m κ p := by
  by_cases hκ : 0 ≤ κ
  · exact levelTruncationBound_of_nonnegative_coreBounds h m κ p hκ
  have hb := levelTruncationBound_of_nonnegative_coreBounds h m (-κ) p (by omega)
  change Module.finrank ℂ (UniversalLevelPiece m (-κ) p) ≤ _ at hb
  rw [levelTarget_neg_grade] at hb
  exact (htransfer m κ p (by omega)).trans hb

/-- The negative extremal grade belongs to the key-index set for every multiplicity. -/
theorem negativeExtremalLevel_mem (m : ℕ) : (-(m : ℤ), (m : ℤ)) ∈ levelIndices m := by
  apply Finset.mem_image.mpr
  refine ⟨bottomRadicalKey m m 0, ?_, ?_⟩
  · apply D4Levi.mem_keyBox <;> simp [bottomRadicalKey] <;> omega
  · simp [bottomRadicalKey, keyAlphaGrade, keyLeviLevel, D4Levi.keyDepth]

/-- The negative extremal grade satisfies none of the established empty-level criteria. -/
theorem negativeExtremalLevel_not_empty (m : ℕ) :
    ¬ ((-(m : ℤ), (m : ℤ)) ∉ levelIndices m ∨
      ((m : ℤ) - -(m : ℤ)) % 2 ≠ 0 ∨
      (m : ℤ) < -(m : ℤ) ∨ 2 * (m : ℤ) < (m : ℤ) + -(m : ℤ)) := by
  rintro (h | h | h | h)
  · exact h (negativeExtremalLevel_mem m)
  all_goals omega

/-- A negative grade cannot be the natural middle label of any existing core presentation. -/
theorem negativeExtremalLevel_no_bottomTriple (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∃ a b c : ℕ, a + b + c = m ∧ (b : ℤ) = -(m : ℤ) ∧
      2 * (a : ℤ) + b = m := by
  rintro ⟨a, b, c, _, hb, _⟩
  omega

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_neg_grade
#print axioms VOA.DeligneAudit.D4LevelReduction.negativeExtremalLevel_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.negativeExtremalLevel_not_empty
#print axioms VOA.DeligneAudit.D4LevelReduction.negativeExtremalLevel_no_bottomTriple
#print axioms
  VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_coreBounds_and_negativeGradeTransfer

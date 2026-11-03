import VOA.DeligneAudit.D4LevelReductionCount
import Mathlib.Tactic.FinCases

/-! The single-configuration count at D4 levels with zero central count. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- The edge configuration has only adjoint sites and positive exterior-square sites. -/
def adjointEdgeMultiplicity (a b : ℕ) : SiteMultiplicity := ![a, b, 0, 0]

theorem adjointEdgeMultiplicity_mem (a b : ℕ) :
    adjointEdgeMultiplicity a b ∈ siteMultiplicities (a + b) := by
  simp [siteMultiplicities, Finset.mem_piAntidiag, adjointEdgeMultiplicity,
    Fin.sum_univ_succ]

/-- There is exactly one configuration at an edge level with nonnegative labels. -/
theorem multiplicity_eq_adjointEdge (a b : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities (a + b)) (hκ : multiplicityGrade t = b)
    (hp : multiplicityLevel t = 2 * (a : ℤ) + b) :
    t = adjointEdgeMultiplicity a b := by
  have hs := siteMultiplicity_sum (a + b) t ht
  simp only [multiplicityGrade, multiplicityLevel] at hκ hp
  have ht₀ : t 0 = a := by omega
  have ht₁ : t 1 = b := by omega
  have ht₂ : t 2 = 0 := by omega
  have ht₃ : t 3 = 0 := by omega
  funext i
  fin_cases i <;> simp [adjointEdgeMultiplicity, ht₀, ht₁, ht₂, ht₃]

/-- The edge configuration has the binomial multiplicity and the mixed sl₄ local rank. -/
theorem adjointEdge_configurationDimension (a b : ℕ) :
    configurationDimension (adjointEdgeMultiplicity a b) =
      (a + b).choose a * 15 ^ a * 6 ^ b := by
  rw [configurationDimension_factorial (a + b) _ (adjointEdgeMultiplicity_mem a b)]
  simp only [adjointEdgeMultiplicity, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Nat.factorial_zero, mul_one, add_zero]
  rw [Nat.choose_eq_factorial_div_factorial (Nat.le_add_right a b)]
  simp

/-- The target at zero central count is the binomial multiplicity times the mixed rank. -/
theorem levelTarget_adjoint_edge (a b : ℕ) :
    levelTarget (a + b) b (2 * (a : ℤ) + b) =
      (a + b).choose a * 15 ^ a * 6 ^ b := by
  classical
  have hmem : adjointEdgeMultiplicity a b ∈
      (siteMultiplicities (a + b)).filter
        (fun t => multiplicityGrade t = b ∧ multiplicityLevel t = 2 * (a : ℤ) + b) := by
    refine Finset.mem_filter.mpr ⟨adjointEdgeMultiplicity_mem a b, ?_, ?_⟩
    · simp [multiplicityGrade, adjointEdgeMultiplicity]
    · simp [multiplicityLevel, adjointEdgeMultiplicity]
  rw [levelTarget, Finset.sum_eq_single_of_mem _ hmem]
  · exact adjointEdge_configurationDimension a b
  · intro t ht hne
    obtain ⟨ht, hκ, hp⟩ := Finset.mem_filter.mp ht
    exact (hne (multiplicity_eq_adjointEdge a b t ht hκ hp)).elim

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.adjointEdgeMultiplicity_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.multiplicity_eq_adjointEdge
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointEdge_configurationDimension
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_adjoint_edge

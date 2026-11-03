import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval

/-! The four-colour multinomial count for the D4 Levi-level truncation targets. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- Multiplicities of the adjoint, two exterior-square colours, and the centre. -/
abbrev SiteMultiplicity := Fin 4 → ℕ

def siteMultiplicities (m : ℕ) : Finset SiteMultiplicity :=
  Finset.piAntidiag Finset.univ m

def siteDimension : Fin 4 → ℕ := ![15, 6, 6, 1]

def multiplicityGrade (t : SiteMultiplicity) : ℤ := (t 1 : ℤ) - t 2

def multiplicityLevel (t : SiteMultiplicity) : ℤ := 2 * (t 0 : ℤ) + t 1 + t 2

/-- The multinomial dimension of a colour configuration. -/
def configurationDimension (t : SiteMultiplicity) : ℕ :=
  Nat.multinomial Finset.univ t * 15 ^ t 0 * 6 ^ (t 1 + t 2)

/-- The target dimension at fixed vector-node grade and Levi coroot level. -/
def levelTarget (m : ℕ) (κ p : ℤ) : ℕ :=
  ∑ t ∈ (siteMultiplicities m).filter
    (fun t => multiplicityGrade t = κ ∧ multiplicityLevel t = p),
      configurationDimension t

/-- A finite rectangle containing all grade and level pairs of `m` sites. -/
def targetIndices (m : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc 0 (2 * (m : ℤ)))

theorem siteMultiplicity_sum (m : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities m) : t 0 + t 1 + t 2 + t 3 = m := by
  have hs := (Finset.mem_piAntidiag.mp ht).1
  simpa [Fin.sum_univ_succ, add_assoc] using hs

/-- The configuration weight is exactly the stated factorial quotient times the local ranks. -/
theorem configurationDimension_factorial (m : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities m) :
    configurationDimension t =
      (m.factorial / ((t 0).factorial * (t 1).factorial *
        (t 2).factorial * (t 3).factorial)) * 15 ^ t 0 * 6 ^ (t 1 + t 2) := by
  have hs := siteMultiplicity_sum m t ht
  simp only [configurationDimension, Nat.multinomial, Fin.sum_univ_succ,
    Fin.prod_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl,
    Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one]
  simp only [← add_assoc, ← mul_assoc, hs]

theorem configurationDimension_eq_product (t : SiteMultiplicity) :
    configurationDimension t = Nat.multinomial Finset.univ t *
      ∏ j : Fin 4, siteDimension j ^ t j := by
  simp [configurationDimension, siteDimension, Fin.prod_univ_succ, pow_add, mul_assoc]

/-- The four local dimensions add to the dimension of the D4 adjoint representation. -/
theorem siteDimension_sum : (∑ j : Fin 4, siteDimension j) = 28 := by
  decide

/-- The weighted four-colour multinomial count is `28^m`, uniformly in `m`. -/
theorem configurationDimension_sum (m : ℕ) :
    (∑ t ∈ siteMultiplicities m, configurationDimension t) = 28 ^ m := by
  simp_rw [configurationDimension_eq_product]
  exact (Finset.sum_pow_eq_sum_piAntidiag Finset.univ siteDimension m).symm.trans
    (congrArg (fun n : ℕ => n ^ m) siteDimension_sum)

theorem multiplicityIndex_mem (m : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities m) :
    (multiplicityGrade t, multiplicityLevel t) ∈ targetIndices m := by
  have hs := siteMultiplicity_sum m t ht
  have hs' : (t 0 : ℤ) + t 1 + t 2 + t 3 = m := by exact_mod_cast hs
  simp only [targetIndices, Finset.mem_product, Finset.mem_Icc,
    multiplicityGrade, multiplicityLevel]
  omega

/-- Summing over all grades and levels gives exactly the full four-colour count. -/
theorem levelTarget_total (m : ℕ) :
    (∑ i ∈ targetIndices m, levelTarget m i.1 i.2) = 28 ^ m := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := siteMultiplicities m) (t := targetIndices m)
    (g := fun t => (multiplicityGrade t, multiplicityLevel t))
    (multiplicityIndex_mem m) configurationDimension
  have heq : (∑ i ∈ targetIndices m, levelTarget m i.1 i.2) =
      ∑ t ∈ siteMultiplicities m, configurationDimension t := by
    simpa only [levelTarget, Prod.ext_iff] using hf
  exact heq.trans (configurationDimension_sum m)

/-- The double sum over the possible grade and level intervals is `28^m`. -/
theorem levelTarget_double_sum (m : ℕ) :
    (∑ κ ∈ Finset.Icc (-(m : ℤ)) m,
      ∑ p ∈ Finset.Icc (0 : ℤ) (2 * (m : ℤ)), levelTarget m κ p) = 28 ^ m := by
  simpa only [targetIndices, Finset.sum_product] using levelTarget_total m

theorem levelTarget_zero_of_outside (m : ℕ) (i : ℤ × ℤ)
    (hi : i ∉ targetIndices m) : levelTarget m i.1 i.2 = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨ht, hκ, hp⟩ := Finset.mem_filter.mp ht
  have hmem := multiplicityIndex_mem m t ht
  rw [hκ, hp] at hmem
  exact (hi hmem).elim

/-- Any finite selection of distinct grade and level targets has sum at most `28^m`. -/
theorem levelTarget_sum_le (m : ℕ) (s : Finset (ℤ × ℤ)) :
    (∑ i ∈ s, levelTarget m i.1 i.2) ≤ 28 ^ m := by
  have heq : (∑ i ∈ s, levelTarget m i.1 i.2) =
      ∑ i ∈ s ∩ targetIndices m, levelTarget m i.1 i.2 := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hnot
    apply levelTarget_zero_of_outside
    intro hmem
    exact hnot (Finset.mem_inter.mpr ⟨hi, hmem⟩)
  rw [heq, ← levelTarget_total m]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.siteMultiplicity_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.configurationDimension_factorial
#print axioms VOA.DeligneAudit.D4LevelReduction.configurationDimension_eq_product
#print axioms VOA.DeligneAudit.D4LevelReduction.siteDimension_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.configurationDimension_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.multiplicityIndex_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_total
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_double_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_zero_of_outside
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_sum_le

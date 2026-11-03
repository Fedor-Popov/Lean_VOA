import VOA.DeligneAudit.D4LevelReductionCoreNonSubsetBound

/-! The two configurations and the honest-pair cell count for a single adjoint site. -/

namespace VOA.DeligneAudit.D4LevelReduction

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- The configuration with one adjoint site and no negative exterior-square site. -/
def singleAdjointDirectMultiplicity (b c : ℕ) : SiteMultiplicity := ![1, b, 0, c]

/-- The configuration replacing the adjoint and one central site by an exterior-square pair. -/
def singleAdjointPairedMultiplicity (b c : ℕ) : SiteMultiplicity := ![0, b + 1, 1, c - 1]

/-- The direct configuration has the required total number of sites. -/
theorem singleAdjointDirectMultiplicity_mem (b c : ℕ) :
    singleAdjointDirectMultiplicity b c ∈ siteMultiplicities (1 + b + c) := by
  simp [siteMultiplicities, Finset.mem_piAntidiag, singleAdjointDirectMultiplicity,
    Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm]

/-- The paired configuration has the same site count when a central site is available. -/
theorem singleAdjointPairedMultiplicity_mem (b c : ℕ) (hc : 1 ≤ c) :
    singleAdjointPairedMultiplicity b c ∈ siteMultiplicities (1 + b + c) := by
  simp [siteMultiplicities, Finset.mem_piAntidiag, singleAdjointPairedMultiplicity,
    Fin.sum_univ_succ]
  omega

/-- There are exactly two possible colour configurations at a single-adjoint level. -/
theorem singleAdjointMultiplicity_cases (b c : ℕ) (t : SiteMultiplicity)
    (ht : t ∈ siteMultiplicities (1 + b + c)) (hg : multiplicityGrade t = b)
    (hl : multiplicityLevel t = (b : ℤ) + 2) :
    t = singleAdjointDirectMultiplicity b c ∨ t = singleAdjointPairedMultiplicity b c := by
  have hs := siteMultiplicity_sum (1 + b + c) t ht
  simp only [multiplicityGrade, multiplicityLevel] at hg hl
  have ht0 : t 0 = 1 ∨ t 0 = 0 := by omega
  rcases ht0 with ht0 | ht0
  · left
    have ht1 : t 1 = b := by omega
    have ht2 : t 2 = 0 := by omega
    have ht3 : t 3 = c := by omega
    funext i
    fin_cases i <;> simp [singleAdjointDirectMultiplicity, ht0, ht1, ht2, ht3]
  · right
    have ht1 : t 1 = b + 1 := by omega
    have ht2 : t 2 = 1 := by omega
    have ht3 : t 3 = c - 1 := by omega
    funext i
    fin_cases i <;> simp [singleAdjointPairedMultiplicity, ht0, ht1, ht2, ht3]

/-- The direct multinomial coefficient counts a complement subset and a marked site in it. -/
theorem singleAdjointDirect_multinomial (b c : ℕ) :
    Nat.multinomial Finset.univ (singleAdjointDirectMultiplicity b c) =
      (1 + b + c).choose (b + 1) * (b + 1) := by
  have hm := Nat.multinomial_spec Finset.univ (singleAdjointDirectMultiplicity b c)
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, singleAdjointDirectMultiplicity,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, Fin.sum_univ_zero,
    Nat.factorial_one, Nat.factorial_zero, one_mul, mul_one, add_zero] at hm
  have hc := Nat.choose_mul_factorial_mul_factorial
    (show b + 1 ≤ 1 + b + c by omega)
  have he : 1 + b + c - (b + 1) = c := by omega
  rw [he, Nat.factorial_succ] at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos c))
  calc
    (b.factorial * c.factorial) * Nat.multinomial Finset.univ
        (singleAdjointDirectMultiplicity b c) = (1 + b + c).factorial := by
      simpa only [add_assoc, zero_add] using hm
    _ = (b.factorial * c.factorial) * ((1 + b + c).choose (b + 1) * (b + 1)) := by
      rw [← hc]
      ring

/-- The paired multinomial coefficient counts a complement subset and a site outside it. -/
theorem singleAdjointPaired_multinomial (b c : ℕ) (hc : 1 ≤ c) :
    Nat.multinomial Finset.univ (singleAdjointPairedMultiplicity b c) =
      (1 + b + c).choose (b + 1) * c := by
  have hm := Nat.multinomial_spec Finset.univ (singleAdjointPairedMultiplicity b c)
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, singleAdjointPairedMultiplicity,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, Fin.sum_univ_zero,
    Nat.factorial_one, Nat.factorial_zero, one_mul, mul_one, add_zero, zero_add] at hm
  have ht : b + 1 + (1 + (c - 1)) = 1 + b + c := by omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial
    (show b + 1 ≤ 1 + b + c by omega)
  have he : 1 + b + c - (b + 1) = c := by omega
  rw [he, show c = (c - 1) + 1 by omega, Nat.factorial_succ] at hchoose
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (Nat.factorial_pos (b + 1)) (Nat.factorial_pos (c - 1)))
  calc
    ((b + 1).factorial * (c - 1).factorial) * Nat.multinomial Finset.univ
        (singleAdjointPairedMultiplicity b c) = (1 + b + c).factorial := by
      simpa only [ht] using hm
    _ = ((b + 1).factorial * (c - 1).factorial) *
        ((1 + b + c).choose (b + 1) * c) := by
      have hfac : c.factorial = c * (c - 1).factorial := by
        conv_lhs => rw [show c = (c - 1) + 1 by omega, Nat.factorial_succ]
        congr 1
        omega
      have hh := Nat.choose_mul_factorial_mul_factorial
        (show b + 1 ≤ 1 + b + c by omega)
      rw [he, hfac] at hh
      rw [← hh]
      ring

/-- The exact two-configuration target equals the sum of subset and non-subset cell costs. -/
theorem levelTarget_singleAdjoint (b c : ℕ) (hc : 1 ≤ c) :
    levelTarget (1 + b + c) b ((b : ℤ) + 2) =
      (1 + b + c).choose (b + 1) * ((b + 1) * 15 * 6 ^ b + c * 6 ^ (b + 2)) := by
  classical
  have he : (siteMultiplicities (1 + b + c)).filter
      (fun t => multiplicityGrade t = b ∧ multiplicityLevel t = (b : ℤ) + 2) =
        {singleAdjointDirectMultiplicity b c, singleAdjointPairedMultiplicity b c} := by
    ext t
    constructor
    · intro ht
      obtain ⟨ht, hg, hl⟩ := Finset.mem_filter.mp ht
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        singleAdjointMultiplicity_cases b c t ht hg hl
    · intro ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · refine Finset.mem_filter.mpr ⟨singleAdjointDirectMultiplicity_mem b c, ?_⟩
        simp [multiplicityGrade, multiplicityLevel, singleAdjointDirectMultiplicity, add_comm]
      · refine Finset.mem_filter.mpr ⟨singleAdjointPairedMultiplicity_mem b c hc, ?_⟩
        simp [multiplicityGrade, multiplicityLevel, singleAdjointPairedMultiplicity]
        omega
  have hne : singleAdjointDirectMultiplicity b c ≠ singleAdjointPairedMultiplicity b c := by
    intro ht
    have hh := congrFun ht 0
    simp [singleAdjointDirectMultiplicity, singleAdjointPairedMultiplicity] at hh
  rw [levelTarget, he, Finset.sum_pair hne]
  simp only [configurationDimension]
  rw [singleAdjointDirect_multinomial, singleAdjointPaired_multinomial b c hc]
  change (1 + b + c).choose (b + 1) * (b + 1) * 15 ^ 1 * 6 ^ (b + 0) +
    (1 + b + c).choose (b + 1) * c * 15 ^ 0 * 6 ^ (b + 1 + 1) = _
  simp only [pow_one, pow_zero, mul_one, add_zero]
  ring

/-- The rank contribution of an honest-pair cell with a singleton adjoint alphabet. -/
noncomputable def singleAdjointCellCost (b : ℕ) (d : SL4T.SiteCell) : ℕ :=
  if d.2 ⊆ d.1 then 15 * 6 ^ b else 6 ^ (b + 2)

/-- Marking a site gives the subset and exterior contributions with their exact multiplicities. -/
theorem singleAdjoint_markedSite_sum (m b : ℕ) (G : Finset ℕ) (hG : G ⊆ Finset.range m) :
    (∑ x ∈ Finset.range m, if x ∈ G then 15 * 6 ^ b else 6 ^ (b + 2)) =
      G.card * (15 * 6 ^ b) + (m - G.card) * 6 ^ (b + 2) := by
  classical
  have hyes : (Finset.range m).filter (fun x => x ∈ G) = G := by
    ext x
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hx => hG hx
  have hno : (Finset.range m).filter (fun x => x ∉ G) = Finset.range m \ G := by
    ext x
    simp
  rw [Finset.sum_ite, hyes, hno]
  simp [Finset.card_sdiff_of_subset hG]

/-- The ordered single-adjoint cell catalog has the claimed binomial total. -/
theorem singleAdjoint_cellCost_sum (b c : ℕ) :
    ((coreCellCatalog 1 b c).map (singleAdjointCellCost b)).sum =
      (1 + b + c).choose (b + 1) * ((b + 1) * 15 * 6 ^ b + c * 6 ^ (b + 2)) := by
  classical
  unfold coreCellCatalog
  rw [← List.sum_toFinset _ (SL4T.cellCatalog_nodup (1 + b + c) (1 + b) 1),
    SL4T.cellCatalog_toFinset, SL4T.cellSet, Finset.product_eq_sprod, Finset.sum_product]
  have he : ∀ G ∈ (Finset.range (1 + b + c)).powersetCard (1 + b),
      (∑ X ∈ (Finset.range (1 + b + c)).powersetCard 1, singleAdjointCellCost b (G, X)) =
        (b + 1) * 15 * 6 ^ b + c * 6 ^ (b + 2) := by
    intro G hG
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hG
    rw [Finset.powersetCard_one, Finset.sum_map]
    simp only [singleAdjointCellCost, Function.Embedding.coeFn_mk, Finset.singleton_subset_iff]
    rw [singleAdjoint_markedSite_sum _ _ G hsub, hcard]
    have hc' : 1 + b + c - (1 + b) = c := by omega
    rw [hc']
    ring
  rw [Finset.sum_congr rfl he]
  simp [Finset.card_powersetCard, Nat.add_comm, mul_assoc]

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjointDirectMultiplicity_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjointPairedMultiplicity_mem
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjointMultiplicity_cases
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjointDirect_multinomial
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjointPaired_multinomial
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_singleAdjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_markedSite_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_cellCost_sum

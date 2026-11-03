import VOA.DeligneAudit.D4CharMixedDownBranch

/-! The genuine last-variable constant term of mixed GT branching, coefficientwise. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- A shorter GT polynomial has no monomial in the deleted last variable. -/
theorem gtPoly_last_shift_zero (q : R) (N : ℕ) (μ : Fin N → ℤ)
    (p : ℕ →₀ ℤ) (hp : p N = 0) (d : ℤ) (hd : d ≠ 0) :
    gtPoly q N μ (-Finsupp.single N d + p) = 0 := by
  by_contra hn
  have hh := (gtPoly_support_bounds q N μ _ hn).1 N le_rfl
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.single_eq_same, hp, add_zero] at hh
  exact hd (neg_eq_zero.mp hh)

/-- Extracting the last-variable constant term retains exactly equal-size GT branches. -/
theorem gtPoly_last_zero_coeff (q : R) (N : ℕ) (lam : Fin (N + 1) → ℤ)
    (p : ℕ →₀ ℤ) (hp : p N = 0) :
    gtPoly q (N + 1) lam p =
      ∑ μ ∈ gtRows lam, if (∑ i, lam i) = ∑ i, μ i then
        gtPsi q lam μ * gtPoly q N μ p else 0 := by
  rw [gtPoly_coeff_succ]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hd : (∑ i, lam i) = ∑ i, μ i
  · simp [hd]
  · rw [if_neg hd, gtPoly_last_shift_zero q N μ p hp _ (sub_ne_zero.mpr hd), mul_zero]

/-- The mixed fifth-variable constant term has equal positive and negative size gains. -/
theorem gtMixedFive_last_zero_coeff (q : R) (a b c d : ℤ) (p : ℕ →₀ ℤ)
    (hp : p 4 = 0) :
    gtPoly q 5 (gtMixedFiveRow a b c d) p =
      ∑ α ∈ gtRows ![a, b, 0], ∑ β ∈ gtRows ![c, d, 0],
        if a + b - ∑ i, α i = c + d - ∑ i, β i then
          (gtPsi q ![a, b, 0] α * gtPsi q ![c, d, 0] β) *
            gtPoly q 4 (gtMixedFourRow (α 0) (α 1) (β 0) (β 1)) p else 0 := by
  rw [gtPoly_last_zero_coeff q 4 _ p hp, sum_gtMixedFiveRows]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β hβ
  have he := gtMixedFive_branch_degree a b c d α β
  have hd : (∑ i, gtMixedFiveRow a b c d i) =
      (∑ i, gtMixedFourRow (α 0) (α 1) (β 0) (β 1) i) ↔
        a + b - ∑ i, α i = c + d - ∑ i, β i := by
    simp only [Fin.sum_univ_two] at he ⊢
    omega
  simp only [hd, gtMixedFive_psi_factor q a b c d α β hβ]

/-- Both gains in the constant-term formula are nonnegative on every interlacing branch. -/
theorem gtMixedFive_branch_gains_nonneg (a b c d : ℤ) (α β : Fin 2 → ℤ)
    (hα : α ∈ gtRows ![a, b, 0]) (hβ : β ∈ gtRows ![c, d, 0]) :
    0 ≤ a + b - ∑ i, α i ∧ 0 ≤ c + d - ∑ i, β i := by
  have h₀ := (mem_gtRows _ _).mp hα 0
  have h₁ := (mem_gtRows _ _).mp hα 1
  have h₂ := (mem_gtRows _ _).mp hβ 0
  have h₃ := (mem_gtRows _ _).mp hβ 1
  change b ≤ α 0 ∧ α 0 ≤ a at h₀
  change 0 ≤ α 1 ∧ α 1 ≤ b at h₁
  change d ≤ β 0 ∧ β 0 ≤ c at h₂
  change 0 ≤ β 1 ∧ β 1 ≤ d at h₃
  simp only [Fin.sum_univ_two]
  omega

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPoly_last_shift_zero
#print axioms VOA.DeligneAudit.D4Char.gtPoly_last_zero_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_last_zero_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_branch_gains_nonneg

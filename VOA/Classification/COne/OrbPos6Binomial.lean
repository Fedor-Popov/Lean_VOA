import VOA.Moonshine.HeisenbergTwistedModuleReduction

/-! # Composition of the finite binomial corrections -/

namespace VOA.Classification.COne.OrbPos6
open VOA TwistedReduction

/-- Vandermonde for a truncated two-index vector-valued family. -/
theorem binomial_convolution {M : Type*} [AddCommGroup M] [Module ℂ M]
    (b c : ℂ) (P Q : ℤ → ℤ → M) (L : ℤ)
    (hP : ∀ ℓ s, L ≤ ℓ → P ℓ s = 0)
    (hQ : ∀ ℓ s, L ≤ ℓ → Q ℓ s = 0)
    (hPQ : ∀ ℓ s, Q ℓ s = ∑ᶠ i : ℕ, cbinom c i • P (ℓ + i) (s - i)) (ℓ s : ℤ) :
    (∑ᶠ d : ℕ, cbinom b d • Q (ℓ + d) (s - d)) =
      ∑ᶠ d : ℕ, cbinom (b + c) d • P (ℓ + d) (s - d) := by
  let K : ℕ := (L - ℓ).toNat
  rw [finsum_nat_eq_sum_range K _ (fun d hd => by
    rw [hQ _ _ (by dsimp [K] at hd; omega), smul_zero]),
    finsum_nat_eq_sum_range K _ (fun d hd => by
    rw [hP _ _ (by dsimp [K] at hd; omega), smul_zero])]
  have hQ' (d : ℕ) : Q (ℓ + d) (s - d) =
      ∑ i ∈ Finset.range K, cbinom c i • P (ℓ + d + i) (s - d - i) := by
    rw [hPQ, finsum_nat_eq_sum_range K _ (fun i hi => by
      rw [hP _ _ (by dsimp [K] at hi; omega), smul_zero])]
  simp_rw [hQ', Finset.smul_sum, smul_smul]
  rw [sum_range_sq_eq_sum_antidiagonal K
    (fun d i => (cbinom b d * cbinom c i) • P (ℓ + d + i) (s - d - i))
    (fun d i h => by
      change (cbinom b d * cbinom c i) • P (ℓ + d + i) (s - d - i) = 0
      rw [hP _ _ (by dsimp [K] at h; omega), smul_zero])]
  apply Finset.sum_congr rfl
  intro k hk
  rw [cbinom_add, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp]
  congr 2 <;> push_cast <;> ring

end VOA.Classification.COne.OrbPos6

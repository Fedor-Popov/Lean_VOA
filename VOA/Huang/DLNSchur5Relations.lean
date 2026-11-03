import VOA.Huang.DLNSchur5Field

/-! # Strictly smaller large-prime residuals

The generator relation is settled for primes congruent to one modulo four.
The field boundary follows from the generator relation. The residual below retains
only the complementary primes for symbols and exponents at least two for boundaries.
-/

namespace VOA.Huang.DLNSchur

/-- The remaining generator obligations, restricted to `p = 3 mod 4`.
This is a TRUE restriction of the larger residual, not an asserted theorem. -/
def LargePrimeTorusGeneratorRelationsModFourThree : Prop :=
  ∀ p k : ℕ, ∀ hp : p.Prime, ∀ hp5 : 5 ≤ p, p % 4 = 3 → 0 < k →
    TorusGeneratorRelations (p ^ k) (primePower_coprime_two_three hp hp5).1

/-- The remaining boundary obligations, restricted to genuine prime powers.
This is a TRUE restriction of the larger residual, not an asserted theorem. -/
def LargePrimeGaussBoundaryRelationsHigher : Prop :=
  ∀ p k : ℕ, ∀ hp : p.Prime, ∀ hp5 : 5 ≤ p, 2 ≤ k →
    GaussBoundaryRelations (p ^ k) (primePower_coprime_two_three hp hp5).1

/-- Exact removal of the generator subfamily proved in this file. -/
theorem largePrimeTorusGeneratorRelations_iff_mod_four_three :
    LargePrimeTorusGeneratorRelations ↔ LargePrimeTorusGeneratorRelationsModFourThree := by
  constructor
  · intro h p k hp hp5 _ hk
    exact h p k hp hp5 hk
  · intro h p k hp hp5 hk
    by_cases hp4 : p % 4 = 1
    · exact torusGeneratorRelations_primePower_mod_four_one hp hp5 hp4 hk
    · obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
      exact h p k hp hp5 (by omega) hk

/-- After solving the generator relation, only higher-power boundaries remain. -/
theorem largePrimeGaussBoundaryRelations_of_generator_and_higher
    (ht : LargePrimeTorusGeneratorRelations)
    (hb : LargePrimeGaussBoundaryRelationsHigher) : LargePrimeGaussBoundaryRelations := by
  intro p k hp hp5 hk
  by_cases hk2 : 2 ≤ k
  · exact hb p k hp hp5 hk2
  · have hk1 : k = 1 := by omega
    subst k
    have h2 : Nat.Coprime 2 p := by
      simpa only [pow_one] using (primePower_coprime_two_three (k := 1) hp hp5).1
    have h3 : Nat.Coprime 3 p := by
      simpa only [pow_one] using (primePower_coprime_two_three (k := 1) hp hp5).2
    have htp : TorusGeneratorRelations p h2 := by
      simpa only [pow_one] using ht p 1 hp hp5 (by omega)
    have hl := gaussLowerRelations_prime_of_torusGeneratorRelations hp h2 h3 htp
    have hbp : GaussBoundaryRelations p h2 := by
      intro E _ π hs hc X Y hX hY hgen hn g _
      exact hl E π hs hc X Y hX hY hgen hn g
    simpa only [pow_one] using hbp

/-- Exact remaining work: the complementary generator family and higher-power boundaries. -/
theorem largePrimeRootRelations_iff_mod_four_three_and_higher_boundary :
    LargePrimeRootRelations ↔
      LargePrimeTorusGeneratorRelationsModFourThree ∧ LargePrimeGaussBoundaryRelationsHigher := by
  rw [largePrimeRootRelations_iff_gaussLowerRelations,
    largePrimeGaussLowerRelations_iff_generator_and_boundary]
  constructor
  · rintro ⟨ht, hb⟩
    exact ⟨largePrimeTorusGeneratorRelations_iff_mod_four_three.mp ht,
      fun p k hp hp5 hk => hb p k hp hp5 (by omega)⟩
  · rintro ⟨ht, hb⟩
    have ht' := largePrimeTorusGeneratorRelations_iff_mod_four_three.mpr ht
    exact ⟨ht', largePrimeGaussBoundaryRelations_of_generator_and_higher ht' hb⟩

/-- Conditional DLN assembly with the genuinely reduced large-prime obligations. -/
theorem matrixDLNLifting_of_session5_remaining
    (ht : LargePrimeTorusGeneratorRelationsModFourThree)
    (hb : LargePrimeGaussBoundaryRelationsHigher)
    (hthree : ThreePowerSchur) (htwo : TwoPowerInflationFromTwo) :
    VOA.Huang.DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_rootRelations
    (largePrimeRootRelations_iff_mod_four_three_and_higher_boundary.mpr ⟨ht, hb⟩) hthree htwo

end VOA.Huang.DLNSchur

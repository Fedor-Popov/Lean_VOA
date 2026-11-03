import VOA.DeligneAudit.D4CharMixedTwoCoeff

/-! The local mixed shift after extracting both negative-block degrees. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Fixed x_1 and y degrees, before restricting the remaining homogeneous degree. -/
def gtMixedWeight (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) : R :=
  gtTwoWeight q h r (lam 0) (lam 1) *
    if lam 2 = 0 then gtTwoCoeff q h t v (-lam 4) (-lam 3) else 0

theorem gtMixedWeight_seed (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) :
    gtMixedWeight q h r t v lam =
      gtInvPoch q h r * gtMixedSeed q h r (gtMixedTailCoeff q h t v) lam := by
  simp only [gtMixedWeight, gtMixedSeed, ← mul_assoc, gtTwoWeight_normalized]
  rfl

theorem gtMixedWeight_support (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) (hn : gtMixedWeight q h r t v lam ≠ 0) :
    0 ≤ lam 1 ∧ lam 1 ≤ r ∧ (r : ℤ) ≤ lam 0 ∧ lam 2 = 0 ∧
      0 ≤ -lam 3 ∧ -lam 3 ≤ t ∧ t ≤ -lam 4 ∧ -lam 3 ≤ v ∧
        -lam 4 + -lam 3 = t + v := by
  unfold gtMixedWeight at hn
  have hh := left_ne_zero_of_mul hn
  have ht := right_ne_zero_of_mul hn
  obtain ⟨hb, hbr, hra⟩ := gtTwoWeight_support q h r (lam 0) (lam 1) hh
  split_ifs at ht with hz
  · obtain ⟨hd, h₀, h₁, h₂, h₃⟩ := gtTwoCoeff_support q h t v (-lam 4) (-lam 3) ht
    exact ⟨hb, hbr, hra, hz, h₀, h₁, h₂, h₃, hd⟩
  · exact (ht rfl).elim

theorem gtMixedWeight_dominant (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) (hn : gtMixedWeight q h r t v lam ≠ 0) : Antitone lam := by
  obtain ⟨hb, hbr, hra, hz, h₀, h₁, h₂, h₃, hd⟩ :=
    gtMixedWeight_support q h r t v lam hn
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  fin_cases i
  · change lam 1 ≤ lam 0
    omega
  · change lam 2 ≤ lam 1
    omega
  · change lam 3 ≤ lam 2
    omega
  · change lam 4 ≤ lam 3
    omega

theorem gtMixedWeight_sum (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) (hn : gtMixedWeight q h r t v lam ≠ 0) :
    (∑ i, lam i) = lam 0 + lam 1 - t - v := by
  obtain ⟨_, _, _, hz, _, _, _, _, hd⟩ := gtMixedWeight_support q h r t v lam hn
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc] at *
  omega

theorem gtMixedWeight_nonneg (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ)
    (lam : Fin 5 → ℤ) (hn : gtMixedWeight q h r t v lam ≠ 0)
    (hd : (∑ i, lam i) = r + s - t - v) : 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ v := by
  have he := gtMixedWeight_sum q h r t v lam hn
  obtain ⟨hb, hbr, hra, hz, h₀, h₁, h₂, h₃, ht⟩ :=
    gtMixedWeight_support q h r t v lam hn
  omega

/-- X times Y with both y coefficients extracted; every integer output row is included. -/
theorem gtMixedWeight_subsets (q : R) (h : PochhammerUnits q) (r : ℕ) (t v : ℤ)
    (lam : Fin 5 → ℤ) :
    (∑ S : Finset (Fin 5), (-1) ^ S.card *
      gtMixedWeight q h r t v (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ (lam 0 + lam 1 - r).toNat *
        (gtMixedWeight q h r t v lam - gtMixedWeight q h r (t - 1) v lam -
          gtMixedWeight q h r t (v - 1) lam +
            gtMixedWeight q h r (t - 1) (v - 1) lam) := by
  have hh := congrArg (fun x : R => gtInvPoch q h r * x)
    (gtMixedSeed_subsets q h r 2 (gtMixedTailCoeff q h t v) lam)
  simp only [Finset.mul_sum] at hh
  calc
    _ = gtInvPoch q h r *
        (q ^ (lam 0 + lam 1 - r).toNat * gtQCoeff q h ![lam 0, lam 1] ![(r : ℤ)] *
          if lam 2 = 0 then gtMixedTailAction q (gtMixedTailCoeff q h t v)
            (fun i => lam i.succ.succ.succ) else 0) := by
      rw [← hh]
      apply Finset.sum_congr rfl
      intro S _
      rw [gtMixedWeight_seed]
      ring
    _ = _ := by
      have ht : (fun i : Fin 2 => lam i.succ.succ.succ) = ![-(-lam 3), -(-lam 4)] := by
        ext i
        fin_cases i <;> simp
      rw [ht, gtMixedTailAction_coeff]
      by_cases hz : lam 2 = 0
      · simp only [gtMixedWeight, if_pos hz]
        rw [show gtInvPoch q h r *
            (q ^ (lam 0 + lam 1 - r).toNat * gtQCoeff q h ![lam 0, lam 1] ![(r : ℤ)] *
              (gtTwoCoeff q h t v (-lam 4) (-lam 3) -
                gtTwoCoeff q h (t - 1) v (-lam 4) (-lam 3) -
                gtTwoCoeff q h t (v - 1) (-lam 4) (-lam 3) +
                gtTwoCoeff q h (t - 1) (v - 1) (-lam 4) (-lam 3))) =
            q ^ (lam 0 + lam 1 - r).toNat *
              (gtInvPoch q h r * gtQCoeff q h ![lam 0, lam 1] ![(r : ℤ)]) *
                (gtTwoCoeff q h t v (-lam 4) (-lam 3) -
                  gtTwoCoeff q h (t - 1) v (-lam 4) (-lam 3) -
                  gtTwoCoeff q h t (v - 1) (-lam 4) (-lam 3) +
                  gtTwoCoeff q h (t - 1) (v - 1) (-lam 4) (-lam 3)) by ring]
        rw [gtTwoWeight_normalized]
        ring
      · simp [gtMixedWeight, hz]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_seed
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_support
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_dominant
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_sum
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_nonneg
#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_subsets

import VOA.DeligneAudit.D4CharMixedFiveLocal

/-! The stable mixed-Cauchy local equation on every dominant GL_5 output row. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- A dominant row with zero middle entry has precisely the mixed partition shape. -/
theorem gtMixedFive_shape (lam : Fin 5 → ℤ) (hlam : Antitone lam) (hz : lam 2 = 0) :
    ∃ c d : ℕ, d ≤ c ∧ lam = gtMixedFiveRow (lam 0) (lam 1) c d := by
  have h₃ : lam 3 ≤ 0 := (hlam (show (2 : Fin 5) ≤ 3 by decide)).trans_eq hz
  have h₄ : lam 4 ≤ lam 3 := hlam (show (3 : Fin 5) ≤ 4 by decide)
  refine ⟨(-lam 4).toNat, (-lam 3).toNat, by omega, ?_⟩
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hz
  · change lam 3 = -((-lam 3).toNat : ℤ)
    omega
  · change lam 4 = -((-lam 4).toNat : ℤ)
    omega

theorem gtMixedSeed_five (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (a b r : ℤ) (c d : ℕ) :
    gtMixedSeed q h r (gtNegativeQTwo q h y) (gtMixedFiveRow a b c d) =
      gtQCoeff q h ![a, b] ![r] * gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  have ht : (fun i : Fin 2 => gtMixedFiveRow a b c d i.succ.succ.succ) =
      ![-(d : ℤ), -(c : ℤ)] := by
    ext i
    fin_cases i <;> rfl
  unfold gtMixedSeed
  rw [ht, gtNegativeQTwo_eval]
  simp [gtMixedFiveRow]

/-- X, B and Y assembled on every dominant output, including every bad middle row. -/
theorem gtMixedFive_local (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (r : ℤ) (lam : Fin 5 → ℤ) (hlam : Antitone lam) :
    (∑ S : Finset (Fin 5), (-1) ^ S.card *
      gtMixedSeed q h r (gtNegativeQTwo q h y) (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ (lam 0 + lam 1 - r).toNat * ((1 - (y 0 : R)) * (1 - (y 1 : R))) *
        gtMixedSeed q h r (gtNegativeQTwo q h y) lam := by
  by_cases hz : lam 2 = 0
  · obtain ⟨c, d, hd, he⟩ := gtMixedFive_shape lam hlam hz
    have hs := gtMixedFive_good q h y (lam 0) (lam 1) r c d hd
    rw [he, gtMixedSeed_five]
    convert hs using 1
    simp only [gtMixedFiveRow, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · rw [gtMixedSeed_bad_middle q h r 2 (gtNegativeQTwo q h y) lam hz]
    simp [gtMixedSeed, hz]

/-- The same local equation with the normalization of the fixed first x-degree. -/
theorem gtMixedFive_local_normalized (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (r : ℕ) (lam : Fin 5 → ℤ) (hlam : Antitone lam) :
    (∑ S : Finset (Fin 5), (-1) ^ S.card *
      (gtInvPoch q h r * gtMixedSeed q h r (gtNegativeQTwo q h y)
        (gtLowerSubset lam S)) * pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ (lam 0 + lam 1 - r).toNat * ((1 - (y 0 : R)) * (1 - (y 1 : R))) *
        (gtInvPoch q h r * gtMixedSeed q h r (gtNegativeQTwo q h y) lam) := by
  have hs := congrArg (fun x : R => gtInvPoch q h r * x)
    (gtMixedFive_local q h y r lam hlam)
  simp only [Finset.mul_sum] at hs
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro S _
    ring
  · ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_shape
#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_five
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_local
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_local_normalized

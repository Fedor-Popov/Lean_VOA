import VOA.DeligneAudit.D4CharMixedNegative

/-! The local X times Y identity at the only stable mixed rank needed by D4. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The stable GL_5 mixed weight [kappa,rho]_5, for arbitrary integer entries. -/
def gtMixedFiveRow (a b c d : ℤ) : Fin 5 → ℤ := ![a, b, 0, -d, -c]

/-- The actual negative-partition evaluation, extended by zero to positive tail entries. -/
def gtNegativeQTwo (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (μ : Fin 2 → ℤ) : R :=
  if μ 0 ≤ 0 ∧ μ 1 ≤ 0 then gtQ q h y 2 (gtDual μ) else 0

theorem gtNegativeQTwo_eval (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (c d : ℕ) : gtNegativeQTwo q h y ![-(d : ℤ), -(c : ℤ)] =
      gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  have he : gtDual (![-(d : ℤ), -(c : ℤ)] : Fin 2 → ℤ) =
      ![(c : ℤ), (d : ℤ)] := by
    ext i
    fin_cases i <;> simp [gtDual]
  simp [gtNegativeQTwo, he]

/-- The negative-block identity is valid for the zero-extended partition function. -/
theorem gtMixedTailAction_negativeQTwo (q : R) (h : PochhammerUnits q)
    (y : ℕ → Rˣ) (c d : ℕ) (hd : d ≤ c) :
    gtMixedTailAction q (gtNegativeQTwo q h y) ![-(d : ℤ), -(c : ℤ)] =
      (1 - (y 0 : R)) * (1 - (y 1 : R)) * gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  rw [← gtMixedTailAction_Q_two q h y c d hd]
  unfold gtMixedTailAction
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply if_pos
  have hs (i : Fin 2) : 0 ≤ pieriBit (s i) := by cases s i <;> decide
  change -(d : ℤ) - pieriBit (s 0) ≤ 0 ∧ -(c : ℤ) - pieriBit (s 1) ≤ 0
  constructor <;> linarith [hs 0, hs 1]

/-- The good-row local mixed-Cauchy comparison at GL_5, for every pair of partitions. -/
theorem gtMixedFive_good (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (a b r : ℤ) (c d : ℕ) (hd : d ≤ c) :
    (∑ S : Finset (Fin 5), (-1) ^ S.card *
      gtMixedSeed q h r (gtNegativeQTwo q h y)
        (gtLowerSubset (gtMixedFiveRow a b c d) S) *
      pieriCoeff q (gtLowerSubset (gtMixedFiveRow a b c d) S) S) =
      q ^ (a + b - r).toNat * gtQCoeff q h ![a, b] ![r] *
        ((1 - (y 0 : R)) * (1 - (y 1 : R))) * gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  rw [gtMixedSeed_subsets]
  have ht : (fun i : Fin 2 => gtMixedFiveRow a b c d i.succ.succ.succ) =
      ![-(d : ℤ), -(c : ℤ)] := by
    ext i
    fin_cases i <;> rfl
  rw [ht, gtMixedTailAction_negativeQTwo q h y c d hd]
  simp [gtMixedFiveRow, mul_assoc]

/-- The same identity in the x_1 coefficient normalization of C(2,N). -/
theorem gtMixedFive_good_normalized (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (a b : ℤ) (r c d : ℕ) (hd : d ≤ c) :
    (∑ S : Finset (Fin 5), (-1) ^ S.card *
      (gtInvPoch q h r * gtMixedSeed q h r (gtNegativeQTwo q h y)
        (gtLowerSubset (gtMixedFiveRow a b c d) S)) *
      pieriCoeff q (gtLowerSubset (gtMixedFiveRow a b c d) S) S) =
      q ^ (a + b - r).toNat * (gtInvPoch q h r * gtQCoeff q h ![a, b] ![r]) *
        ((1 - (y 0 : R)) * (1 - (y 1 : R))) * gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  have hs := congrArg (fun x : R => gtInvPoch q h r * x)
    (gtMixedFive_good q h y a b r c d hd)
  simp only [Finset.mul_sum] at hs
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro S _
    ring
  · ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtNegativeQTwo_eval
#print axioms VOA.DeligneAudit.D4Char.gtMixedTailAction_negativeQTwo
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_good
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_good_normalized

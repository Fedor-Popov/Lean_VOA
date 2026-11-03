import VOA.DeligneAudit.D4CharMixedFiveUnique

/-! Integer-degree coefficients for the negative two-row block of mixed Cauchy. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The normalized one-variable branching coefficient, extended to all integer degrees. -/
def gtTwoWeight (q : R) (h : PochhammerUnits q) (r a b : ℤ) : R :=
  gtInvPoch q h (a - r) * gtInvPoch q h (r - b) * gtInvPoch q h b

theorem gtTwoWeight_support (q : R) (h : PochhammerUnits q) (r a b : ℤ)
    (hn : gtTwoWeight q h r a b ≠ 0) : 0 ≤ b ∧ b ≤ r ∧ r ≤ a := by
  have ha : 0 ≤ a - r := by
    by_contra ha
    exact hn (by simp [gtTwoWeight, gtInvPoch_of_neg q h (show a - r < 0 by omega)])
  have hb : 0 ≤ r - b := by
    by_contra hb
    exact hn (by simp [gtTwoWeight, gtInvPoch_of_neg q h (show r - b < 0 by omega)])
  have hc : 0 ≤ b := by
    by_contra hc
    exact hn (by simp [gtTwoWeight, gtInvPoch_of_neg q h (show b < 0 by omega)])
  exact ⟨hc, by omega, by omega⟩

theorem gtTwoWeight_normalized (q : R) (h : PochhammerUnits q) (r : ℕ) (a b : ℤ) :
    gtInvPoch q h r * gtQCoeff q h ![a, b] ![(r : ℤ)] =
      gtTwoWeight q h r a b := by
  simp only [gtQCoeff_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.toNat_natCast, gtTwoWeight]
  have hh := gtPoch_mul_invPoch q h r
  linear_combination
    (gtInvPoch q h (a - r) * gtInvPoch q h (r - b) * gtInvPoch q h b) * hh

/-- Coefficientwise normalized e_1-Pieri, including all integer boundary cases. -/
theorem gtTwoWeight_eOne (q : R) (h : PochhammerUnits q) (r a b : ℤ) :
    (1 - q ^ (a - b + 1).toNat) * gtTwoWeight q h r (a + 1) b +
      (1 - q ^ (b + 1).toNat) * gtTwoWeight q h r a (b + 1) =
        gtTwoWeight q h (r - 1) a b + gtTwoWeight q h r a b := by
  unfold gtTwoWeight
  have h₁ : a - (r - 1) = a + 1 - r := by omega
  have h₂ : r - (b + 1) = r - b - 1 := by omega
  have h₃ : r - 1 - b = r - b - 1 := by omega
  rw [h₁, h₂, h₃]
  by_cases ha : a + 1 - r < 0
  · rw [gtInvPoch_of_neg q h ha, gtInvPoch_of_neg q h (show a - r < 0 by omega)]
    ring
  · by_cases hb : r - b < 0
    · rw [gtInvPoch_of_neg q h hb,
        gtInvPoch_of_neg q h (show r - b - 1 < 0 by omega)]
      ring
    · have he : (a - b + 1).toNat = (a + 1 - r).toNat + (r - b).toNat := by omega
      have hl : a - r = (a + 1 - r) - 1 := by omega
      rw [hl, gtInvPoch_lower q h (a + 1 - r), gtInvPoch_lower q h (r - b),
        he, pow_add, ← gtInvPoch_raise q h b]
      ring

/-- Coefficientwise normalized e_2-Pieri. -/
theorem gtTwoWeight_eTwo (q : R) (h : PochhammerUnits q) (r a b : ℤ) :
    (1 - q ^ (b + 1).toNat) * gtTwoWeight q h r (a + 1) (b + 1) =
      gtTwoWeight q h (r - 1) a b := by
  unfold gtTwoWeight
  rw [show a - (r - 1) = a + 1 - r by omega,
    show r - 1 - b = r - (b + 1) by omega]
  calc
    _ = gtInvPoch q h (a + 1 - r) * gtInvPoch q h (r - (b + 1)) *
        ((1 - q ^ (b + 1).toNat) * gtInvPoch q h (b + 1)) := by ring
    _ = _ := by rw [gtInvPoch_raise]

/-- The coefficient of y_1^t y_2^v in Q_(a,b), zero outside its homogeneous degree. -/
def gtTwoCoeff (q : R) (h : PochhammerUnits q) (t v a b : ℤ) : R :=
  if a + b = t + v then gtTwoWeight q h t a b else 0

theorem gtTwoCoeff_support (q : R) (h : PochhammerUnits q) (t v a b : ℤ)
    (hn : gtTwoCoeff q h t v a b ≠ 0) :
    a + b = t + v ∧ 0 ≤ b ∧ b ≤ t ∧ t ≤ a ∧ b ≤ v := by
  unfold gtTwoCoeff at hn
  split_ifs at hn with hd
  · obtain ⟨hb, hbt, hta⟩ := gtTwoWeight_support q h t a b hn
    exact ⟨hd, hb, hbt, hta, by omega⟩
  · exact (hn rfl).elim

/-- The negative tail is zero extended automatically by reciprocal Pochhammers. -/
def gtMixedTailCoeff (q : R) (h : PochhammerUnits q) (t v : ℤ)
    (μ : Fin 2 → ℤ) : R := gtTwoCoeff q h t v (-μ 1) (-μ 0)

theorem gtMixedTailCoeff_pair (q : R) (h : PochhammerUnits q) (t v a b : ℤ) :
    gtMixedTailCoeff q h t v ![-b, -a] = gtTwoCoeff q h t v a b := by
  simp [gtMixedTailCoeff]

/-- Extracting both y degrees in Y produces the full four-term Euler denominator. -/
theorem gtMixedTailAction_coeff (q : R) (h : PochhammerUnits q) (t v a b : ℤ) :
    gtMixedTailAction q (gtMixedTailCoeff q h t v) ![-b, -a] =
      gtTwoCoeff q h t v a b - gtTwoCoeff q h (t - 1) v a b -
        gtTwoCoeff q h t (v - 1) a b + gtTwoCoeff q h (t - 1) (v - 1) a b := by
  rw [gtMixedTailAction_two]
  simp only [show -b - 1 = -(b + 1) by ring, show -a - 1 = -(a + 1) by ring,
    gtMixedTailCoeff_pair]
  have h₁ : a + 1 + b = t + v ↔ a + b = t - 1 + v := by omega
  have h₂ : a + (b + 1) = t + v ↔ a + b = t - 1 + v := by omega
  have h₃ : a + b = t + (v - 1) ↔ a + b = t - 1 + v := by omega
  have h₄ : a + 1 + (b + 1) = t + v ↔ a + b = t - 1 + (v - 1) := by omega
  simp only [gtTwoCoeff, h₁, h₂, h₃, h₄]
  split_ifs <;> solve
  | omega
  | ring
  | linear_combination -(gtTwoWeight_eOne q h t a b)
  | linear_combination gtTwoWeight_eTwo q h t a b

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtTwoWeight_support
#print axioms VOA.DeligneAudit.D4Char.gtTwoWeight_normalized
#print axioms VOA.DeligneAudit.D4Char.gtTwoWeight_eOne
#print axioms VOA.DeligneAudit.D4Char.gtTwoWeight_eTwo
#print axioms VOA.DeligneAudit.D4Char.gtTwoCoeff_support
#print axioms VOA.DeligneAudit.D4Char.gtMixedTailCoeff_pair
#print axioms VOA.DeligneAudit.D4Char.gtMixedTailAction_coeff

import VOA.DeligneAudit.D4CharInvPoch

/-!
The two-state recursion for X and B at rank two. All three row entries are arbitrary
integers: in particular the non-interlaced boundary is part of each statement.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtQCoeff_one (q : R) (h : PochhammerUnits q)
    (lam : Fin 1 → ℤ) (μ : Fin 0 → ℤ) :
    gtQCoeff q h lam μ = gtInvPoch q h (lam 0) := by
  simp [gtQCoeff]

theorem gtQCoeff_two (q : R) (h : PochhammerUnits q)
    (lam : Fin 2 → ℤ) (μ : Fin 1 → ℤ) :
    gtQCoeff q h lam μ = CarrierChain.qpochGen q (μ 0).toNat *
      gtInvPoch q h (lam 0 - μ 0) * gtInvPoch q h (μ 0 - lam 1) *
        gtInvPoch q h (lam 1) := by
  have hg : gtGap μ 0 = (μ 0).toNat := gtGap_last μ
  simp [gtQCoeff, hg]

/-- State zero: the sum over whether the first box was removed. -/
theorem gtQ_two_state_zero (q : R) (h : PochhammerUnits q) (a b c : ℤ) :
    gtQCoeff q h ![a, b] ![c] - gtQCoeff q h ![a - 1, b] ![c] =
      q ^ (a - c).toNat * gtQCoeff q h ![a, b] ![c] := by
  simp only [gtQCoeff_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show a - 1 - c = a - c - 1 by omega, gtInvPoch_lower]
  ring

/-- State one: the cancellation includes the gap c - b = -1 without division by zero. -/
theorem gtQ_two_state_one (q : R) (h : PochhammerUnits q) (a b c : ℤ) :
    gtQCoeff q h ![a - 1, b - 1] ![c] -
        (1 - q ^ (a - b + 1).toNat) * gtQCoeff q h ![a, b - 1] ![c] =
      -(1 - q ^ b.toNat) * (q ^ (a - c).toNat * gtQCoeff q h ![a, b] ![c]) := by
  simp only [gtQCoeff_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases ha : a - c < 0
  · rw [gtInvPoch_of_neg q h ha, gtInvPoch_of_neg q h (show a - 1 - c < 0 by omega)]
    ring
  · by_cases hb : c - b + 1 < 0
    · rw [gtInvPoch_of_neg q h (show c - (b - 1) < 0 by omega),
        gtInvPoch_of_neg q h (show c - b < 0 by omega)]
      ring
    · have he : (a - b + 1).toNat = (a - c).toNat + (c - b + 1).toNat := by omega
      rw [show a - 1 - c = a - c - 1 by omega,
        show c - (b - 1) = c - b + 1 by omega,
        gtInvPoch_lower q h (a - c), gtInvPoch_lower q h b, he, pow_add,
        ← gtInvPoch_raise q h (c - b)]
      ring

/-- Identity B in its two-state form, on every integer row. -/
theorem gtQ_two_state_boundary (q : R) (h : PochhammerUnits q) (a b c : ℤ) :
    (1 - q ^ b.toNat) *
        (gtQCoeff q h ![a, b] ![c] - gtQCoeff q h ![a - 1, b] ![c]) +
      (gtQCoeff q h ![a - 1, b - 1] ![c] -
        (1 - q ^ (a - b + 1).toNat) * gtQCoeff q h ![a, b - 1] ![c]) = 0 := by
  rw [gtQ_two_state_zero, gtQ_two_state_one]
  ring

/-- Identity X in its two-state form, including every zero-extended boundary. -/
theorem gtQ_two_state_total (q : R) (h : PochhammerUnits q) (a b c : ℤ) :
    (gtQCoeff q h ![a, b] ![c] - gtQCoeff q h ![a - 1, b] ![c]) +
      (gtQCoeff q h ![a - 1, b - 1] ![c] -
        (1 - q ^ (a - b + 1).toNat) * gtQCoeff q h ![a, b - 1] ![c]) =
      q ^ (a + b - c).toNat * gtQCoeff q h ![a, b] ![c] := by
  rw [gtQ_two_state_zero, gtQ_two_state_one]
  by_cases ha : a - c < 0
  · have hz : gtQCoeff q h ![a, b] ![c] = 0 := by
      simp [gtQCoeff_two, gtInvPoch_of_neg q h ha]
    simp [hz]
  · by_cases hb : b < 0
    · have hz : gtQCoeff q h ![a, b] ![c] = 0 := by
        simp [gtQCoeff_two, gtInvPoch_of_neg q h hb]
      simp [hz]
    · have he : (a + b - c).toNat = (a - c).toNat + b.toNat := by omega
      rw [he, pow_add]
      ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_one
#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_two
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_state_zero
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_state_one
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_state_boundary
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_state_total

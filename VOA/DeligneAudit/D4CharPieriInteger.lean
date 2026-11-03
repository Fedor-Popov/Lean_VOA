import VOA.DeligneAudit.D4CharPieriDominance

/-!
# Gaussian entries with integer boundary indices

The zero extension is essential: `Int.toNat` alone would turn a negative lower index into
zero and give a spurious coefficient one. All identities below include every integer lower
index. These are the four local weights and balance relation used in STEP2, Lemma E.
-/

namespace VOA.DeligneAudit.D4Char

open VOA.DeligneGaussian

variable {R : Type*} [CommRing R]

/-- Gaussian binomials extended by zero to negative upper or lower indices. -/
def intQbinom (q : R) (a b : ℤ) : R :=
  if 0 ≤ a ∧ 0 ≤ b then qbinom q a.toNat b.toNat else 0

@[simp] theorem intQbinom_nat (q : R) (a b : ℕ) :
    intQbinom q a b = qbinom q a b := by
  simp [intQbinom]

theorem intQbinom_lower_neg (q : R) (a b : ℤ) (hb : b < 0) :
    intQbinom q a b = 0 := by
  simp [intQbinom, show ¬ 0 ≤ b by omega]

theorem intQbinom_upper_neg (q : R) (a b : ℤ) (ha : a < 0) :
    intQbinom q a b = 0 := by
  simp [intQbinom, show ¬ 0 ≤ a by omega]

theorem intQbinom_above (q : R) (a b : ℤ) (hab : a < b) :
    intQbinom q a b = 0 := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by omega
    simp only [intQbinom, ha, hb, and_self, ↓reduceIte]
    exact qbinom_eq_zero_of_lt q (by omega)
  · exact intQbinom_upper_neg q a b (by omega)

/-- Integer q-Pascal, including the lower boundary b = -1. -/
theorem intQbinom_pascal (q : R) (a b : ℤ) (ha : 0 ≤ a) :
    intQbinom q (a + 1) (b + 1) =
      q ^ (a - b).toNat * intQbinom q a b + intQbinom q a (b + 1) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  rcases lt_trichotomy b (-1) with hb | rfl | hb
  · rw [intQbinom_lower_neg q _ (b + 1) (by omega),
      intQbinom_lower_neg q _ b (by omega),
      intQbinom_lower_neg q _ (b + 1) (by omega)]
    ring
  · simp [intQbinom, show (0 : ℤ) ≤ (n : ℤ) + 1 by omega]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b by omega)
    simpa only [← Nat.cast_add, Nat.cast_one, intQbinom_nat, Int.toNat_sub,
      Int.toNat_natCast] using qbinom_succ_succ q n k

/-- The transfer balance relation, including both out-of-range tails. -/
theorem intQbinom_balance (q : R) (a b : ℤ) (ha : 0 ≤ a) :
    (1 - q ^ (a - b).toNat) * intQbinom q a b =
      (1 - q ^ (b + 1).toNat) * intQbinom q a (b + 1) := by
  rcases lt_trichotomy b (-1) with hb | rfl | hb
  · rw [intQbinom_lower_neg q _ b (by omega),
      intQbinom_lower_neg q _ (b + 1) (by omega)]
    ring
  · simp [intQbinom]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b by omega)
    simpa only [← Nat.cast_add, Nat.cast_one, intQbinom_nat, Int.toNat_sub,
      Int.toNat_natCast] using qbinom_balance q n k

theorem qbinom_X_lower (n k : ℕ) :
    (1 - Polynomial.X ^ (n + 1 - k)) * qbinom (Polynomial.X : Polynomial ℤ) (n + 1) k =
      (1 - Polynomial.X ^ (n + 1)) * qbinom Polynomial.X n k := by
  by_cases hk : k ≤ n
  · have h₁ := CarrierChain.qbinom_mul_qpochGen
      (Polynomial.X : Polynomial ℤ) (n + 1) k (by omega)
    have h₂ := CarrierChain.qbinom_mul_qpochGen (Polynomial.X : Polynomial ℤ) n k hk
    rw [show n + 1 - k = (n - k) + 1 by omega, CarrierChain.qpochGen_succ,
      CarrierChain.qpochGen_succ] at h₁
    apply mul_right_cancel₀ (mul_ne_zero (qpoch_X_ne_zero k) (qpoch_X_ne_zero (n - k)))
    rw [show n + 1 - k = n - k + 1 by omega]
    linear_combination h₁ - (1 - Polynomial.X ^ (n + 1)) * h₂
  · rw [show n + 1 - k = 0 by omega, pow_zero, sub_self, zero_mul,
      qbinom_eq_zero_of_lt _ (by omega), mul_zero]

theorem qbinom_lower (q : R) (n k : ℕ) :
    (1 - q ^ (n + 1 - k)) * qbinom q (n + 1) k =
      (1 - q ^ (n + 1)) * qbinom q n k := by
  have h := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) q)
    (qbinom_X_lower n k)
  simpa only [map_mul, map_sub, map_one, map_pow, A2.map_qbinom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

/-- The W(0,1) identity, also at a = 0 where the upper index a-1 is negative. -/
theorem intQbinom_lower (q : R) (a b : ℤ) (ha : 0 ≤ a) :
    intQbinom q (a - 1) b * (1 - q ^ a.toNat) =
      (1 - q ^ (a - b).toNat) * intQbinom q a b := by
  by_cases hb : b < 0
  · rw [intQbinom_lower_neg q _ b hb, intQbinom_lower_neg q _ b hb]
    ring
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b by omega)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  cases n with
  | zero =>
      cases k with
      | zero => simp
      | succ k =>
          rw [intQbinom_nat, qbinom_eq_zero_of_lt _ (by omega)]
          simp
  | succ n =>
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = n by omega]
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, intQbinom_nat,
        ← Nat.cast_add, Int.toNat_sub, Int.toNat_natCast, mul_comm] using
        (qbinom_lower q n k).symm

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.intQbinom_pascal
#print axioms VOA.DeligneAudit.D4Char.intQbinom_balance
#print axioms VOA.DeligneAudit.D4Char.qbinom_X_lower
#print axioms VOA.DeligneAudit.D4Char.qbinom_lower
#print axioms VOA.DeligneAudit.D4Char.intQbinom_lower

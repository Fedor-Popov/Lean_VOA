import VOA.DeligneAudit.D4CharPieriTransfer

/-! The Gaussian balance relation required by the e-Pieri transfer engine. -/

namespace VOA.DeligneAudit.D4Char

open VOA.DeligneGaussian

theorem qbinom_X_balance (n k : ℕ) :
    (1 - Polynomial.X ^ (n - k)) * qbinom (Polynomial.X : Polynomial ℤ) n k =
      (1 - Polynomial.X ^ (k + 1)) * qbinom Polynomial.X n (k + 1) := by
  by_cases hk : k < n
  · have h₁ := CarrierChain.qbinom_mul_qpochGen
      (Polynomial.X : Polynomial ℤ) n k hk.le
    have h₂ := CarrierChain.qbinom_mul_qpochGen
      (Polynomial.X : Polynomial ℤ) n (k + 1) hk
    rw [show n - k = (n - (k + 1)) + 1 by omega,
      CarrierChain.qpochGen_succ] at h₁
    rw [CarrierChain.qpochGen_succ] at h₂
    apply mul_right_cancel₀
      (mul_ne_zero (qpoch_X_ne_zero k) (qpoch_X_ne_zero (n - (k + 1))))
    rw [show n - k = (n - (k + 1)) + 1 by omega]
    linear_combination h₁ - h₂
  · have hkn : n ≤ k := by omega
    rw [Nat.sub_eq_zero_of_le hkn, pow_zero, sub_self, zero_mul,
      qbinom_eq_zero_of_lt _ (by omega), mul_zero]

/-- The local relation of Lemma E, for every n and k over any commutative ring. -/
theorem qbinom_balance {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    (1 - q ^ (n - k)) * qbinom q n k =
      (1 - q ^ (k + 1)) * qbinom q n (k + 1) := by
  have h := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) q)
    (qbinom_X_balance n k)
  simpa only [map_mul, map_sub, map_one, map_pow, A2.map_qbinom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

/-- An actual Gaussian edge of the transfer chain. -/
def gaussianPieriEdge {R : Type*} [CommRing R] (q : R) (n k : ℕ) : PieriEdge R where
  c := q ^ (n - k)
  beta := q ^ (k + 1)
  X := qbinom q n k
  Y := qbinom q n (k + 1)
  balance := qbinom_balance q n k

/-- The transfer identity specialized to arbitrary finite chains of Gaussian entries. -/
theorem gaussian_pieri_transfer_chain {R : Type*} [CommRing R] (q z : R)
    (n k : ℕ) (indices : List (ℕ × ℕ)) :
    let e := gaussianPieriEdge q n k
    let es := indices.map fun p => gaussianPieriEdge q p.1 p.2
    (pieriLeftRun z (e :: es) (1, z)).1 +
      (pieriLeftRun z (e :: es) (1, z)).2 =
    (1 + z) * ((pieriRightRun z e.c es (e.X, z * e.Y)).1 +
      (pieriRightRun z e.c es (e.X, z * e.Y)).2) :=
  pieri_transfer_chain z _ _

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.qbinom_X_balance
#print axioms VOA.DeligneAudit.D4Char.qbinom_balance
#print axioms VOA.DeligneAudit.D4Char.gaussian_pieri_transfer_chain

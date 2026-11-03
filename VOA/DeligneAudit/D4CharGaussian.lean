import VOA.DeligneAudit.D4CharGTShift
import VOA.DeligneAudit.A2CarrierResummation

/-! Gaussian symmetry from the proved finite Pochhammer identity, with no division in R. -/

namespace VOA.DeligneAudit.D4Char

open VOA.DeligneGaussian
open scoped BigOperators

theorem qpoch_X_ne_zero (n : ℕ) :
    CarrierChain.qpochGen (Polynomial.X : Polynomial ℤ) n ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.evalRingHom (0 : ℤ)) h
  simp [CarrierChain.qpochGen, map_prod] at hh

theorem qbinom_X_symm (n k : ℕ) (hk : k ≤ n) :
    qbinom (Polynomial.X : Polynomial ℤ) n (n - k) = qbinom Polynomial.X n k := by
  apply mul_right_cancel₀
    (mul_ne_zero (qpoch_X_ne_zero k) (qpoch_X_ne_zero (n - k)))
  have h₁ := CarrierChain.qbinom_mul_qpochGen
    (Polynomial.X : Polynomial ℤ) n (n - k) (Nat.sub_le _ _)
  have h₂ := CarrierChain.qbinom_mul_qpochGen (Polynomial.X : Polynomial ℤ) n k hk
  rw [Nat.sub_sub_self hk] at h₁
  calc
    _ = CarrierChain.qpochGen Polynomial.X n := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h₁
    _ = _ := by simpa only [mul_assoc] using h₂.symm

/-- Gaussian symmetry in any commutative ring, even when Pochhammer factors vanish. -/
theorem qbinom_symm {R : Type*} [CommRing R] (q : R) (n k : ℕ) (hk : k ≤ n) :
    qbinom q n (n - k) = qbinom q n k := by
  have h := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) q)
    (qbinom_X_symm n k hk)
  simpa only [A2.map_qbinom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

theorem qbinom_diagonal {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qbinom q n n = 1 := by
  simpa only [Nat.sub_zero, qbinom_zero_right] using qbinom_symm q n 0 (Nat.zero_le n)

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.qpoch_X_ne_zero
#print axioms VOA.DeligneAudit.D4Char.qbinom_X_symm
#print axioms VOA.DeligneAudit.D4Char.qbinom_symm
#print axioms VOA.DeligneAudit.D4Char.qbinom_diagonal

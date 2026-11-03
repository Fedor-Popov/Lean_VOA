import VOA.DeligneAudit.D4CharGaussian
import VOA.DeligneAudit.DeligneCharacterD4Functional

/-!
The finite q-binomial theorem at the signed quadratic theta sequence. Its q-Pascal
proof incorporates the exponent shift, so no negative power of a natural number occurs.
This is the finite cancellation used for the zero moments in Lemma O of STEP2.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian DeligneCharacter

noncomputable section

/-- The signed quadratic coefficient of the Jacobi theta series. -/
def rsThetaSeed (a : ℤ) : D4K.Kq := D4K.sgn a * D4K.qC a

/-- The backwards shift of the signed quadratic sequence, including negative indices. -/
theorem rsThetaSeed_pred (a : ℤ) :
    rsThetaSeed (a - 1) = -(D4K.qq ^ (1 - a)) * rsThetaSeed a := by
  have hs := D4K.sgn_add_one (a - 1)
  have hq := D4K.qC_succ (a - 1)
  rw [sub_add_cancel] at hs hq
  unfold rsThetaSeed
  rw [hs, hq]
  have hp : D4K.qq ^ (1 - a) * D4K.qq ^ (a - 1) = 1 := by
    rw [← zpow_add₀ D4K.qq_ne_zero]
    simp
  linear_combination D4K.sgn (a - 1) * D4K.qC (a - 1) * (1 - hp)

/-- Theta's even coefficients are the difference of adjacent signed seeds. -/
theorem rsThetaSeed_difference (a : ℤ) :
    D4K.thK (2 * a) = rsThetaSeed a - rsThetaSeed (a + 1) := by
  rw [D4K.thK_even, rsThetaSeed, rsThetaSeed, D4K.sgn_add_one]
  ring

/-- The theta measure is invariant under inversion of the Laurent variable. -/
theorem rsTheta_even_neg (a : ℤ) : D4K.thK (2 * -a) = D4K.thK (2 * a) := by
  rw [D4K.thK_even, D4K.thK_even, D4K.sgn_neg, D4K.qC_neg]
  have h : D4K.qC (-a + 1) = D4K.qC a := by
    have h := D4K.qC_neg (a - 1)
    rw [show -(a - 1) = -a + 1 by ring, sub_add_cancel] at h
    exact h
  rw [h, add_comm]

/-- The full Gaussian convolution against a signed theta seed. -/
def rsThetaSum (n : ℕ) (a : ℤ) : D4K.Kq :=
  ∑ j ∈ Finset.range (n + 1), qbinom D4K.qq n j * rsThetaSeed (a - j)

/-- q-Pascal produces the next finite Euler factor. -/
theorem rsThetaSum_succ (n : ℕ) (a : ℤ) :
    rsThetaSum (n + 1) a =
      (1 - D4K.qq ^ ((n : ℤ) + 1 - a)) * rsThetaSum n a := by
  unfold rsThetaSum
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [qbinom_succ_succ, add_mul, Finset.sum_add_distrib,
    qbinom_zero_right, Nat.cast_zero, sub_zero, one_mul]
  have hshift :
      (∑ j ∈ Finset.range (n + 1),
        qbinom D4K.qq n (j + 1) * rsThetaSeed (a - (j + 1))) + rsThetaSeed a =
      ∑ j ∈ Finset.range (n + 1), qbinom D4K.qq n j * rsThetaSeed (a - j) := by
    have h := Finset.sum_range_succ'
      (fun j => qbinom D4K.qq n j * rsThetaSeed (a - j)) (n + 1)
    rw [Finset.sum_range_succ] at h
    simpa [qbinom_eq_zero_of_lt D4K.qq (Nat.lt_succ_self n)] using h.symm
  have hterm :
      (∑ j ∈ Finset.range (n + 1),
        D4K.qq ^ (n - j) * qbinom D4K.qq n j * rsThetaSeed (a - (j + 1))) =
      -(D4K.qq ^ ((n : ℤ) + 1 - a)) *
        ∑ j ∈ Finset.range (n + 1), qbinom D4K.qq n j * rsThetaSeed (a - j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    rw [show a - ((j : ℤ) + 1) = (a - j) - 1 by omega, rsThetaSeed_pred]
    have hp : D4K.qq ^ (n - j) * D4K.qq ^ (1 - (a - j)) =
        D4K.qq ^ ((n : ℤ) + 1 - a) := by
      rw [← zpow_natCast, ← zpow_add₀ D4K.qq_ne_zero, Int.natCast_sub hjn]
      congr 1
      ring
    linear_combination -qbinom D4K.qq n j * rsThetaSeed (a - j) * hp
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hterm, add_assoc, hshift]
  ring

/-- The specialized finite q-binomial product, for every integer shift. -/
theorem rsThetaSum_product (n : ℕ) (a : ℤ) :
    rsThetaSum n a = rsThetaSeed a *
      ∏ i ∈ Finset.range n, (1 - D4K.qq ^ ((i : ℤ) + 1 - a)) := by
  induction n with
  | zero => simp [rsThetaSum]
  | succ n ih => rw [rsThetaSum_succ, ih, Finset.prod_range_succ]; ring

/-- Every interior integer shift is a zero of the full finite Gaussian sum. -/
theorem rsThetaSum_zero (n a : ℕ) (ha : 0 < a) (han : a ≤ n) :
    rsThetaSum n a = 0 := by
  rw [rsThetaSum_product]
  have hz : (∏ i ∈ Finset.range n, (1 - D4K.qq ^ ((i : ℤ) + 1 - a))) = 0 := by
    apply Finset.prod_eq_zero (i := a - 1) (by simp; omega)
    rw [show ((a - 1 : ℕ) : ℤ) + 1 - a = 0 by omega, zpow_zero, sub_self]
  rw [hz, mul_zero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsThetaSeed_pred
#print axioms VOA.DeligneAudit.D4Char.rsThetaSeed_difference
#print axioms VOA.DeligneAudit.D4Char.rsTheta_even_neg
#print axioms VOA.DeligneAudit.D4Char.rsThetaSum_succ
#print axioms VOA.DeligneAudit.D4Char.rsThetaSum_product
#print axioms VOA.DeligneAudit.D4Char.rsThetaSum_zero

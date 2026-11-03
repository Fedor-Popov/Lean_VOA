import VOA.DeligneAudit.D4CharQBoundary

/-! Lemma 5.1: coefficient recursion and uniqueness for a formal q-difference equation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The exact unit hypothesis of the q-difference uniqueness lemma. -/
def QDifferenceUnits (q : R) : Prop := ∀ n : ℕ, 0 < n → IsUnit (1 - q ^ n)

/-- The formal parameter satisfies the unit hypothesis, over any commutative base ring. -/
theorem powerSeries_qDifferenceUnits (A : Type*) [CommRing A] :
    QDifferenceUnits (X : PowerSeries A) := by
  intro n hn
  apply isUnit_iff_constantCoeff.mpr
  simp [map_sub, map_pow, ne_of_gt hn]

/-- Units persist under the coefficient-ring extensions used by the Cauchy identities. -/
theorem qDifferenceUnits_map {S : Type*} [CommRing S] (φ : R →+* S) {q : R}
    (hq : QDifferenceUnits q) : QDifferenceUnits (φ q) := by
  intro n hn
  simpa only [map_sub, map_one, map_pow] using (hq n hn).map φ

/-- The coefficient recursion, with the unit factor written as 1 - q^n. -/
theorem qDifference_coeff_rec (q : R) (A B G : PowerSeries R)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hG : rescale q G * A = G * B) (n : ℕ) :
    (1 - q ^ n) * coeff n G = ∑ k ∈ Finset.range n,
      coeff k G * (q ^ k * coeff (n - k) A - coeff (n - k) B) := by
  have he := congrArg (coeff n) hG
  simp only [coeff_mul, coeff_rescale,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at he
  simp only [Nat.sub_self, coeff_zero_eq_constantCoeff_apply, hA, hB, mul_one] at he
  have hs : (∑ k ∈ Finset.range n,
      coeff k G * (q ^ k * coeff (n - k) A - coeff (n - k) B)) =
      (∑ k ∈ Finset.range n, q ^ k * coeff k G * coeff (n - k) A) -
      ∑ k ∈ Finset.range n, coeff k G * coeff (n - k) B := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  linear_combination -he

/-- Lemma 5.1, with every positive degree handled by strong induction. -/
theorem qDifference_unique (q : R) (hq : QDifferenceUnits q)
    (A B G H : PowerSeries R) (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hG : rescale q G * A = G * B) (hH : rescale q H * A = H * B)
    (hzero : constantCoeff G = constantCoeff H) : G = H := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [coeff_zero_eq_constantCoeff_apply] using hzero
      · apply (hq n (Nat.pos_of_ne_zero hn)).mul_left_cancel
        rw [qDifference_coeff_rec q A B G hA hB hG,
          qDifference_coeff_rec q A B H hA hB hH]
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]

/-- In particular, zero initial value forces the zero solution. -/
theorem qDifference_zero (q : R) (hq : QDifferenceUnits q)
    (A B G : PowerSeries R) (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hG : rescale q G * A = G * B) (hzero : constantCoeff G = 0) : G = 0 := by
  apply qDifference_unique q hq A B G 0 hA hB hG
  · simp
  · simpa using hzero

/-- The integral q-series version, also valid after any coefficient-ring homomorphism. -/
theorem qDifference_unique_of_series_map (φ : PowerSeries ℤ →+* R)
    (A B G H : PowerSeries R) (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hG : rescale (φ X) G * A = G * B) (hH : rescale (φ X) H * A = H * B)
    (hzero : constantCoeff G = constantCoeff H) : G = H :=
  qDifference_unique (φ X) (qDifferenceUnits_map φ (powerSeries_qDifferenceUnits ℤ))
    A B G H hA hB hG hH hzero

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.powerSeries_qDifferenceUnits
#print axioms VOA.DeligneAudit.D4Char.qDifferenceUnits_map
#print axioms VOA.DeligneAudit.D4Char.qDifference_coeff_rec
#print axioms VOA.DeligneAudit.D4Char.qDifference_unique
#print axioms VOA.DeligneAudit.D4Char.qDifference_zero
#print axioms VOA.DeligneAudit.D4Char.qDifference_unique_of_series_map

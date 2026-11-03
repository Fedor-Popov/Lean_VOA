/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.QWeylCharacter
import Mathlib.Algebra.BigOperators.Intervals

/-! # Finite odd-even pairing of the boundary Weyl character correction -/
namespace VOA.QSeries
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

/-- Pair consecutive odd and even terms while retaining the initial term. -/
theorem sum_alternating_pairs (f : ℕ → K) (N : ℕ) :
    ∑ r ∈ Finset.range (2*N+1), (-1 : K)^r * f r =
      f 0 + ∑ s ∈ Finset.Icc 1 N, (f (2*s) - f (2*s-1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)+1=(2*N+1)+1+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1),ih]
    have ho : (-1 : K)^(2*N+1) = -1 := by rw [pow_add,pow_mul]; simp
    have he : (-1 : K)^(2*N+1+1) = 1 := by rw [show 2*N+1+1=2*(N+1) by omega,pow_mul]; simp
    rw [ho,he]
    rw [show 2*(N+1)-1=2*N+1 by omega,show 2*(N+1)=2*N+1+1 by omega]
    ring

/-- The finite Weyl cutoff may be enlarged because later shifts exceed the degree. -/
theorem weylTermCoefficient_eq_zero_of_lt (p n r : ℕ) (hp : p ≠ 0) (hn : n < r) :
    (weylTermCoefficient p n r : K) = 0 := by
  have ht := le_triangular r
  have hm : (r+1).choose 2 ≤ p*(r+1).choose 2 := by
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp)
  simp [weylTermCoefficient,show ¬p*(r+1).choose 2 ≤ n by omega]

/-- Exact odd triangular exponent. -/
theorem triangular_odd (s : ℕ) (hs : 0<s) :
    (2*s-1+1).choose 2 = s*(2*s-1) := by
  have he := two_mul_choose_two_add (2*s)
  have hh : 2*s-1+1=2*s := by omega
  rw [hh]
  have hb : 2*s-1+1=2*s := by omega
  nlinarith

/-- Exact even triangular exponent. -/
theorem triangular_even (s : ℕ) : (2*s+1).choose 2 = s*(2*s+1) := by
  have he := two_mul_choose_two_add (2*s+1)
  nlinarith

/-- The root-order correction after pairing the two affine root families. -/
def weylPairTail (p n : ℕ) : K :=
  ∑ s ∈ Finset.Icc 1 n,
    ((if p*s*(2*s-1) ≤ n then
      (4*s-1 : ℕ) * PowerSeries.coeff (n-p*s*(2*s-1)) (reciprocalEuler^3 : PowerSeries K)
      else 0) -
    (if p*s*(2*s+1) ≤ n then
      (4*s+1 : ℕ) * PowerSeries.coeff (n-p*s*(2*s+1)) (reciprocalEuler^3 : PowerSeries K)
      else 0))

theorem weylTermCoefficient_odd (p n s : ℕ) (hs : 0<s) :
    (weylTermCoefficient p n (2*s-1) : K) =
      if p*s*(2*s-1) ≤ n then
        (4*s-1 : ℕ) * PowerSeries.coeff (n-p*s*(2*s-1)) (reciprocalEuler^3 : PowerSeries K)
      else 0 := by
  rw [weylTermCoefficient,triangular_odd s hs]
  rw [show 2*(2*s-1)+1=4*s-1 by omega]
  simp only [mul_assoc]

theorem weylTermCoefficient_even (p n s : ℕ) :
    (weylTermCoefficient p n (2*s) : K) =
      if p*s*(2*s+1) ≤ n then
        (4*s+1 : ℕ) * PowerSeries.coeff (n-p*s*(2*s+1)) (reciprocalEuler^3 : PowerSeries K)
      else 0 := by
  rw [weylTermCoefficient,triangular_even]
  rw [show 2*(2*s)+1=4*s+1 by omega]
  simp only [mul_assoc]

/-- The paired finite root-order tail plus the product coefficient equals
the universal three-colour PBW coefficient. -/
theorem weylPairTail_add_product (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    (weylPairTail p n : K) + PowerSeries.coeff n
        ((PowerSeries.expand p hp (euler : PowerSeries K))^3 * reciprocalEuler^3) =
      PowerSeries.coeff n (reciprocalEuler^3 : PowerSeries K) := by
  rw [coeff_weyl_product_eq_sum]
  have he : (∑ r ∈ Finset.range (n+1), (-1 : K)^r * weylTermCoefficient p n r) =
      ∑ r ∈ Finset.range (2*n+1), (-1 : K)^r * weylTermCoefficient p n r := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r hr hnot
    rw [weylTermCoefficient_eq_zero_of_lt p n r hp (by simp only [Finset.mem_range] at hnot; omega),mul_zero]
  rw [he,sum_alternating_pairs]
  have hz : (weylTermCoefficient p n 0 : K) = PowerSeries.coeff n (reciprocalEuler^3 : PowerSeries K) := by
    simp [weylTermCoefficient]
  rw [hz]
  have ht : (weylPairTail p n : K) =
      ∑ s ∈ Finset.Icc 1 n, (weylTermCoefficient p n (2*s-1) - weylTermCoefficient p n (2*s)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [weylTermCoefficient_odd p n s (Finset.mem_Icc.mp hs).1,weylTermCoefficient_even]
  rw [ht,← add_assoc,add_comm _ (PowerSeries.coeff n (reciprocalEuler^3 : PowerSeries K)),
    add_assoc,← Finset.sum_add_distrib]
  have hs : (∑ s ∈ Finset.Icc 1 n,
      ((weylTermCoefficient p n (2*s-1) : K)-weylTermCoefficient p n (2*s) +
        (weylTermCoefficient p n (2*s)-weylTermCoefficient p n (2*s-1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    ring
  rw [hs,add_zero]

end
end VOA.QSeries

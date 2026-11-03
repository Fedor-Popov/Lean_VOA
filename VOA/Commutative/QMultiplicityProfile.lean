/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.QHilbertProduct
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Multiplicity profiles and the actual Hilbert-bound source sum

The source energy is the literal minimum-kernel quadratic form of equation 5.8.
Grouping profiles by their total multiplicity and peeling their first coordinate
produces the descending cumulative-count chains of equation 5.12.
-/

namespace VOA.QSeries

open scoped BigOperators
open VOA.LocallyFinitePowerSeriesSum

/-- The minimum-kernel quadratic energy on colors indexed from one. -/
def profileQuadratic {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  ∑ i, ∑ j, min (i.val + 1) (j.val + 1) * r i * r j

/-- The linear particle weight of a multiplicity profile. -/
def profileLinear {m : ℕ} (r : Fin m → ℕ) : ℕ :=
  ∑ i, (i.val + 1) * r i

/-- The chain-independent part of the exponent in equation 5.8. -/
def profileEnergy {m : ℕ} (r : Fin m → ℕ) : ℕ := profileQuadratic r + profileLinear r

/-- Peeling the first multiplicity shifts every remaining color by one. -/
theorem profileQuadratic_cons {m : ℕ} (a : ℕ) (r : Fin m → ℕ) :
    profileQuadratic (Fin.cons a r) = (a + ∑ i, r i) ^ 2 + profileQuadratic r := by
  simp only [profileQuadratic, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.min_self, one_mul]
  simp only [show ∀ i : Fin m, min 1 (i.val + 1 + 1) = 1 by intro i; omega,
    show ∀ i : Fin m, min (i.val + 1 + 1) 1 = 1 by intro i; omega,
    Nat.add_min_add_right, one_mul]
  simp only [add_mul, mul_add, Finset.sum_add_distrib, pow_two, Finset.sum_mul, Finset.mul_sum]
  have hswap : (∑ i, ∑ j, r j * r i) = ∑ i, ∑ j, r i * r j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.mul_comm _ _
  rw [hswap]
  ring_nf

/-- The linear profile weight has the same tail-count recurrence. -/
theorem profileLinear_cons {m : ℕ} (a : ℕ) (r : Fin m → ℕ) :
    profileLinear (Fin.cons a r) = a + (∑ i, r i) + profileLinear r := by
  simp only [profileLinear, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, one_mul, add_mul, Finset.sum_add_distrib]
  ring_nf

/-- The exact cumulative-count energy recurrence. -/
theorem profileEnergy_cons {m : ℕ} (a : ℕ) (r : Fin m → ℕ) :
    profileEnergy (Fin.cons a r) =
      (a + ∑ i, r i) * (a + ∑ i, r i + 1) + profileEnergy r := by
  rw [profileEnergy, profileQuadratic_cons, profileLinear_cons, profileEnergy]
  ring_nf

/-- Total multiplicity is bounded by the source exponent. -/
theorem sum_le_profileEnergy {m : ℕ} (r : Fin m → ℕ) :
    (∑ i, r i) ≤ profileEnergy r := by
  have hlinear : (∑ i, r i) ≤ profileLinear r := by
    apply Finset.sum_le_sum
    intro i hi
    have : 1 ≤ i.val + 1 := by omega
    nlinarith
  exact hlinear.trans (Nat.le_add_left _ _)

noncomputable section

variable {K : Type*} [Field K]

/-- All profile denominators except the final color, whose denominator is in `residualSum`. -/
def profileInitialDenominator {m : ℕ} (r : Fin (m + 1) → ℕ) : PowerSeries K :=
  ∏ i : Fin m, reciprocalQFactorial (r i.castSucc)

/-- The literal minimum-energy profile summand after only the three residual sums are grouped. -/
def multiplicityTerm {m : ℕ} (r : Fin (m + 1) → ℕ) : PowerSeries K :=
  PowerSeries.X ^ profileEnergy r * profileInitialDenominator r * residualSum (r (Fin.last m))

/-- Peeling the first profile denominator. -/
theorem profileInitialDenominator_cons {m : ℕ} (a : ℕ) (r : Fin (m + 1) → ℕ) :
    profileInitialDenominator (K := K) (Fin.cons a r) =
      reciprocalQFactorial a * profileInitialDenominator r := by
  simp [profileInitialDenominator, Fin.prod_univ_succ]

/-- The literal profile summand becomes one outer chain weight times its tail summand. -/
theorem multiplicityTerm_cons {m : ℕ} (a : ℕ) (r : Fin (m + 1) → ℕ) :
    multiplicityTerm (K := K) (Fin.cons a r) =
      PowerSeries.X ^ ((a + ∑ i, r i) * (a + ∑ i, r i + 1)) *
        reciprocalQFactorial a * multiplicityTerm r := by
  rw [multiplicityTerm, profileEnergy_cons, pow_add, profileInitialDenominator_cons]
  simp only [Fin.cons_last, multiplicityTerm]
  ring_nf

/-- Reindex the profiles of a fixed total by the total of their tail and the tail profile.
The removed coordinate is the difference of two successive cumulative counts. -/
theorem sum_antidiagonalTuple_peel {A : Type*} [AddCommMonoid A] (m n : ℕ)
    (F : (Fin (m + 1) → ℕ) → A) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple (m + 1) n, F r) =
      ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.Nat.antidiagonalTuple m j,
        F (Fin.cons (n - j) r) := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun r => ⟨∑ i, Fin.tail r i, Fin.tail r⟩)
    (fun p => Fin.cons (n - p.1) p.2)
  · intro r hr
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp hr
    rw [Fin.sum_univ_succ] at hsum
    change r 0 + (∑ i, Fin.tail r i) = n at hsum
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
    exact ⟨by omega, trivial⟩
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hp ⊢
    rw [Fin.sum_cons, hp.2]
    omega
  · intro r hr
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp hr
    rw [Fin.sum_univ_succ] at hsum
    change r 0 + (∑ i, Fin.tail r i) = n at hsum
    have hhead : n - ∑ i, Fin.tail r i = r 0 := by omega
    rw [hhead]
    exact Fin.cons_self_tail r
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hp
    simp only [Fin.tail_cons, hp.2]
  · intro r hr
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp hr
    rw [Fin.sum_univ_succ] at hsum
    change r 0 + (∑ i, Fin.tail r i) = n at hsum
    have hhead : n - ∑ i, Fin.tail r i = r 0 := by omega
    rw [hhead, Fin.cons_self_tail]

/-- A fixed total-multiplicity slice equals the actual bounded descending-chain kernel. -/
theorem sum_multiplicityTerm_fixed_total (m n : ℕ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple (m + 1) n, multiplicityTerm (K := K) r) =
      PowerSeries.X ^ (n * (n + 1)) * hilbertBoundKernel m n := by
  induction m generalizing n with
  | zero => simp [multiplicityTerm, profileEnergy, profileQuadratic, profileLinear,
      profileInitialDenominator, hilbertBoundKernel, Nat.mul_add]
  | succ m ih =>
      rw [sum_antidiagonalTuple_peel, hilbertBoundKernel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      calc
        _ = (PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) * reciprocalQFactorial (n - j) *
            (∑ r ∈ Finset.Nat.antidiagonalTuple (m + 1) j, multiplicityTerm r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [multiplicityTerm_cons, Finset.Nat.mem_antidiagonalTuple.mp hr,
            Nat.sub_add_cancel hjn]
        _ = _ := by rw [ih]; ring_nf

/-- Profiles of bounded total multiplicity, as an explicit finite union of antidiagonals. -/
def profileCutoff (m D : ℕ) : Finset (Fin (m + 1) → ℕ) :=
  (Finset.range (D + 1)).biUnion (Finset.Nat.antidiagonalTuple (m + 1))

/-- The cutoff contains exactly the profiles whose total multiplicity is at most `D`. -/
theorem mem_profileCutoff (m D : ℕ) (r : Fin (m + 1) → ℕ) :
    r ∈ profileCutoff m D ↔ (∑ i, r i) ≤ D := by
  classical
  constructor
  · intro h
    obtain ⟨n, hn, hr⟩ := Finset.mem_biUnion.mp h
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp hr
    have hnD := Finset.mem_range.mp hn
    omega
  · intro h
    apply Finset.mem_biUnion.mpr
    exact ⟨∑ i, r i, Finset.mem_range.mpr (by omega),
      Finset.Nat.mem_antidiagonalTuple.mpr rfl⟩

/-- Distinct total multiplicities label disjoint profile slices. -/
theorem antidiagonalTuple_pairwiseDisjoint (m D : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (D + 1))) (Finset.Nat.antidiagonalTuple (m + 1)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro r hri hrj
  exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hri).symm.trans
    (Finset.Nat.mem_antidiagonalTuple.mp hrj))

/-- The literal source monomial enforces a finite profile cutoff in every coefficient. -/
theorem coeff_multiplicityTerm_eq_zero (m D : ℕ) (r : Fin (m + 1) → ℕ)
    (h : D < ∑ i, r i) : PowerSeries.coeff D (multiplicityTerm (K := K) r) = 0 := by
  rw [multiplicityTerm, mul_assoc, PowerSeries.coeff_X_pow_mul']
  have hbound := sum_le_profileEnergy r
  simp [show ¬ profileEnergy r ≤ D by omega]

/-- The profile-indexed source family is coefficientwise locally finite. -/
theorem multiplicityTerm_finite (m : ℕ) :
    IsCoefficientwiseFinite (fun r : Fin (m + 1) → ℕ => multiplicityTerm (K := K) r) := by
  apply isCoefficientwiseFinite_of_mem_finset _ (profileCutoff m)
  intro D r hr
  rw [mem_profileCutoff]
  by_contra h
  exact hr (coeff_multiplicityTerm_eq_zero m D r (by omega))

/-- The source series of equation 5.8 with `m+1` multiplicity colors and all three residual
species. Its summand uses the literal minimum-kernel energy, not a chain or product definition. -/
def multiplicitySource (m : ℕ) : PowerSeries K :=
  VOA.LocallyFinitePowerSeriesSum.sum (fun r : Fin (m + 1) → ℕ => multiplicityTerm r)

/-- The profile-to-chain reindexing of the actual source series, including its quadratic energy. -/
theorem multiplicitySource_eq_hilbertBoundSeries (m : ℕ) :
    multiplicitySource (K := K) m = hilbertBoundSeries (m + 1) := by
  classical
  apply PowerSeries.ext
  intro D
  calc
    _ = ∑ r ∈ profileCutoff m D, PowerSeries.coeff D (multiplicityTerm (K := K) r) := by
      rw [multiplicitySource, coeff_sum]
      apply finsum_eq_sum_of_support_subset
      intro r hr
      change r ∈ profileCutoff m D
      rw [mem_profileCutoff]
      by_contra h
      exact hr (coeff_multiplicityTerm_eq_zero m D r (by omega))
    _ = ∑ n ∈ Finset.range (D + 1),
        PowerSeries.coeff D (∑ r ∈ Finset.Nat.antidiagonalTuple (m + 1) n,
          multiplicityTerm (K := K) r) := by
      rw [profileCutoff, Finset.sum_biUnion (antidiagonalTuple_pairwiseDisjoint m D)]
      simp only [map_sum]
    _ = ∑ n ∈ Finset.range (D + 1), PowerSeries.coeff D
        ((PowerSeries.X : PowerSeries K) ^ (n * (n + 1)) * hilbertBoundKernel m n) := by
      simp only [sum_multiplicityTerm_fixed_total]
    _ = _ := by
      rw [hilbertBoundSeries]
      symm
      rw [coeff_indexBounded_sum _ (fun d n h => ?_) D D le_rfl, map_sum]
      · simp only [Nat.add_sub_cancel]
      · rw [PowerSeries.coeff_X_pow_mul']
        have hn : n ≤ n * (n + 1) := by nlinarith
        simp [show ¬ n * (n + 1) ≤ d by omega]

/-- The product evaluation of the explicit minimum-energy multiplicity source, equation 5.33. -/
theorem multiplicitySource_product (m : ℕ) :
    multiplicitySource (K := K) m =
      (PowerSeries.expand (2 * (m + 1) + 1) (by omega) (euler : PowerSeries K)) ^ 3 *
        reciprocalEuler ^ 3 := by
  rw [multiplicitySource_eq_hilbertBoundSeries, hilbertBoundSeries_product (m + 1) (by omega)]

/-- A single finite cube computes every residual coefficient through the chosen cutoff. -/
theorem truncEq_residualSum_cube (n D : ℕ) :
    TruncEq D (residualSum n : PowerSeries K)
      (∑ s ∈ Finset.range (D + 1), ∑ t ∈ Finset.range (D + 1),
        ∑ c ∈ Finset.range (D + 1),
        PowerSeries.X ^ ((n + 1) * (s + t + c) + s * t) *
          reciprocalQFactorial n * reciprocalQFactorial s *
            reciprocalQFactorial t * reciprocalQFactorial c) := by
  intro i hi
  rw [residualSum, coeff_powerShiftSum (n + 1) (by omega) _ i D hi, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  let T : PowerSeries K := ∑ t ∈ Finset.range (D + 1),
    PowerSeries.X ^ ((n + s + 1) * t) * reciprocalQFactorial t
  let C : PowerSeries K := ∑ c ∈ Finset.range (D + 1),
    PowerSeries.X ^ ((n + 1) * c) * reciprocalQFactorial c
  have ht : TruncEq D (eulerSum (n + s + 1) : PowerSeries K) T :=
    truncEq_powerShiftSum _ (by omega) _ D
  have hc : TruncEq D (eulerSum (n + 1) : PowerSeries K) C :=
    truncEq_powerShiftSum _ (by omega) _ D
  have he := (TruncEq.refl D (PowerSeries.X ^ ((n + 1) * s))).mul
    ((((TruncEq.refl D (reciprocalQFactorial s)).mul ht).mul hc).mul
      (TruncEq.refl D (reciprocalQFactorial n)))
  rw [he i hi]
  congr 1
  dsimp [T, C]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro c hc
  have hexp : (n + 1) * (s + t + c) + s * t =
      (n + 1) * s + (n + s + 1) * t + (n + 1) * c := by ring_nf
  rw [hexp, pow_add, pow_add]
  ring_nf

/-- The literal triple-residual summand of equation 5.8 for a fixed profile. -/
def multiplicityResidualTerm {m : ℕ} (r : Fin (m + 1) → ℕ) (s t c : ℕ) : PowerSeries K :=
  PowerSeries.X ^ (profileEnergy r + (r (Fin.last m) + 1) * (s + t + c) + s * t) *
    (∏ i, reciprocalQFactorial (r i)) * reciprocalQFactorial s *
      reciprocalQFactorial t * reciprocalQFactorial c

/-- The grouped profile summand is exactly the original three-variable residual sum,
with a common finite cube cutoff for every requested coefficient. -/
theorem coeff_multiplicityTerm (m D : ℕ) (r : Fin (m + 1) → ℕ) :
    PowerSeries.coeff D (multiplicityTerm (K := K) r) =
      PowerSeries.coeff D (∑ s ∈ Finset.range (D + 1), ∑ t ∈ Finset.range (D + 1),
        ∑ c ∈ Finset.range (D + 1), multiplicityResidualTerm (K := K) r s t c) := by
  have hres := truncEq_residualSum_cube (K := K) (r (Fin.last m)) D
  have he := ((TruncEq.refl D (PowerSeries.X ^ profileEnergy r)).mul
    (TruncEq.refl D (profileInitialDenominator (K := K) r))).mul hres
  unfold multiplicityTerm
  rw [he D le_rfl]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro c hc
  unfold multiplicityResidualTerm profileInitialDenominator
  rw [Fin.prod_univ_castSucc (fun i => reciprocalQFactorial (R := K) (r i))]
  rw [show profileEnergy r + (r (Fin.last m) + 1) * (s + t + c) + s * t =
    profileEnergy r + ((r (Fin.last m) + 1) * (s + t + c) + s * t) by omega, pow_add]
  ring_nf

/-- The actual equation 5.8 source, written coefficientwise as an explicit finite profile
sum and finite cube over `s,t,c`. All exponents and every profile denominator are visible. -/
theorem coeff_multiplicitySource (m D : ℕ) :
    PowerSeries.coeff D (multiplicitySource (K := K) m) =
      PowerSeries.coeff D (∑ r ∈ profileCutoff m D,
        ∑ s ∈ Finset.range (D + 1), ∑ t ∈ Finset.range (D + 1),
          ∑ c ∈ Finset.range (D + 1), multiplicityResidualTerm (K := K) r s t c) := by
  classical
  rw [multiplicitySource, coeff_sum, map_sum]
  calc
    _ = ∑ r ∈ profileCutoff m D, PowerSeries.coeff D (multiplicityTerm (K := K) r) := by
      apply finsum_eq_sum_of_support_subset
      intro r hr
      change r ∈ profileCutoff m D
      rw [mem_profileCutoff]
      by_contra h
      exact hr (coeff_multiplicityTerm_eq_zero m D r (by omega))
    _ = _ := by simp only [coeff_multiplicityTerm]

end
end VOA.QSeries

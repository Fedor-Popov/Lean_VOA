/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningLaurent
import VOA.Examples.VirasoroScreeningNewton

/-!
# The nonzero middle coefficient of every even Vandermonde power

The finite Laurent sum-of-squares argument applies at every rank and every
integer exponent. Counting the pairs containing a given variable identifies
its central exponent as (r-1)t. This proves the ordinary scalar fact needed
in the integer-screening construction, without an explicit product formula.
-/
namespace VOA.VirasoroScreening
open AddMonoidAlgebra
open scoped BigOperators

/-- The exponent vector of a single auxiliary variable. -/
noncomputable def unitExponent (r : ℕ) (i : Fin r) : Fin r → ℤ := Pi.single i 1

/-- Each unordered pair of auxiliary variables is represented once, in
increasing order. This prevents double counting in the Vandermonde product. -/
def variablePairs (r : ℕ) : Finset (Fin r × Fin r) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-- Vandermonde as a finite Laurent polynomial; its exponents are actually
nonnegative, but the Laurent carrier permits reversal without division. -/
noncomputable def vandermondeLaurent (r : ℕ) : Laurent (Fin r → ℤ) :=
  ∏ ij ∈ variablePairs r,
    (single (unitExponent r ij.1) 1 - single (unitExponent r ij.2) 1)

/-- Distinct auxiliary variables have distinct unit exponent vectors. -/
theorem unitExponent_injective (r : ℕ) : Function.Injective (unitExponent r) := by
  intro i j hij
  by_contra hne
  have he := congrFun hij i
  simp [unitExponent,Pi.single_apply,hne,Ne.symm hne] at he

/-- Every variable occurs in exactly r-1 unordered pairs. Thus the common
reversal shift has the same exponent r-1 in every coordinate. -/
theorem variablePairs_exponent_sum (r : ℕ) :
    (∑ ij ∈ variablePairs r, (unitExponent r ij.1 + unitExponent r ij.2)) =
      fun _ : Fin r => ((r-1:ℕ):ℤ) := by
  classical
  funext k
  simp only [Finset.sum_apply,Pi.add_apply]
  rw [variablePairs,Finset.sum_filter]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  have hs : ∀ i j : Fin r,
      (if i<j then unitExponent r i k + unitExponent r j k else 0) =
      (if i=k then (if k<j then (1:ℤ) else 0) else 0) +
      (if j=k then (if i<k then (1:ℤ) else 0) else 0) := by
    intro i j
    by_cases hi : i=k <;> by_cases hj : j=k <;>
      simp_all [unitExponent,Pi.single_apply]
  simp_rw [hs,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin r => if i=k then (if k<j then (1:ℤ) else 0) else 0)]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← Finset.sum_add_distrib]
  have hi : ∀ j : Fin r,
      (if k<j then (1:ℤ) else 0) + (if j<k then 1 else 0) =
        if j=k then 0 else 1 := by
    intro j
    split_ifs <;> omega
  simp_rw [hi]
  simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add]
  have he : (Finset.univ.filter (fun j : Fin r => ¬ j=k)) = Finset.univ.erase k := by
    ext j
    simp [eq_comm]
  rw [he]
  simp

/-- The Vandermonde product is nonzero at every rank, including rank zero
where it is the empty product one. -/
theorem vandermondeLaurent_ne_zero (r : ℕ) : vandermondeLaurent r ≠ 0 := by
  apply binomial_product_ne_zero
  intro ij hij
  apply (unitExponent_injective r).ne
  exact ne_of_lt (Finset.mem_filter.mp hij).2

/-- Every even integer Vandermonde power has a nonzero central coefficient.
Each variable's exponent is (r-1)t. This is a finite uniform theorem, not
merely a checked list of small screening parameters. -/
theorem vandermonde_central_coefficient_ne_zero (r t : ℕ) :
    (vandermondeLaurent r ^ (2*t))
      (fun _ : Fin r => (((r-1)*t:ℕ):ℤ)) ≠ 0 := by
  have h := binomial_product_central_ne_zero (variablePairs r)
    (fun ij => unitExponent r ij.1) (fun ij => unitExponent r ij.2)
    (fun ij hij => (unitExponent_injective r).ne (ne_of_lt (Finset.mem_filter.mp hij).2)) t
  rw [variablePairs_exponent_sum] at h
  have he : (t • fun _ : Fin r => ((r-1:ℕ):ℤ)) =
      fun _ : Fin r => (((r-1)*t:ℕ):ℤ) := by
    funext k
    change t • ((r-1:ℕ):ℤ) = (((r-1)*t:ℕ):ℤ)
    simp [nsmul_eq_mul,Nat.cast_mul,mul_comm]
  rw [he] at h
  exact h

end VOA.VirasoroScreening

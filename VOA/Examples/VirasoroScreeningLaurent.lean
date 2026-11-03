/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic

/-!
# Finite Laurent coefficient positivity for integer screenings

Reversing every exponent turns the constant coefficient of a polynomial
 times its reversal into a sum of rational squares. A product of binomials
has a precise reversal law. Its even powers consequently have a nonzero
central coefficient, without a Dyson or Selberg product formula.
These are finite algebraic statements; no screening Ward identity or
Virasoro singular-state existence is assumed or concluded here.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open AddMonoidAlgebra

/-- Finite Laurent expressions with rational coefficients and an additive
exponent group. All sums and products have finite support. -/
abbrev Laurent (G : Type*) [AddCommGroup G] := AddMonoidAlgebra ℚ G

/-- Reverse every exponent, keeping rational coefficients fixed. -/
noncomputable def reverse {G : Type*} [AddCommGroup G] : Laurent G ≃+* Laurent G :=
  AddMonoidAlgebra.mapDomainRingEquiv ℚ (AddEquiv.neg G)

/-- Reversal sends the coefficient at g to the original coefficient at -g. -/
theorem reverse_apply {G : Type*} [AddCommGroup G] (P : Laurent G) (g : G) :
    reverse P g = P (-g) := by
  exact AddMonoidAlgebra.mapDomainRingEquiv_apply _ _ _

/-- A single Laurent monomial reverses its exponent. -/
theorem reverse_single {G : Type*} [AddCommGroup G] (g : G) (q : ℚ) :
    reverse (single g q : Laurent G) = single (-g) q := by
  classical
  ext h
  simp [reverse_apply, single_apply, neg_eq_iff_eq_neg]

/-- The constant coefficient of P times its reversal is a sum of squares
of all nonzero coefficients of P. This is an exact finite identity. -/
theorem constant_mul_reverse {G : Type*} [AddCommGroup G] (P : Laurent G) :
    (P * reverse P) 0 = ∑ g ∈ P.support, (P g)^2 := by
  classical
  simp [AddMonoidAlgebra.mul_apply_left, reverse_apply, Finsupp.sum, pow_two]

/-- A nonzero rational Laurent expression has strictly positive squared
coefficient norm. No positivity of the individual coefficients is needed. -/
theorem constant_mul_reverse_pos {G : Type*} [AddCommGroup G]
    (P : Laurent G) (hP : P ≠ 0) : 0 < (P * reverse P) 0 := by
  classical
  rw [constant_mul_reverse]
  apply Finset.sum_pos'
  · intro g hg
    exact sq_nonneg _
  · obtain ⟨g,hg⟩ := Finsupp.support_nonempty_iff.mpr hP
    exact ⟨g,hg,sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)⟩

/-- Reversing z^a-z^b multiplies it by -z^(-a-b). This elementary
identity is the source of the central coefficient symmetry. -/
theorem reverse_binomial {G : Type*} [AddCommGroup G] (a b : G) :
    reverse (single a 1 - single b 1 : Laurent G) =
      single (-(a+b)) (-1) * (single a 1 - single b 1) := by
  rw [map_sub,reverse_single,reverse_single,mul_sub,single_mul_single,single_mul_single]
  have ha : -(a+b)+a = -b := by abel
  have hb : -(a+b)+b = -a := by abel
  simp only [ha,hb]
  simp only [neg_one_mul]
  rw [AddMonoidAlgebra.single_neg,AddMonoidAlgebra.single_neg]
  abel

/-- A finite product of differences reverses by one sign per factor and
one common monomial shift. The shift adds both exponents of every factor. -/
theorem reverse_binomial_product {G I : Type*} [AddCommGroup G]
    (S : Finset I) (a b : I → G) :
    reverse (∏ i ∈ S, (single (a i) 1 - single (b i) 1 : Laurent G)) =
      single (-(∑ i ∈ S, (a i+b i))) ((-1 : ℚ)^S.card) *
        ∏ i ∈ S, (single (a i) 1 - single (b i) 1 : Laurent G) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def,reverse_single]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi,Finset.card_insert_of_notMem hi,
      map_mul,reverse_binomial,ih]
    rw [show (single (-(a i+b i)) (-1) * (single (a i) 1-single (b i) 1)) *
        (single (-(∑ j ∈ S, (a j+b j))) ((-1:ℚ)^S.card) *
          ∏ j ∈ S, (single (a j) 1-single (b j) 1 : Laurent G)) =
        (single (-(a i+b i)) (-1) *
          single (-(∑ j ∈ S, (a j+b j))) ((-1:ℚ)^S.card)) *
          ((single (a i) 1-single (b i) 1) *
          ∏ j ∈ S, (single (a j) 1-single (b j) 1 : Laurent G)) by ring]
    rw [single_mul_single]
    congr 2
    · abel
    · rw [pow_succ]; ring

/-- Distinct exponents give a nonzero Laurent binomial. This can be checked
at the coefficient of its first monomial. -/
theorem binomial_ne_zero {G : Type*} [AddCommGroup G] {a b : G} (hab : a ≠ b) :
    (single a 1 - single b 1 : Laurent G) ≠ 0 := by
  classical
  intro h
  have hh := congrArg (fun P : Laurent G => P a) h
  change (single a (1:ℚ)) a - (single b (1:ℚ)) a = 0 at hh
  simp [AddMonoidAlgebra.single_apply, hab, Ne.symm hab] at hh

/-- Every product of nonzero Laurent binomials is nonzero when the exponent
group has unique sums; finite products of integer exponent groups do. -/
theorem binomial_product_ne_zero {G I : Type*} [AddCommGroup G] [UniqueSums G]
    (S : Finset I) (a b : I → G) (hab : ∀ i ∈ S, a i ≠ b i) :
    (∏ i ∈ S, (single (a i) 1-single (b i) 1 : Laurent G)) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => binomial_ne_zero (hab i hi))

/-- A reciprocal Laurent polynomial has a nonzero middle coefficient in
 every even power. Reversal converts that coefficient into its positive
 sum-of-squares norm, up to a nonzero rational factor. -/
theorem reciprocal_even_coefficient_ne_zero {G : Type*} [AddCommGroup G] [UniqueSums G]
    (P : Laurent G) (B : G) (e : ℚ) (hP : P ≠ 0)
    (hrev : reverse P = single (-B) e * P) (t : ℕ) :
    (P^(2*t)) (t • B) ≠ 0 := by
  have hpos := constant_mul_reverse_pos (P^t) (pow_ne_zero t hP)
  have hid : P^t * reverse (P^t) = single (-(t • B)) (e^t) * P^(2*t) := by
    rw [map_pow,hrev,mul_pow,single_pow]
    rw [smul_neg,show 2*t=t+t by omega,pow_add]
    ring
  rw [hid,single_mul_apply] at hpos
  simp only [neg_neg,add_zero] at hpos
  intro hz
  rw [hz,mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The central exponent of every even power of a product of differences
has a nonzero coefficient. This includes all integer Vandermonde powers. -/
theorem binomial_product_central_ne_zero {G I : Type*} [AddCommGroup G] [UniqueSums G]
    (S : Finset I) (a b : I → G) (hab : ∀ i ∈ S, a i ≠ b i) (t : ℕ) :
    ((∏ i ∈ S, (single (a i) 1-single (b i) 1 : Laurent G))^(2*t))
      (t • ∑ i ∈ S, (a i+b i)) ≠ 0 := by
  exact reciprocal_even_coefficient_ne_zero _ _ _
    (binomial_product_ne_zero S a b hab) (reverse_binomial_product S a b) t

end VOA.VirasoroScreening

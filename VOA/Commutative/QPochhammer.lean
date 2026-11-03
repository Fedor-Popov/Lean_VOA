/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite q-Pochhammer products and the formal Euler product

Foundations for Section 5 of Arakawa--Dai, arXiv:2609.33348.
All infinite-product coefficients are defined by their finite, stable truncations.
No analytic convergence, vertex-algebra character formula, or additional axiom is used.
-/

namespace VOA.QSeries

open scoped BigOperators

section FiniteProducts

variable {R : Type*} [CommRing R]

/-- The finite q-Pochhammer product `(a;q)_n`. -/
def pochhammer (a q : R) (n : ℕ) : R :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

@[simp] theorem pochhammer_zero (a q : R) : pochhammer a q 0 = 1 := by
  simp [pochhammer]

theorem pochhammer_succ (a q : R) (n : ℕ) :
    pochhammer a q (n + 1) = pochhammer a q n * (1 - a * q ^ n) := by
  exact Finset.prod_range_succ _ _

@[simp] theorem pochhammer_one (a q : R) : pochhammer a q 1 = 1 - a := by
  simp [pochhammer]

@[simp] theorem pochhammer_zero_left (q : R) (n : ℕ) :
    pochhammer 0 q n = 1 := by
  simp [pochhammer]

/-- Split a finite q-Pochhammer product at any index. -/
theorem pochhammer_add (a q : R) (n m : ℕ) :
    pochhammer a q (n + m) =
      pochhammer a q n * pochhammer (a * q ^ n) q m := by
  unfold pochhammer
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add, mul_assoc]

/-- The denominator product `(q)_n = (q;q)_n`. -/
def qFactorial (q : R) (n : ℕ) : R := pochhammer q q n

@[simp] theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 :=
  pochhammer_zero q q

theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * (1 - q ^ (n + 1)) := by
  simp only [qFactorial, pochhammer_succ, pow_succ']

theorem qFactorial_eq_prod (q : R) (n : ℕ) :
    qFactorial q n = ∏ j ∈ Finset.range n, (1 - q ^ (j + 1)) := by
  simp only [qFactorial, pochhammer, pow_succ']

theorem qFactorial_add (q : R) (n m : ℕ) :
    qFactorial q (n + m) = qFactorial q n * pochhammer (q ^ (n + 1)) q m := by
  simpa only [qFactorial, pow_succ'] using pochhammer_add q q n m

end FiniteProducts

section FormalProducts

variable {R : Type*} [CommRing R]

@[simp] theorem constantCoeff_qFactorial (n : ℕ) :
    PowerSeries.constantCoeff (qFactorial (PowerSeries.X : PowerSeries R) n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [qFactorial_succ, ih]

/-- Every finite denominator product is invertible as a formal power series. -/
theorem isUnit_qFactorial (n : ℕ) :
    IsUnit (qFactorial (PowerSeries.X : PowerSeries R) n) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

/-- A newly appended Euler factor cannot affect a coefficient of smaller degree. -/
theorem coeff_qFactorial_succ (d n : ℕ) (h : d ≤ n) :
    PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) (n + 1)) =
      PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) n) := by
  rw [qFactorial_succ, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp [show ¬ n + 1 ≤ d by omega]

/-- Finite products have identical degree-`d` coefficients once their cutoffs exceed `d`. -/
theorem coeff_qFactorial_stable (d n N : ℕ) (hd : d ≤ n) (hn : n ≤ N) :
    PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) N) =
      PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, coeff_qFactorial_succ d (n + r) (by omega), ih]

/-- The formal Euler product `(q)_∞`, with each coefficient read at a sufficient finite cutoff. -/
noncomputable def euler : PowerSeries R :=
  PowerSeries.mk fun d => PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) d)

/-- Any cutoff at least `d` computes the degree-`d` coefficient of the infinite product. -/
theorem coeff_euler (d n : ℕ) (h : d ≤ n) :
    PowerSeries.coeff d (euler : PowerSeries R) =
      PowerSeries.coeff d (qFactorial (PowerSeries.X : PowerSeries R) n) := by
  rw [euler, PowerSeries.coeff_mk]
  exact (coeff_qFactorial_stable d d n le_rfl h).symm

@[simp] theorem constantCoeff_euler :
    PowerSeries.constantCoeff (euler : PowerSeries R) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_euler 0 0 le_rfl]
  simp

/-- The infinite denominator product is a unit, just as every finite truncation is. -/
theorem isUnit_euler : IsUnit (euler : PowerSeries R) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

/-- Inversion at a fixed unit constant term depends only on coefficients up to the
requested degree. This is the formal justification for passing finite-product denominator
identities to coefficientwise limits. -/
theorem coeff_invOfUnit_congr (u : Rˣ) (d : ℕ) (f g : PowerSeries R)
    (h : ∀ j, j ≤ d → PowerSeries.coeff j f = PowerSeries.coeff j g) :
    PowerSeries.coeff d (PowerSeries.invOfUnit f u) =
      PowerSeries.coeff d (PowerSeries.invOfUnit g u) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rw [PowerSeries.coeff_invOfUnit, PowerSeries.coeff_invOfUnit]
      split_ifs with hd
      · rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro ij hij
        have hsum : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
        split_ifs with hj
        · rw [h ij.1 (by omega), ih ij.2 hj (fun j hjd => h j (by omega))]
        · rfl

/-- The reciprocal finite Euler product, defined over every commutative coefficient ring. -/
noncomputable def reciprocalQFactorial (n : ℕ) : PowerSeries R :=
  PowerSeries.invOfUnit (qFactorial PowerSeries.X n) 1

/-- The reciprocal infinite Euler product, defined by its unit constant term. -/
noncomputable def reciprocalEuler : PowerSeries R := PowerSeries.invOfUnit euler 1

@[simp] theorem qFactorial_mul_reciprocal (n : ℕ) :
    qFactorial PowerSeries.X n * (reciprocalQFactorial n : PowerSeries R) = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

@[simp] theorem euler_mul_reciprocal :
    (euler : PowerSeries R) * reciprocalEuler = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

/-- Reciprocal denominator coefficients stabilize at the same cutoff as the products. -/
theorem coeff_reciprocalEuler (d n : ℕ) (h : d ≤ n) :
    PowerSeries.coeff d (reciprocalEuler : PowerSeries R) =
      PowerSeries.coeff d (reciprocalQFactorial n : PowerSeries R) := by
  apply coeff_invOfUnit_congr
  intro j hj
  exact coeff_euler j n (hj.trans h)

end FormalProducts

end VOA.QSeries

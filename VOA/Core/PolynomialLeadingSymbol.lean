/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Weighted leading symbols of finite polynomials and formal series

A leading-symbol relation records a homogeneous top part and strictly
smaller errors. Its product rule retains all cross terms and works even
when either top part is zero. Coefficientwise extension to formal series
uses only finite antidiagonal sums, with no convergence requirement.
-/
namespace VOA.PolynomialLeading
noncomputable section
open scoped BigOperators
open MvPolynomial
open Classical
variable {σ : Type*} {w : σ → ℕ}

/-- Every monomial in the polynomial has weight at most d. -/
def AtMost (w : σ → ℕ) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {P | ∀ e, coeff e P ≠ 0 → Finsupp.weight w e ≤ d}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hp hq e he
    by_cases h : coeff e P = 0
    · exact hq e (by simpa [coeff_add, h] using he)
    · exact hp e h
  smul_mem' := by
    intro c P hp e he
    exact hp e (right_ne_zero_of_mul (by simpa [coeff_smul] using he))

/-- Every nonzero coefficient lies strictly below weight d. -/
def Below (w : σ → ℕ) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {P | ∀ e, coeff e P ≠ 0 → Finsupp.weight w e < d}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hp hq e he
    by_cases h : coeff e P = 0
    · exact hq e (by simpa [coeff_add, h] using he)
    · exact hp e h
  smul_mem' := by
    intro c P hp e he
    exact hp e (right_ne_zero_of_mul (by simpa [coeff_smul] using he))

/-- A polynomial with homogeneous top Q and strictly lower remainder. -/
structure Symbol (w : σ → ℕ) (d : ℕ) (P Q : MvPolynomial σ ℂ) : Prop where
  homogeneous : Q.IsWeightedHomogeneous w d
  remainder : P - Q ∈ Below w d

/-- A homogeneous polynomial has its indicated upper bound. -/
theorem homogeneous_atMost {d : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsWeightedHomogeneous w d) : P ∈ AtMost w d :=
  fun e he => (h he).le

/-- A strict bound implies the corresponding weak bound. -/
theorem below_atMost {d : ℕ} {P : MvPolynomial σ ℂ}
    (h : P ∈ Below w d) : P ∈ AtMost w d := fun e he => (h e he).le

/-- Bounds add under multiplication. -/
theorem atMost_mul {a b : ℕ} {P Q : MvPolynomial σ ℂ}
    (hp : P ∈ AtMost w a) (hq : Q ∈ AtMost w b) : P*Q ∈ AtMost w (a+b) := by
  intro e he
  rw [coeff_mul] at he
  obtain ⟨⟨u,v⟩, huv, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add]
  exact Nat.add_le_add (hp u (left_ne_zero_of_mul ht)) (hq v (right_ne_zero_of_mul ht))

/-- A strict bound on one factor keeps the product strictly below the
sum of the two bounds. -/
theorem below_mul_atMost {a b : ℕ} {P Q : MvPolynomial σ ℂ}
    (hp : P ∈ Below w a) (hq : Q ∈ AtMost w b) : P*Q ∈ Below w (a+b) := by
  intro e he
  rw [coeff_mul] at he
  obtain ⟨⟨u,v⟩, huv, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp huv, map_add]
  exact Nat.add_lt_add_of_lt_of_le (hp u (left_ne_zero_of_mul ht))
    (hq v (right_ne_zero_of_mul ht))

/-- The symmetric strict product estimate. -/
theorem atMost_mul_below {a b : ℕ} {P Q : MvPolynomial σ ℂ}
    (hp : P ∈ AtMost w a) (hq : Q ∈ Below w b) : P*Q ∈ Below w (a+b) := by
  simpa [mul_comm, add_comm] using below_mul_atMost hq hp

/-- Any polynomial with a leading symbol satisfies its upper bound. -/
theorem Symbol.atMost {d : ℕ} {P Q : MvPolynomial σ ℂ} (h : Symbol w d P Q) :
    P ∈ AtMost w d := by
  have hh := (AtMost w d).add_mem (below_atMost h.remainder) (homogeneous_atMost h.homogeneous)
  simpa using hh

/-- A homogeneous polynomial is its own leading symbol. -/
theorem Symbol.exact {d : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsWeightedHomogeneous w d) : Symbol w d P P :=
  ⟨h, by simp only [sub_self]; exact (Below w d).zero_mem⟩

/-- Zero has zero leading symbol at any chosen weight. -/
theorem Symbol.zero (w : σ → ℕ) (d : ℕ) : Symbol w d 0 0 :=
  Symbol.exact (isWeightedHomogeneous_zero ℂ w d)

/-- Addition of two symbols at the same weight. -/
theorem Symbol.add {d : ℕ} {P Q U V : MvPolynomial σ ℂ}
    (h : Symbol w d P Q) (g : Symbol w d U V) : Symbol w d (P+U) (Q+V) := by
  refine ⟨h.homogeneous.add g.homogeneous, ?_⟩
  convert (Below w d).add_mem h.remainder g.remainder using 1 <;> abel

/-- Negation preserves the leading-symbol relation. -/
theorem Symbol.neg {d : ℕ} {P Q : MvPolynomial σ ℂ}
    (h : Symbol w d P Q) : Symbol w d (-P) (-Q) := by
  refine ⟨(weightedHomogeneousSubmodule ℂ w d).neg_mem h.homogeneous, ?_⟩
  convert (Below w d).neg_mem h.remainder using 1 <;> abel

/-- Multiplication multiplies the leading symbols and adds their
weights; the remainder estimate includes both cross terms. -/
theorem Symbol.mul {a b : ℕ} {P Q U V : MvPolynomial σ ℂ}
    (h : Symbol w a P Q) (g : Symbol w b U V) : Symbol w (a+b) (P*U) (Q*V) := by
  refine ⟨h.homogeneous.mul g.homogeneous, ?_⟩
  have hh := (Below w (a+b)).add_mem
    (below_mul_atMost h.remainder g.atMost)
    (atMost_mul_below (homogeneous_atMost h.homogeneous) g.remainder)
  convert hh using 1 <;> ring

/-- A finite sum at one weight has the sum of its leading symbols. -/
theorem Symbol.sum {ι : Type*} (s : Finset ι) (d : ℕ)
    (P Q : ι → MvPolynomial σ ℂ) (h : ∀ i ∈ s, Symbol w d (P i) (Q i)) :
    Symbol w d (∑ i ∈ s, P i) (∑ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Symbol.zero w d
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

/-- A lower-weight homogeneous term has zero symbol at any larger weight. -/
theorem Symbol.lower {a b : ℕ} {P : MvPolynomial σ ℂ}
    (h : P.IsWeightedHomogeneous w a) (hab : a < b) : Symbol w b P 0 := by
  refine ⟨isWeightedHomogeneous_zero ℂ w b, ?_⟩
  simpa only [sub_zero] using (show P ∈ Below w b from fun e he => h he ▸ hab)

/-- Natural powers multiply both the leading symbol and its weight. -/
theorem Symbol.pow {d : ℕ} {P Q : MvPolynomial σ ℂ}
    (h : Symbol w d P Q) (n : ℕ) : Symbol w (n*d) (P^n) (Q^n) := by
  induction n with
  | zero => simpa using Symbol.exact (isWeightedHomogeneous_one ℂ w)
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul h

/-- Finite products have the product of their symbols and the sum of
individual weights, including the empty product. -/
theorem Symbol.prod {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (P Q : ι → MvPolynomial σ ℂ) (h : ∀ i ∈ s, Symbol w (d i) (P i) (Q i)) :
    Symbol w (∑ i ∈ s, d i) (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Symbol.exact (isWeightedHomogeneous_one ℂ w)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (by simp)).mul (ih fun j hj => h j (by simp [hj]))

/-- The indicated homogeneous component is exactly the symbol. -/
theorem Symbol.component {d : ℕ} {P Q : MvPolynomial σ ℂ} (h : Symbol w d P Q) :
    weightedHomogeneousComponent w d P = Q := by
  ext e
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with he
  · have hr : coeff e (P-Q) = 0 := by
      by_contra hc
      exact (Nat.lt_irrefl d) (he ▸ h.remainder e hc)
    simpa only [coeff_sub, sub_eq_zero] using hr
  · exact (h.homogeneous.coeff_eq_zero e he).symm

/-- Every component above the declared leading weight is zero. -/
theorem Symbol.component_above {d e : ℕ} {P Q : MvPolynomial σ ℂ}
    (h : Symbol w d P Q) (he : d < e) : weightedHomogeneousComponent w e P = 0 := by
  ext u
  simp only [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hu
  · by_contra hc
    exact (Nat.not_le_of_lt he) (hu ▸ h.atMost u hc)
  · rfl

/-- A coefficientwise symbol relation for formal series. -/
def SeriesSymbol (w : σ → ℕ) (d : ℕ)
    (P Q : PowerSeries (MvPolynomial σ ℂ)) : Prop :=
  ∀ n, Symbol w d (PowerSeries.coeff n P) (PowerSeries.coeff n Q)

/-- A coefficientwise homogeneous series is its own symbol. -/
theorem SeriesSymbol.exact {d : ℕ} {P : PowerSeries (MvPolynomial σ ℂ)}
    (h : ∀ n, (PowerSeries.coeff n P).IsWeightedHomogeneous w d) :
    SeriesSymbol w d P P := fun n => Symbol.exact (h n)

/-- Series negation preserves all coefficientwise symbols. -/
theorem SeriesSymbol.neg {d : ℕ} {P Q : PowerSeries (MvPolynomial σ ℂ)}
    (h : SeriesSymbol w d P Q) : SeriesSymbol w d (-P) (-Q) := by
  intro n
  simpa only [map_neg] using (h n).neg

/-- Every scalar multiple has the corresponding scalar-multiplied symbol. -/
theorem SeriesSymbol.smul {d : ℕ} {P Q : PowerSeries (MvPolynomial σ ℂ)}
    (h : SeriesSymbol w d P Q) (c : ℂ) : SeriesSymbol w d (c • P) (c • Q) := by
  intro n
  simp only [PowerSeries.coeff_smul]
  refine ⟨(weightedHomogeneousSubmodule ℂ w d).smul_mem c (h n).homogeneous, ?_⟩
  simpa only [smul_sub] using (Below w d).smul_mem c (h n).remainder

/-- Series addition preserves a common coefficientwise leading weight. -/
theorem SeriesSymbol.add {d : ℕ} {P Q U V : PowerSeries (MvPolynomial σ ℂ)}
    (h : SeriesSymbol w d P Q) (g : SeriesSymbol w d U V) :
    SeriesSymbol w d (P+U) (Q+V) := by
  intro n
  simp only [map_add]
  exact (h n).add (g n)

/-- Series multiplication uses only the finite coefficient antidiagonal,
so the polynomial symbol product rule applies at every jet order. -/
theorem SeriesSymbol.mul {a b : ℕ} {P Q U V : PowerSeries (MvPolynomial σ ℂ)}
    (h : SeriesSymbol w a P Q) (g : SeriesSymbol w b U V) :
    SeriesSymbol w (a+b) (P*U) (Q*V) := by
  intro n
  simp only [PowerSeries.coeff_mul]
  exact Symbol.sum _ _ _ _ fun ij _ => (h ij.1).mul (g ij.2)

/-- Linearly independent leading symbols prevent any finite linear
relation among the original polynomials. Only a largest weight in the
finite proposed relation is needed. -/
theorem linearIndependent_of_symbols {ι : Type*} (d : ι → ℕ)
    (P Q : ι → MvPolynomial σ ℂ) (h : ∀ i, Symbol w (d i) (P i) (Q i))
    (hq : LinearIndependent ℂ Q) : LinearIndependent ℂ P := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j => g j ≠ 0
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  let n := (t.image d).max' (ht.image d)
  obtain ⟨j₀,hj₀,hdegree⟩ := Finset.mem_image.mp (Finset.max'_mem (t.image d) (ht.image d))
  have hp := congrArg (weightedHomogeneousComponent w n) hsum
  simp only [map_sum, map_smul, map_zero] at hp
  have hh : ∑ j ∈ s, (if d j = n then g j else 0) • Q j = 0 := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hg : g j = 0
    · simp [hg]
    · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hj,hg⟩
      have hd : d j ≤ n := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j,hjt,rfl⟩)
      rcases hd.eq_or_lt with he | he
      · rw [if_pos he, ← he, (h j).component]
      · rw [if_neg (ne_of_lt he), (h j).component_above he]
        simp
  have hz := linearIndependent_iff'.mp hq s
    (fun j => if d j = n then g j else 0) hh j₀ (Finset.mem_filter.mp hj₀).1
  exact (Finset.mem_filter.mp hj₀).2 (by simpa only [hdegree, n, if_true] using hz)

end
end VOA.PolynomialLeading

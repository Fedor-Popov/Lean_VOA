/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningOperators

/-!
# Finite auxiliary-degree bounds for the screening coefficient

The selected degree after removing the Vandermonde is r(q-1). Any error
whose remaining total auxiliary degree is larger therefore has zero selected
coefficient. The argument uses finite Laurent convolution; it does not assume
an infinite exponential or a screening Ward equation.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening
open scoped BigOperators
noncomputable section

/-- Total integer degree of an auxiliary Laurent monomial. -/
def exponentDegree (r : ℕ) : (Fin r → ℤ) →+ ℤ where
  toFun g := ∑ i, g i
  map_zero' := by simp
  map_add' g h := by simp [Finset.sum_add_distrib]

/-- A Laurent expression has lower degree d when all coefficients of
smaller total degree vanish. Negative exponents are permitted in the carrier. -/
def LowerDegree {r : ℕ} (d : ℤ) (P : Auxiliary r) : Prop :=
  ∀ g, exponentDegree r g<d → P g=0

/-- Zero satisfies every auxiliary lower-degree bound. -/
theorem LowerDegree.zero (r : ℕ) (d : ℤ) : LowerDegree d (0 : Auxiliary r) := by
  intro g hg
  rfl

/-- A monomial satisfies any bound no greater than its exponent degree. -/
theorem LowerDegree.single (r : ℕ) (d : ℤ) (g : Fin r → ℤ) (p : WakFock)
    (h : d≤exponentDegree r g) : LowerDegree d (single g p) := by
  classical
  intro x hx
  have hne : g≠x := by intro he; subst x; omega
  exact Finsupp.single_eq_of_ne hne.symm

/-- Finite sums preserve a common lower-degree bound. -/
theorem LowerDegree.sum {r : ℕ} {I : Type*} (d : ℤ) (S : Finset I)
    (P : I → Auxiliary r) (h : ∀ i∈S, LowerDegree d (P i)) :
    LowerDegree d (∑ i∈S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LowerDegree.zero r d
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      intro g hg
      change P i g + (∑ j∈S, P j) g=0
      rw [h i (by simp) g hg,ih (fun j hj => h j (by simp [hj])) g hg,add_zero]

/-- Products add lower-degree bounds, by finite Laurent convolution. -/
theorem LowerDegree.mul {r : ℕ} {a b : ℤ} {P Q : Auxiliary r}
    (hP : LowerDegree a P) (hQ : LowerDegree b Q) : LowerDegree (a+b) (P*Q) := by
  classical
  intro g hg
  rw [AddMonoidAlgebra.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  dsimp only
  split_ifs with hxy
  · by_cases hx' : exponentDegree r x<a
    · rw [hP x hx',zero_mul]
    · have hy' : exponentDegree r y<b := by
        rw [← hxy,map_add] at hg
        omega
      rw [hQ y hy',mul_zero]
  · rfl

/-- The auxiliary unit has lower degree zero. -/
theorem LowerDegree.one (r : ℕ) : LowerDegree 0 (1 : Auxiliary r) := by
  rw [AddMonoidAlgebra.one_def]
  exact LowerDegree.single r 0 0 1 (by simp)

/-- A finite product has the sum of its factors' lower-degree bounds. -/
theorem LowerDegree.prod {r : ℕ} {I : Type*} (S : Finset I) (d : I → ℤ)
    (P : I → Auxiliary r) (h : ∀ i∈S, LowerDegree (d i) (P i)) :
    LowerDegree (∑ i∈S, d i) (∏ i∈S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LowerDegree.one r
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi]
      exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

/-- Natural powers multiply a lower-degree bound by the exponent. -/
theorem LowerDegree.pow {r : ℕ} {d : ℤ} {P : Auxiliary r}
    (h : LowerDegree d P) (n : ℕ) : LowerDegree ((n : ℤ)*d) (P^n) := by
  induction n with
  | zero => simpa using LowerDegree.one r
  | succ n ih =>
      convert ih.mul h using 1 <;> simp [pow_succ,Nat.cast_add,add_mul]

/-- Subtraction preserves a common lower-degree bound. -/
theorem LowerDegree.sub {r : ℕ} {d : ℤ} {P Q : Auxiliary r}
    (hP : LowerDegree d P) (hQ : LowerDegree d Q) : LowerDegree d (P-Q) := by
  intro g hg
  change P g-Q g=0
  rw [hP g hg,hQ g hg,sub_zero]

/-- A stronger lower-degree bound implies every weaker one. -/
theorem LowerDegree.mono {r : ℕ} {a b : ℤ} {P : Auxiliary r}
    (hP : LowerDegree b P) (h : a≤b) : LowerDegree a P := by
  intro g hg
  exact hP g (lt_of_lt_of_le hg h)

/-- Each auxiliary unit has integer degree one. -/
theorem exponentDegree_unit (r : ℕ) (i : Fin r) :
    exponentDegree r (unitExponent r i)=1 := by
  classical
  simp [exponentDegree,unitExponent,Pi.single_apply]

/-- Multiples of an auxiliary unit have the corresponding integer degree. -/
theorem exponentDegree_smul_unit (r : ℕ) (i : Fin r) (n : ℤ) :
    exponentDegree r (n • unitExponent r i)=n := by
  rw [map_zsmul,exponentDegree_unit]
  simp

/-- The finite beta series contains only nonnegative auxiliary degrees. -/
theorem betaFactor_lower (r D : ℕ) (i : Fin r) : LowerDegree 0 (betaFactor r D i) := by
  apply LowerDegree.sum
  intro j hj
  apply LowerDegree.single
  rw [exponentDegree_smul_unit]
  omega

/-- The boson power sum has auxiliary degree at least m. -/
theorem bosonPower_lower (r m : ℕ) : LowerDegree (m : ℤ) (bosonPower r m) := by
  apply LowerDegree.sum
  intro i hi
  exact LowerDegree.single r _ _ _ (by rw [exponentDegree_smul_unit])

/-- A constant oscillator coefficient at auxiliary exponent zero has
lower degree zero. -/
theorem constant_lower (r : ℕ) (p : WakFock) : LowerDegree 0 (single 0 p : Auxiliary r) :=
  LowerDegree.single r 0 0 p (by simp)

/-- Each individual exponential summand has lower degree m times ell. -/
theorem exponentialTerm_lower (r M m ell : ℕ) :
    LowerDegree ((ell : ℤ)*m)
      (single 0 (MvPolynomial.C (((-(M : ℂ)/(m : ℂ))^ell)/(ell.factorial : ℂ))) *
        bosonPower r m ^ ell) := by
  simpa using (constant_lower r _).mul ((bosonPower_lower r m).pow ell)

/-- Truncated boson exponentials have no negative auxiliary degree. -/
theorem exponentialFactor_lower (r D M m : ℕ) :
    LowerDegree 0 (exponentialFactor r D M m) := by
  apply LowerDegree.sum
  intro ell hell
  exact (exponentialTerm_lower r M m ell).mono (by positivity)

/-- The Vandermonde has lower degree equal to its number of pairs. -/
theorem delta_lower (r : ℕ) : LowerDegree ((variablePairs r).card : ℤ) (delta r) := by
  rw [delta_product]
  have h := LowerDegree.prod (variablePairs r) (fun _ => (1 : ℤ))
    (fun ij => (single (unitExponent r ij.1) (1 : WakFock) - single (unitExponent r ij.2) 1))
    (by
      intro ij hij
      apply LowerDegree.sub <;> apply LowerDegree.single <;> simp [exponentDegree_unit])
  simpa using h

/-- The endpoint count for all Vandermonde pairs in integer arithmetic. -/
theorem twice_pair_card_int (r : ℕ) :
    (2 : ℤ)*(variablePairs r).card = (r : ℤ)*((r-1 : ℕ) : ℤ) := by
  have h := congrArg (exponentDegree r) (variablePairs_exponent_sum r)
  simp only [map_sum,map_add,exponentDegree_unit] at h
  simpa [exponentDegree,mul_comm,two_mul] using h

/-- The even Vandermonde power consumes exactly its full r(r-1)M degree
before the screening coefficient can see any beta or boson term. -/
theorem delta_power_lower (r M : ℕ) :
    LowerDegree ((r : ℤ)*((r-1 : ℕ) : ℤ)*M) (delta r^(2*M)) := by
  have h := (delta_lower r).pow (2*M)
  convert h using 1
  push_cast
  linear_combination -(M : ℤ)*twice_pair_card_int r

/-- The finite product of all beta and boson factors has lower degree zero. -/
theorem screening_factors_lower (r q M : ℕ) :
    LowerDegree 0 ((∏ i : Fin r, betaFactor r (r*(q-1)) i) *
      ∏ m∈Finset.range (r*(q-1)), exponentialFactor r (r*(q-1)) M (m+1)) := by
  have hb := LowerDegree.prod Finset.univ (fun _ : Fin r => (0 : ℤ))
    (betaFactor r (r*(q-1))) (fun i _ => betaFactor_lower r _ i)
  have he := LowerDegree.prod (Finset.range (r*(q-1))) (fun _ => (0 : ℤ))
    (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => exponentialFactor_lower r _ M _)
  simpa using hb.mul he

/-- Any remaining error of total degree greater than r(q-1) makes ZERO
contribution to the actual selected screening coefficient after multiplying
by the Vandermonde. This is the finite truncation exclusion bound. -/
theorem screening_high_degree_zero (r q M : ℕ) (hq : 0<q) (P : Auxiliary r)
    (hP : LowerDegree ((r : ℤ)*(q-1)+1) P) :
    (delta r^(2*M)*P) (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  apply ((delta_power_lower r M).mul hP)
  have hn : (r-1)*M+q-1 = (r-1)*M+(q-1) := by omega
  have hq' : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
  simp only [exponentDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hn,
    Nat.cast_add,Nat.cast_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,hq']
  nlinarith

/-- Multiplying a high-degree error by any nonnegative-degree remaining
factors still cannot affect the selected coefficient. -/
theorem screening_high_degree_product_zero (r q M : ℕ) (hq : 0<q)
    (P Q : Auxiliary r) (hP : LowerDegree ((r : ℤ)*(q-1)+1) P)
    (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(P*Q)) (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  apply screening_high_degree_zero r q M hq
  simpa using hP.mul hQ

/-- An omitted beta summand beyond the remaining degree has zero
selected coefficient, even after multiplying by any nonnegative-degree factors. -/
theorem screening_beta_tail_zero (r q M j : ℕ) (hq : 0<q) (i : Fin r)
    (hj : r*(q-1)<j) (Q : Auxiliary r) (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(single ((j : ℤ) • unitExponent r i)
      (MvPolynomial.X (0,j) : WakFock)*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  apply screening_high_degree_product_zero r q M hq _ Q _ hQ
  apply LowerDegree.single
  rw [exponentDegree_smul_unit]
  have hq' : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
  have hj' : (r : ℤ)*((q-1 : ℕ) : ℤ)<j := by exact_mod_cast hj
  rw [hq'] at hj'
  omega

/-- Every omitted positive-mode exponential summand has zero selected
coefficient. This proves the truncation exclusion for the explicit factorial
terms, without extending the exponential to an infinite series. -/
theorem screening_exponential_tail_zero (r q M m ell : ℕ) (hq : 0<q)
    (hm : 0<m) (hell : r*(q-1)<ell) (Q : Auxiliary r) (hQ : LowerDegree 0 Q) :
    (delta r^(2*M)*(((single 0
      (MvPolynomial.C (((-(M : ℂ)/(m : ℂ))^ell)/(ell.factorial : ℂ))) : Auxiliary r) *
        bosonPower r m ^ ell)*Q))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  apply screening_high_degree_product_zero r q M hq _ Q _ hQ
  apply (exponentialTerm_lower r M m ell).mono
  have hq' : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
  have hell' : (r : ℤ)*((q-1 : ℕ) : ℤ)<ell := by exact_mod_cast hell
  rw [hq'] at hell'
  have hm' : (1 : ℤ)≤m := by omega
  have he : (0 : ℤ)≤ell := by positivity
  nlinarith

end
end VOA.Wak.Screening

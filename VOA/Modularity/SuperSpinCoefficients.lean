/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperHalfWeightSquareBracket
import VOA.Modularity.ZhuNormalization
import VOA.Modularity.ThetaGroup
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Formal genus-one coefficients for the four spin sectors

This file formalizes the purely algebraic part of van Ekeren, arXiv:1111.0682v3, Section 3,
especially equation (3.1) and Lemma 3.1, for the four pairs
`(μ,λ) ∈ {+1,-1}²`.  We use the bit `0` for `+1` and `1` for `-1`.

The paper writes `q = exp(2πiτ)` and

`P_k^{μ,λ} = cusp + (2πi)^(k+1)/k! · LambertTail`.

Accordingly `spinP` below retains every factor of `2πi`.  The repository's `zhuG j` divides
the classical weight-`2j` Eisenstein series by `(2πi)^(2j)`; the comparison theorem at the end
therefore has the explicit factor `(spinTwoPiI)^(2j)`.

`FormalQSeries = ℂ → ℂ` can record fractional exponents.  We store these series on the
half-lattice `N/2`, `N : ℕ`.  In the `μ=+1` sectors the coefficients at odd `N` vanish, while
the `μ=-1` sectors may genuinely contain powers `q^(N/2)`.

There is no assertion here about convergence, holomorphy, or modular transformation.  The only
group statements concern the finite sector labels, and are algebraic modulo `2`.
-/

namespace VOA

open scoped BigOperators MatrixGroups

set_option autoImplicit false

/-! ## The finite phase and sector types -/

/-- A sign encoded additively: `0` is `+1`, `1` is `-1`. -/
abbrev SpinPhase := ZMod 2

namespace SpinPhase

def plus : SpinPhase := 0
def minus : SpinPhase := 1

/-- The complex sign represented by a phase bit. -/
noncomputable def value (a : SpinPhase) : ℂ := if a = plus then 1 else -1

@[simp] theorem value_plus : value plus = 1 := by simp [value, plus]
@[simp] theorem value_minus : value minus = -1 := by norm_num [value, plus, minus]

end SpinPhase

/-- A pair `(μ,λ)` of spatial and temporal sign phases. -/
structure SpinPair where
  mu : SpinPhase
  lambda : SpinPhase
deriving DecidableEq, Fintype

namespace SpinPair

@[ext] theorem ext {p q : SpinPair} (hmu : p.mu = q.mu)
    (hlambda : p.lambda = q.lambda) : p = q := by
  cases p
  cases q
  simp_all

def pp : SpinPair := ⟨SpinPhase.plus, SpinPhase.plus⟩
def pm : SpinPair := ⟨SpinPhase.plus, SpinPhase.minus⟩
def mp : SpinPair := ⟨SpinPhase.minus, SpinPhase.plus⟩
def mm : SpinPair := ⟨SpinPhase.minus, SpinPhase.minus⟩

/-- The right action `(mu,lambda) · A = (mu^a lambda^c, mu^b lambda^d)`, written additively
on sign bits and using the entries of `A` reduced modulo `2`. -/
def act (A : SL(2, ℤ)) (p : SpinPair) : SpinPair :=
  ⟨p.mu * ThetaGroup.redEntry A 0 0 + p.lambda * ThetaGroup.redEntry A 1 0,
   p.mu * ThetaGroup.redEntry A 0 1 + p.lambda * ThetaGroup.redEntry A 1 1⟩

@[simp] theorem act_one (p : SpinPair) : act 1 p = p := by
  cases p
  simp [act]

/-- This is a genuine right action. -/
theorem act_mul (A B : SL(2, ℤ)) (p : SpinPair) : act (A * B) p = act B (act A p) := by
  cases p
  apply SpinPair.ext <;> simp only [act, ThetaGroup.redEntry_mul_00, ThetaGroup.redEntry_mul_01,
    ThetaGroup.redEntry_mul_10, ThetaGroup.redEntry_mul_11]
  <;> ring

@[simp] theorem act_S (p : SpinPair) : act ModularGroup.S p = ⟨p.lambda, p.mu⟩ := by
  cases p
  simp [act]

@[simp] theorem act_T (p : SpinPair) :
    act ModularGroup.T p = ⟨p.mu, p.mu + p.lambda⟩ := by
  cases p
  simp [act]

@[simp] theorem act_T_sq (p : SpinPair) : act (ModularGroup.T ^ 2) p = p := by
  rw [pow_two, act_mul, act_T, act_T]
  apply SpinPair.ext
  · rfl
  · dsimp only
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Every element of `GammaTheta` either fixes a sector or swaps its two phase labels. -/
theorem act_gammaTheta_self_or_swap (A : ThetaGroup.GammaTheta) (p : SpinPair) :
    act (A : SL(2, ℤ)) p = p ∨ act (A : SL(2, ℤ)) p = ⟨p.lambda, p.mu⟩ := by
  have hA : ThetaGroup.IsThetaCongr (A : SL(2, ℤ)) := A.property
  unfold ThetaGroup.IsThetaCongr at hA
  rcases hA with hA | hA
  · left
    rcases hA with ⟨h00, h01, h10, h11⟩
    cases p
    simp [act, h00, h01, h10, h11]
  · right
    rcases hA with ⟨h00, h01, h10, h11⟩
    cases p
    simp [act, h00, h01, h10, h11]

end SpinPair

/-! ## Bernoulli and Lambert coefficients -/

/-- The constant `2πi`, kept visible to prevent a normalization mismatch. -/
noncomputable def spinTwoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I

/-- The representative `ε ∈ (-1,0]` with `exp(2πiε)=μ`: `0` for `+1` and `-1/2`
for `-1`. -/
noncomputable def spinEpsilon (mu : SpinPhase) : ℚ :=
  if mu = SpinPhase.plus then 0 else -(1 / 2)

@[simp] theorem spinEpsilon_plus : spinEpsilon SpinPhase.plus = 0 := by
  simp [spinEpsilon]

@[simp] theorem spinEpsilon_minus : spinEpsilon SpinPhase.minus = -(1 / 2) := by
  norm_num [spinEpsilon, SpinPhase.plus, SpinPhase.minus]

/-- Van Ekeren's Bernoulli argument `1+ε`: it is `1` for `μ=+1` and `1/2` for
`μ=-1` (where the chosen representative is `ε=-1/2`). -/
noncomputable def spinBernoulliArg (mu : SpinPhase) : ℚ :=
  if mu = SpinPhase.plus then 1 else 1 / 2

theorem spinBernoulliArg_eq (mu : SpinPhase) :
    spinBernoulliArg mu = 1 + spinEpsilon mu := by
  by_cases hmu : mu = SpinPhase.plus
  · simp [spinBernoulliArg, spinEpsilon, hmu]
  · norm_num [spinBernoulliArg, spinEpsilon, hmu]

/-- `B_n(1+ε)` in the convention of van Ekeren Lemma 3.1. -/
noncomputable def spinBernoulli (mu : SpinPhase) (n : ℕ) : ℚ :=
  (Polynomial.bernoulli n).eval (spinBernoulliArg mu)

@[simp] theorem spinBernoulli_plus (n : ℕ) :
    spinBernoulli SpinPhase.plus n = (Polynomial.bernoulli n).eval 1 := by
  simp [spinBernoulli, spinBernoulliArg]

@[simp] theorem spinBernoulli_minus (n : ℕ) :
    spinBernoulli SpinPhase.minus n = (Polynomial.bernoulli n).eval (1 / 2) := by
  norm_num [spinBernoulli, spinBernoulliArg, SpinPhase.plus, SpinPhase.minus]

/-- The exceptional `k=0`, `μ=+1`, `λ=-1` term `2πi/(1-λ) = πi`. -/
noncomputable def spinDeltaTerm (p : SpinPair) (k : ℕ) : ℂ :=
  if k = 0 ∧ p = SpinPair.pm then (Real.pi : ℂ) * Complex.I else 0

/-- The explicit cusp coefficient in Lemma 3.1. -/
noncomputable def spinPCusp (p : SpinPair) (k : ℕ) : ℂ :=
  spinDeltaTerm p k - spinTwoPiI ^ (k + 1) / (Nat.factorial (k + 1) : ℂ) * spinBernoulli p.mu (k + 1)

theorem spinPCusp_pp (k : ℕ) :
    spinPCusp SpinPair.pp k =
      -(spinTwoPiI ^ (k + 1) / (Nat.factorial (k + 1) : ℂ) *
        (Polynomial.bernoulli (k + 1)).eval 1) := by
  simp [spinPCusp, spinDeltaTerm, SpinPair.pp, SpinPair.pm, spinBernoulli,
    spinBernoulliArg, SpinPhase.plus, SpinPhase.minus]

theorem spinPCusp_pm (k : ℕ) :
    spinPCusp SpinPair.pm k =
      (if k = 0 then (Real.pi : ℂ) * Complex.I else 0) -
        spinTwoPiI ^ (k + 1) / (Nat.factorial (k + 1) : ℂ) *
          (Polynomial.bernoulli (k + 1)).eval 1 := by
  simp [spinPCusp, spinDeltaTerm, SpinPair.pm, spinBernoulli, spinBernoulliArg,
    SpinPhase.plus, SpinPhase.minus]

theorem spinPCusp_mp (k : ℕ) :
    spinPCusp SpinPair.mp k =
      -(spinTwoPiI ^ (k + 1) / (Nat.factorial (k + 1) : ℂ) *
        (Polynomial.bernoulli (k + 1)).eval (1 / 2)) := by
  simp [spinPCusp, spinDeltaTerm, SpinPair.mp, SpinPair.pm, spinBernoulli,
    spinBernoulliArg, SpinPhase.plus, SpinPhase.minus]

theorem spinPCusp_mm (k : ℕ) :
    spinPCusp SpinPair.mm k =
      -(spinTwoPiI ^ (k + 1) / (Nat.factorial (k + 1) : ℂ) *
        (Polynomial.bernoulli (k + 1)).eval (1 / 2)) := by
  simp [spinPCusp, spinDeltaTerm, SpinPair.mm, SpinPair.pm, spinBernoulli,
    spinBernoulliArg, SpinPhase.plus, SpinPhase.minus]

/-- The unique nonzero `P_0` cusp is the untwisted `(1,1)` value `-πi`. -/
@[simp] theorem spinPCusp_pp_zero :
    spinPCusp SpinPair.pp 0 = -(Real.pi : ℂ) * Complex.I := by
  norm_num [spinPCusp, spinDeltaTerm, SpinPair.pp, spinBernoulli, spinBernoulliArg,
    SpinPair.pm, SpinPhase.plus, SpinPhase.minus, spinTwoPiI, Polynomial.bernoulli_one]
  ring

@[simp] theorem spinPCusp_pm_zero : spinPCusp SpinPair.pm 0 = 0 := by
  norm_num [spinPCusp, spinDeltaTerm, SpinPair.pm, spinBernoulli, spinBernoulliArg,
    SpinPhase.plus, SpinPhase.minus, spinTwoPiI, Polynomial.bernoulli_one]
  ring

@[simp] theorem spinPCusp_mp_zero : spinPCusp SpinPair.mp 0 = 0 := by
  norm_num [spinPCusp, spinDeltaTerm, SpinPair.mp, spinBernoulli, spinBernoulliArg,
    SpinPair.pm, SpinPhase.plus, SpinPhase.minus, spinTwoPiI, Polynomial.bernoulli_one]

@[simp] theorem spinPCusp_mm_zero : spinPCusp SpinPair.mm 0 = 0 := by
  norm_num [spinPCusp, spinDeltaTerm, SpinPair.mm, spinBernoulli, spinBernoulliArg,
    SpinPair.pm, SpinPhase.plus, SpinPhase.minus, spinTwoPiI, Polynomial.bernoulli_one]

/-- Integral-lattice Lambert coefficient, before multiplication by `(2πi)^(k+1)/k!`.
Here `r=p.1>0` is the absolute spatial mode and `m=p.2>0` is the geometric-series index. -/
noncomputable def spinIntegralTail (lambda : SpinPhase) (k n : ℕ) : ℂ :=
  ∑ p ∈ n.divisorsAntidiagonal,
    ((p.1 : ℂ) ^ k * SpinPhase.value lambda ^ p.2 -
      (-(p.1 : ℂ)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2)

/-- Half-lattice Lambert coefficient.  Writing a positive mode as `a/2`, the spatial phase
`μ=-1` forces `a` to be odd, and total doubled exponent is `N = a*m`. -/
noncomputable def spinHalfTail (lambda : SpinPhase) (k N : ℕ) : ℂ :=
  ∑ p ∈ N.divisorsAntidiagonal,
    if Odd p.1 then
      ((p.1 : ℂ) / 2) ^ k * SpinPhase.value lambda ^ p.2 -
        (-((p.1 : ℂ) / 2)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2
    else 0

/-- Coefficient at `q^(N/2)`. -/
noncomputable def spinPNatCoeff (p : SpinPair) (k N : ℕ) : ℂ :=
  if N = 0 then spinPCusp p k
  else spinTwoPiI ^ (k + 1) / (Nat.factorial k : ℂ) *
    if p.mu = SpinPhase.plus then
      if Even N then spinIntegralTail p.lambda k (N / 2) else 0
    else spinHalfTail p.lambda k N

@[simp] theorem spinPNatCoeff_zero (p : SpinPair) (k : ℕ) :
    spinPNatCoeff p k 0 = spinPCusp p k := by simp [spinPNatCoeff]

theorem spinPNatCoeff_plus_odd (lambda : SpinPhase) (k N : ℕ) (hN : Odd N) :
    spinPNatCoeff ⟨SpinPhase.plus, lambda⟩ k N =
      if N = 0 then spinPCusp ⟨SpinPhase.plus, lambda⟩ k else 0 := by
  have h0 : N ≠ 0 := Nat.ne_zero_of_lt hN.pos
  have hne : ¬Even N := Nat.not_even_iff_odd.mpr hN
  rw [spinPNatCoeff, if_neg h0, if_pos rfl, if_neg hne, mul_zero, if_neg h0]

theorem spinPNatCoeff_plus_even (lambda : SpinPhase) (k N : ℕ) (h0 : N ≠ 0)
    (hN : Even N) :
    spinPNatCoeff ⟨SpinPhase.plus, lambda⟩ k N =
      spinTwoPiI ^ (k + 1) / (Nat.factorial k : ℂ) * spinIntegralTail lambda k (N / 2) := by
  rw [spinPNatCoeff, if_neg h0, if_pos rfl, if_pos hN]

theorem spinPNatCoeff_minus (lambda : SpinPhase) (k N : ℕ) (h0 : N ≠ 0) :
    spinPNatCoeff ⟨SpinPhase.minus, lambda⟩ k N =
      spinTwoPiI ^ (k + 1) / (Nat.factorial k : ℂ) * spinHalfTail lambda k N := by
  rw [spinPNatCoeff, if_neg h0,
    if_neg (by norm_num [SpinPhase.plus, SpinPhase.minus])]

/-! ## Embedding the half-lattice into `FormalQSeries` -/

/-- The exponent `N/2` as a complex number. -/
noncomputable def halfQExponent (N : ℕ) : ℂ := (N : ℂ) / 2

theorem halfQExponent_injective : Function.Injective halfQExponent := by
  intro m n h
  rw [halfQExponent, halfQExponent] at h
  have h' : (m : ℂ) = (n : ℂ) := by linear_combination 2 * h
  exact_mod_cast h'

/-- Embed coefficients indexed by doubled nonnegative exponents into the repository's
complex-exponent `FormalQSeries`. -/
noncomputable def halfLatticeQSeries (a : ℕ → ℂ) : FormalQSeries :=
  by
    classical
    exact fun e => if h : ∃ N : ℕ, e = halfQExponent N then a (Nat.find h) else 0

@[simp] theorem halfLatticeQSeries_apply (a : ℕ → ℂ) (N : ℕ) :
    halfLatticeQSeries a (halfQExponent N) = a N := by
  classical
  let h : ∃ M : ℕ, halfQExponent N = halfQExponent M := ⟨N, rfl⟩
  rw [halfLatticeQSeries, dif_pos h]
  have hfind : halfQExponent N = halfQExponent (Nat.find h) := Nat.find_spec h
  exact congrArg a (halfQExponent_injective hfind) |>.symm

theorem halfLatticeQSeries_support (a : ℕ → ℂ) {e : ℂ}
    (he : halfLatticeQSeries a e ≠ 0) : ∃ N : ℕ, e = halfQExponent N := by
  classical
  by_contra h
  exact he (by simp [halfLatticeQSeries, h])

/-- Van Ekeren's formal coefficient series `P_k^{μ,λ}`. -/
noncomputable def spinP (p : SpinPair) (k : ℕ) : FormalQSeries :=
  halfLatticeQSeries (spinPNatCoeff p k)

/-- The algebraic sector relabelling under `S`; this makes no analytic transformation claim. -/
theorem spinP_label_S (p : SpinPair) (k : ℕ) :
    spinP (SpinPair.act ModularGroup.S p) k = spinP ⟨p.lambda, p.mu⟩ k := by
  rw [SpinPair.act_S]

/-- The algebraic sector relabelling under `T²`; the pair is fixed. -/
theorem spinP_label_T_sq (p : SpinPair) (k : ℕ) :
    spinP (SpinPair.act (ModularGroup.T ^ 2) p) k = spinP p k := by
  rw [SpinPair.act_T_sq]

/-- On `GammaTheta`, the coefficient label is either fixed or swapped.  This is only the finite
label action, not the analytic modular transformation law of the series. -/
theorem spinP_label_gammaTheta (A : ThetaGroup.GammaTheta) (p : SpinPair) (k : ℕ) :
    spinP (SpinPair.act (A : SL(2, ℤ)) p) k = spinP p k ∨
      spinP (SpinPair.act (A : SL(2, ℤ)) p) k = spinP ⟨p.lambda, p.mu⟩ k := by
  rcases SpinPair.act_gammaTheta_self_or_swap A p with h | h
  · left; rw [h]
  · right; rw [h]

@[simp] theorem spinP_coeff_half (p : SpinPair) (k N : ℕ) :
    spinP p k (halfQExponent N) = spinPNatCoeff p k N :=
  halfLatticeQSeries_apply _ _

/-- All four sectors are supported on nonnegative half-integral exponents. -/
theorem spinP_fractional_support (p : SpinPair) (k : ℕ) {e : ℂ}
    (he : spinP p k e ≠ 0) : ∃ N : ℕ, e = halfQExponent N :=
  halfLatticeQSeries_support _ he

/-- In a `μ=+1` sector, odd doubled exponents vanish. -/
theorem spinP_plus_odd (lambda : SpinPhase) (k N : ℕ) (hN : Odd N) :
    spinP ⟨SpinPhase.plus, lambda⟩ k (halfQExponent N) = 0 := by
  rw [spinP_coeff_half, spinPNatCoeff_plus_odd lambda k N hN,
    if_neg (Nat.ne_zero_of_lt hN.pos)]

/-- The `μ=+1` sectors sharpen half-integral support to nonnegative integral support. -/
theorem spinP_plus_integral_support (lambda : SpinPhase) (k : ℕ) {e : ℂ}
    (he : spinP ⟨SpinPhase.plus, lambda⟩ k e ≠ 0) : ∃ n : ℕ, e = (n : ℂ) := by
  obtain ⟨N, rfl⟩ := spinP_fractional_support _ _ he
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    rw [hn, halfQExponent]
    push_cast
    ring
  · exact (he (spinP_plus_odd lambda k N hN)).elim

/-- The constant coefficient is exactly the explicit Bernoulli cusp term. -/
theorem spinP_cusp (p : SpinPair) (k : ℕ) : spinP p k 0 = spinPCusp p k := by
  rw [show (0 : ℂ) = halfQExponent 0 by simp [halfQExponent], spinP_coeff_half,
    spinPNatCoeff_zero]

/-! ## The untwisted compatibility cell -/

/-- For odd `k=2j-1`, the untwisted integral Lambert tail is twice the repository's
`lambertCoeff`, exactly as in van Ekeren Lemma 3.1. -/
theorem spinIntegralTail_plus_odd {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    spinIntegralTail SpinPhase.plus (2 * j - 1) n = 2 * lambertCoeff (2 * j - 1) n := by
  rw [spinIntegralTail, lambertCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [SpinPhase.value_plus, one_pow, inv_one]
  have hodd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  rw [neg_pow]
  simp [hodd.neg_one_pow]
  ring

/-- The untwisted cusp term has exactly the repository normalization times `(2πi)^(2j)`. -/
theorem spinPCusp_pp_odd {j : ℕ} (hj : j ≠ 0) :
    spinPCusp SpinPair.pp (2 * j - 1) = spinTwoPiI ^ (2 * j) * zhuG j 0 := by
  rw [spinPCusp_pp, zhuG_zero]
  have hk : 2 * j - 1 + 1 = 2 * j := by omega
  rw [hk, Polynomial.bernoulli_eval_one]
  have hne : 2 * j ≠ 1 := by omega
  rw [← bernoulli_eq_bernoulli'_of_ne_one hne]
  ring

/-- At `(μ,λ)=(1,1)`, `P_(2j-1)` is exactly `(2πi)^(2j)` times the repository's
Zhu-normalized `G_(2j)`, coefficient by coefficient. -/
theorem spinP_pp_eq_spinTwoPiI_pow_zhuG {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    spinP SpinPair.pp (2 * j - 1) (n : ℂ) = spinTwoPiI ^ (2 * j) * zhuG j n := by
  by_cases hn : n = 0
  · subst n
    rw [Nat.cast_zero, spinP_cusp, spinPCusp_pp_odd hj]
  · rw [show (n : ℂ) = halfQExponent (2 * n) by simp [halfQExponent], spinP_coeff_half,
      spinPNatCoeff, if_neg (by omega : 2 * n ≠ 0)]
    simp only [SpinPair.pp, SpinPhase.plus, if_true]
    have he : Even (2 * n) := ⟨n, by omega⟩
    simp only [if_pos he]
    change spinTwoPiI ^ (2 * j - 1 + 1) / (Nat.factorial (2 * j - 1) : ℂ) *
      spinIntegralTail SpinPhase.plus (2 * j - 1) (2 * n / 2) =
        spinTwoPiI ^ (2 * j) * zhuG j n
    rw [show 2 * n / 2 = n by omega, spinIntegralTail_plus_odd hj,
      zhuG_of_ne_zero j hn]
    have hk : 2 * j - 1 + 1 = 2 * j := by omega
    rw [hk]
    ring

/-- The same comparison expressed in the repository's constant-one Eisenstein normalization.
The Bernoulli nonvanishing hypothesis is exactly the existing bridge's bookkeeping hypothesis. -/
theorem spinP_pp_eq_spinTwoPiI_pow_zhuEisenstein {j : ℕ} (hj : j ≠ 0)
    (hB : ((bernoulli (2 * j) : ℚ) : ℂ) ≠ 0) (n : ℕ) :
    spinP SpinPair.pp (2 * j - 1) (n : ℂ) =
      spinTwoPiI ^ (2 * j) *
        (-(((bernoulli (2 * j) : ℚ) : ℂ) / (Nat.factorial (2 * j) : ℂ)) *
          zhuEisenstein j n) := by
  rw [spinP_pp_eq_spinTwoPiI_pow_zhuG hj,
    zhuG_eq_smul_zhuEisenstein hj hB n]

end VOA

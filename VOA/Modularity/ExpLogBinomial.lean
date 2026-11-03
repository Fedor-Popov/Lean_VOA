/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SquareBracketSubst

/-!
# `exp ∘ log`, the binomial series, and the three weight-matching identities

The weight matching in Zhu's recursion (Prop. 4.3.2) needs three scalar identities about the
square-bracket coefficients `c(k,m,r) = [w^r](1+w)^{k−1}(log(1+w))^m`:

* **(I1)** `Σ_m d^m/m! · c(k,m,r) = C(k−1+d, r)` for every `d ∈ ℤ` — i.e. `e^{d·log(1+w)} = (1+w)^d`;
* **(I3)** `Σ_{m≥0} 2d^{2m+1}/(2m+1)! · c(k,2m+1,r) = C(k−1+d,r) − C(k−1−d,r)` — the odd part of (I1),
  which is what the geometric tails of the graded-trace telescopes produce;
* **(I2)** `c(k,−1,r) − C(k−1,r+1) − ½C(k−1,r) = −Σ_{m≥0} B_{2m+2}/(2m+2)! · c(k,2m+1,r)`
  — the constant term, i.e. `u = B(log(1+w))` with `B` the Bernoulli generating function.

All three rest on **`exp(log(1+w)) = 1+w`** for formal power series, proved here by an ODE
uniqueness argument: both `exp(c·log(1+X))` and the binomial series `Σ C(c,r) X^r` solve
`(1+X)·F′ = c·F` with `F(0) = 1`.

## Status
Proved, axiom-clean, `pbw`-free.
-/

namespace VOA

open scoped BigOperators
open PowerSeries

/-- The Euler-operator coefficient, for the `Derivation` form of the derivative. -/
theorem coeff_X_mul_derivative (f : PowerSeries ℂ) (k : ℕ) :
    coeff k (X * derivative ℂ f) = (k : ℂ) * coeff k f :=
  coeff_X_mul_derivativeFun f k

/-! ## ODE uniqueness for `(1+X)F′ = cF` -/

/-- **Uniqueness for the first-order ODE `(1+X)F′ = c·F`**: two solutions with the same
constant term agree.  Coefficientwise the ODE is `(r+1)F_{r+1} + rF_r = cF_r`, which determines
`F_{r+1}` from `F_r`. -/
theorem onePlusX_ode_unique (c : ℂ) (F G : PowerSeries ℂ)
    (hF : (1 + X) * derivative ℂ F = c • F)
    (hG : (1 + X) * derivative ℂ G = c • G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  set H := F - G with hHdef
  have hH : (1 + X) * derivative ℂ H = c • H := by
    rw [hHdef, map_sub, mul_sub, hF, hG, smul_sub]
  have hcoeff : ∀ n : ℕ, coeff n H = 0 := by
    intro n
    induction n with
    | zero =>
        rw [coeff_zero_eq_constantCoeff, hHdef, map_sub, h0, sub_self]
    | succ n ih =>
        have h := congrArg (coeff n) hH
        rw [add_mul, one_mul, map_add, coeff_derivative, coeff_X_mul_derivative, ih,
          map_smul, ih, smul_zero, mul_zero, add_zero] at h
        have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        exact (mul_eq_zero.mp h).resolve_right hn
  have : H = 0 := PowerSeries.ext (fun n => by rw [hcoeff n, map_zero])
  exact sub_eq_zero.mp this

/-! ## The binomial series `Σ_r C(n,r) Xʳ` -/

/-- The binomial series `(1+X)^n = Σ_r C(n,r) X^r` for `n : ℤ`, defined by its coefficients. -/
noncomputable def binomSeries (n : ℤ) : PowerSeries ℂ := PowerSeries.mk (fun r => cbz n r)

@[simp] theorem coeff_binomSeries (n : ℤ) (r : ℕ) : coeff r (binomSeries n) = cbz n r := by
  rw [binomSeries, coeff_mk]

/-- Absorption: `(r+1)·C(n,r+1) = n·C(n−1,r)`. -/
theorem cbz_succ_absorb (n : ℤ) (r : ℕ) :
    ((r : ℂ) + 1) * cbz n ((r : ℤ) + 1) = (n : ℂ) * cbz (n - 1) r := by
  rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) from by push_cast; ring,
    cbz_apply_nonneg _ (by positivity), cbz_apply_nonneg _ (by positivity),
    Int.toNat_natCast, Int.toNat_natCast]
  have hfac : ((r.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h1 := gBinom_mul_factorial n (r + 1)
  have h2 := gBinom_mul_factorial (n - 1) r
  rw [Finset.prod_range_succ'] at h1
  have hprod : (∏ i ∈ Finset.range r, ((n : ℂ) - ((i + 1 : ℕ) : ℂ)))
      = ∏ i ∈ Finset.range r, (((n - 1 : ℤ) : ℂ) - (i : ℂ)) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    push_cast; ring
  rw [hprod, ← h2, Nat.factorial_succ] at h1
  push_cast at h1
  refine mul_left_cancel₀ hfac ?_
  linear_combination h1

/-- The binomial series solves the ODE `(1+X)F′ = nF`. -/
theorem binomSeries_ode (n : ℤ) :
    (1 + X) * derivative ℂ (binomSeries n) = (n : ℂ) • binomSeries n := by
  refine PowerSeries.ext (fun r => ?_)
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_X_mul_derivative, map_smul,
    coeff_binomSeries, coeff_binomSeries, smul_eq_mul]
  have habs := cbz_succ_absorb n r
  have hpas := cbz_pascal n r
  have habs' : (r : ℂ) * cbz n r = (n : ℂ) * cbz (n - 1) ((r : ℤ) - 1) := by
    rcases r with _ | s
    · rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num, cbz_apply_neg (n - 1) (by norm_num)]
      simp
    · have := cbz_succ_absorb n s
      rw [show ((s + 1 : ℕ) : ℤ) - 1 = (s : ℤ) from by push_cast; ring]
      push_cast
      linear_combination this
  push_cast at habs ⊢
  linear_combination habs + habs' - (n : ℂ) * hpas

theorem constantCoeff_binomSeries (n : ℤ) : constantCoeff (binomSeries n) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_binomSeries]
  simp

/-- `(1+X)` solves the ODE with `c = 1`. -/
theorem onePlusX_ode : (1 + X : PowerSeries ℂ) * derivative ℂ (1 + X) = 1 + X := by
  rw [map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one]

/-- `(1+X)^n` for a natural `n` solves the ODE with `c = n`. -/
theorem onePlusX_pow_ode (n : ℕ) :
    (1 + X : PowerSeries ℂ) * derivative ℂ ((1 + X) ^ n) = (n : ℂ) • (1 + X) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1 := onePlusX_ode
      rw [smul_eq_C_mul] at ih ⊢
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      push_cast
      rw [map_add (PowerSeries.C (R := ℂ)), map_one]
      linear_combination (1 + X : PowerSeries ℂ) ^ m * h1 + (1 + X : PowerSeries ℂ) * ih

/-- `(1+X)^n` for a natural `n` is the binomial series (via the ODE). -/
theorem onePlusX_pow_eq_binomSeries (n : ℕ) :
    ((1 + X : PowerSeries ℂ) ^ n) = binomSeries n :=
  onePlusX_ode_unique (n : ℂ) _ _ (onePlusX_pow_ode n) (binomSeries_ode n)
    (by rw [constantCoeff_binomSeries, map_pow, map_add, map_one, constantCoeff_X, add_zero,
      one_pow])

/-! ## `exp(c·log(1+X))` and `exp ∘ log = id` -/

theorem hasSubst_log : HasSubst (log ℂ) := HasSubst.of_constantCoeff_zero' constantCoeff_log

theorem hasSubst_smul_log (c : ℂ) : HasSubst (c • log ℂ) := HasSubst.smul' c hasSubst_log

/-- Substituting a series with zero constant term preserves the constant term. -/
theorem constantCoeff_subst_of_constantCoeff_eq_zero {g : PowerSeries ℂ}
    (hg : constantCoeff g = 0) (f : PowerSeries ℂ) :
    constantCoeff (f.subst g) = constantCoeff f := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs,
    finsum_eq_single _ 0 (fun d hd => ?_)]
  · rw [pow_zero, coeff_zero_one, smul_eq_mul, mul_one, coeff_zero_eq_constantCoeff_apply]
  · rw [coeff_zero_eq_constantCoeff_apply, map_pow, hg, zero_pow hd, smul_zero]

/-- `Φ_c = exp(c·log(1+X))`. -/
noncomputable def expLog (c : ℂ) : PowerSeries ℂ := (exp ℂ).subst (c • log ℂ)

/-- `Φ_c` solves `(1+X)F′ = cF`. -/
theorem expLog_ode (c : ℂ) : (1 + X) * derivative ℂ (expLog c) = c • expLog c := by
  rw [expLog, derivative_subst ℂ (hasSubst_smul_log c), derivative_exp, Derivation.map_smul,
    derivative_log_eq_geoAltSeries, mul_smul_comm, mul_smul_comm, ← mul_assoc,
    mul_comm (1 + X : PowerSeries ℂ), mul_assoc, onePlusX_mul_geoAltSeries, mul_one]

theorem constantCoeff_expLog (c : ℂ) : constantCoeff (expLog c) = 1 := by
  rw [expLog, constantCoeff_subst_of_constantCoeff_eq_zero, constantCoeff_exp]
  rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_log, mul_zero]

/-- The product of two ODE solutions solves the ODE with the summed constant. -/
theorem onePlusX_ode_mul {a b : ℂ} {F G : PowerSeries ℂ}
    (hF : (1 + X) * derivative ℂ F = a • F) (hG : (1 + X) * derivative ℂ G = b • G) :
    (1 + X) * derivative ℂ (F * G) = (a + b) • (F * G) := by
  rw [smul_eq_C_mul] at hF hG ⊢
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add]
  linear_combination G * hF + F * hG

/-- **`Φ_a · Φ_b = Φ_{a+b}`.** -/
theorem expLog_mul (a b : ℂ) : expLog a * expLog b = expLog (a + b) :=
  onePlusX_ode_unique (a + b) _ _ (onePlusX_ode_mul (expLog_ode a) (expLog_ode b))
    (expLog_ode (a + b))
    (by rw [map_mul, constantCoeff_expLog, constantCoeff_expLog, constantCoeff_expLog, one_mul])

/-- **`exp(n·log(1+X)) = Σ_r C(n,r) X^r`** for every integer `n`. -/
theorem expLog_intCast_eq_binomSeries (n : ℤ) : expLog n = binomSeries n :=
  onePlusX_ode_unique n _ _ (expLog_ode n) (binomSeries_ode n)
    (by rw [constantCoeff_expLog, constantCoeff_binomSeries])

/-- **`exp(log(1+X)) = 1 + X`.** -/
theorem exp_subst_log : (exp ℂ).subst (log ℂ) = 1 + X := by
  have h := expLog_intCast_eq_binomSeries 1
  have h2 := onePlusX_pow_eq_binomSeries 1
  rw [pow_one, Nat.cast_one] at h2
  rw [expLog, Int.cast_one, one_smul] at h
  rw [h, ← h2]

/-- Substituting `X` is the identity. -/
theorem subst_X_self (f : PowerSeries ℂ) : f.subst X = f := by
  rw [← map_algebraMap_eq_subst_X, Algebra.algebraMap_self, PowerSeries.map_id]
  rfl

/-- The substitution `w ↦ log(1+w)` as an algebra endomorphism. -/
noncomputable def substLogHom : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom hasSubst_log

@[simp] theorem substLogHom_apply (f : PowerSeries ℂ) : substLogHom f = f.subst (log ℂ) :=
  congrFun (coe_substAlgHom hasSubst_log) f

/-- `(e^z − 1)` at `z = log(1+w)` is `w`. -/
theorem expMinusOne_subst_log : expMinusOne.subst (log ℂ) = X := by
  rw [expMinusOne, PowerSeries.subst_sub hasSubst_log, exp_subst_log,
    show ((1 : PowerSeries ℂ)).subst (log ℂ) = 1 from by
      rw [← substLogHom_apply]; exact map_one _]
  ring

/-- **`u = B(log(1+w))`**: `uSeries` is the Bernoulli generating function composed with `log`.
This is `subst_expMinusOne_uSeries` (`u(e^z−1) = B(z)`) read backwards through `exp ∘ log = id`. -/
theorem uSeries_eq_bernoulli_subst_log :
    uSeries = (bernoulliPowerSeries ℂ).subst (log ℂ) := by
  have h := congrArg (fun f : PowerSeries ℂ => f.subst (log ℂ)) subst_expMinusOne_uSeries
  simp only at h
  rw [subst_comp_subst_apply hasSubst_expMinusOne hasSubst_log, expMinusOne_subst_log,
    subst_X_self] at h
  exact h

/-! ## Coefficient extraction through a substitution -/

/-- `log(1+X)^n` has no coefficients below degree `n`. -/
theorem coeff_log_pow_eq_zero {j n : ℕ} (h : j < n) : coeff j ((log ℂ) ^ n) = 0 := by
  rw [← logOnePlusXSeries_eq_log, logOnePlusX_eq_X_mul_u, mul_pow, coeff_X_pow_mul', if_neg]
  omega

/-- **Coefficient extraction**: `[X^r](P · g(log(1+X))) = Σ_{n ≤ r} g_n · [X^r](P · log^n)`. -/
theorem coeff_mul_subst_log (P g : PowerSeries ℂ) (r : ℕ) :
    coeff r (P * g.subst (log ℂ))
      = ∑ n ∈ Finset.range (r + 1), coeff n g * coeff r (P * (log ℂ) ^ n) := by
  have hS : ∀ j ∈ Finset.range (r + 1), coeff j (g.subst (log ℂ))
      = ∑ n ∈ Finset.range (r + 1), coeff n g * coeff j ((log ℂ) ^ n) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [coeff_subst' hasSubst_log]
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (r + 1))]
    · exact Finset.sum_congr rfl (fun n _ => by rw [smul_eq_mul])
    · intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      push_neg at hc
      exact hn (by rw [coeff_log_pow_eq_zero (by omega), smul_zero])
  rw [coeff_mul]
  have h2 : ∀ p ∈ Finset.antidiagonal r, coeff p.1 P * coeff p.2 (g.subst (log ℂ))
      = ∑ n ∈ Finset.range (r + 1), coeff n g * (coeff p.1 P * coeff p.2 ((log ℂ) ^ n)) := by
    intro p hp
    rw [hS p.2 (by
      rw [Finset.mem_range]
      have := Finset.mem_antidiagonal.mp hp
      omega), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [coeff_mul, Finset.mul_sum]

/-- Coefficient extraction for `Φ_c = exp(c·log(1+X))`. -/
theorem coeff_mul_expLog (P : PowerSeries ℂ) (c : ℂ) (r : ℕ) :
    coeff r (P * expLog c)
      = ∑ n ∈ Finset.range (r + 1), (c ^ n / (n.factorial : ℂ)) * coeff r (P * (log ℂ) ^ n) := by
  have hexp : expLog c
      = PowerSeries.subst (log ℂ) (PowerSeries.subst (c • (X : PowerSeries ℂ)) (exp ℂ)) := by
    rw [expLog, PowerSeries.subst_comp_subst_apply (HasSubst.smul_X' c) hasSubst_log,
      PowerSeries.subst_smul hasSubst_log, PowerSeries.subst_X hasSubst_log]
  rw [hexp, coeff_mul_subst_log]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  rw [← rescale_eq_subst, coeff_rescale, coeff_exp, eq_ratCast]
  push_cast
  ring

/-! ## The three weight-matching identities -/

/-- `c(k,m,r)` for `k ≥ 1` as a coefficient of `(1+X)^{k−1}·log^m`. -/
theorem sqBracketCoeff_eq_coeff_pow {k : ℕ} (hk : 1 ≤ k) (m r : ℕ) :
    sqBracketCoeff k m r = coeff r ((1 + X : PowerSeries ℂ) ^ (k - 1) * (log ℂ) ^ m) := by
  rw [sqBracketCoeff, onePlusXUnit_zpow_of_one_le hk, logOnePlusXSeries_eq_log]

/-- **(I1)** `Σ_{m ≤ r} d^m/m! · c(k,m,r) = C(k−1+d, r)`, for every `d ∈ ℤ`. -/
theorem sum_pow_div_factorial_mul_sqBracketCoeff {k : ℕ} (hk : 1 ≤ k) (d : ℤ) (r : ℕ) :
    ∑ m ∈ Finset.range (r + 1), ((d : ℂ) ^ m / (m.factorial : ℂ)) * sqBracketCoeff k m r
      = cbz ((k : ℤ) - 1 + d) r := by
  simp_rw [sqBracketCoeff_eq_coeff_pow hk]
  rw [← coeff_mul_expLog, onePlusX_pow_eq_binomSeries, ← expLog_intCast_eq_binomSeries,
    expLog_mul]
  have hcast : ((((k - 1 : ℕ) : ℤ) : ℂ) + (d : ℂ)) = (((k : ℤ) - 1 + d : ℤ) : ℂ) := by
    push_cast [Nat.cast_sub hk]
    ring
  rw [hcast, expLog_intCast_eq_binomSeries, coeff_binomSeries]

/-- `c(k,m,r) = 0` for `m > r`. -/
theorem sqBracketCoeff_eq_zero_of_lt (k : ℕ) {m r : ℕ} (h : r < m) : sqBracketCoeff k m r = 0 := by
  rw [← sqBracketCoeffZ_of_nonneg, sqBracketCoeffZ_of_lt k (by exact_mod_cast h)]

/-- Reindexing an odd-indexed sum: `Σ_{n < 2N} [Odd n]·g(n) = Σ_{m < N} g(2m+1)`. -/
theorem sum_range_two_mul_odd (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), (if Odd n then g n else 0)
      = ∑ m ∈ Finset.range N, g (2 * m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ,
        if_neg (by rw [Nat.not_odd_iff_even]; exact even_two_mul N),
        if_pos (odd_two_mul_add_one N), add_zero]

/-- **Odd reindexing to a `finsum`**: for `f` vanishing above `r`,
`Σ_{n ≤ r} [Odd n]·f(n) = Σᶠ_m f(2m+1)`. -/
theorem sum_range_odd_eq_finsum (f : ℕ → ℂ) (r : ℕ) (hf : ∀ n, r < n → f n = 0) :
    ∑ n ∈ Finset.range (r + 1), (if Odd n then f n else 0) = ∑ᶠ m : ℕ, f (2 * m + 1) := by
  have h1 : ∑ n ∈ Finset.range (r + 1), (if Odd n then f n else 0)
      = ∑ n ∈ Finset.range (2 * (r + 1)), (if Odd n then f n else 0) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun n _ hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    rw [hf n (by omega), ite_self]
  rw [h1, sum_range_two_mul_odd, finsum_eq_sum_of_support_subset (s := Finset.range (r + 1))]
  intro m hm
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  exact hm (hf _ (by omega))

/-- **(I3)** `Σᶠ_m 2d^{2m+1}/(2m+1)! · c(k,2m+1,r) = C(k−1+d,r) − C(k−1−d,r)`, for `d ∈ ℤ`. -/
theorem finsum_odd_pow_mul_sqBracketCoeff {k : ℕ} (hk : 1 ≤ k) (d : ℤ) (r : ℕ) :
    ∑ᶠ m : ℕ, (2 * (d : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ))
        * sqBracketCoeff k (2 * m + 1) r
      = cbz ((k : ℤ) - 1 + d) r - cbz ((k : ℤ) - 1 - d) r := by
  rw [← sum_pow_div_factorial_mul_sqBracketCoeff hk d r,
    show ((k : ℤ) - 1 - d) = (k : ℤ) - 1 + (-d) from by ring,
    ← sum_pow_div_factorial_mul_sqBracketCoeff hk (-d) r, ← Finset.sum_sub_distrib,
    ← sum_range_odd_eq_finsum
      (fun n => (2 * (d : ℂ) ^ n / (n.factorial : ℂ)) * sqBracketCoeff k n r) r
      (fun n hn => by dsimp only; rw [sqBracketCoeff_eq_zero_of_lt k hn, mul_zero])]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hodd : Odd n
  · rw [if_pos hodd]
    push_cast
    rw [hodd.neg_pow]
    ring
  · rw [if_neg hodd]
    rw [Nat.not_odd_iff_even] at hodd
    push_cast
    rw [hodd.neg_pow]
    ring

/-- The tail of the Bernoulli generating function: `B(z) = 1 + z·B̃(z)`. -/
noncomputable def bernoulliTail : PowerSeries ℂ :=
  PowerSeries.mk (fun n => coeff (n + 1) (bernoulliPowerSeries ℂ))

theorem bernoulliPowerSeries_eq_one_add_X_mul_tail :
    bernoulliPowerSeries ℂ = 1 + X * bernoulliTail := by
  refine PowerSeries.ext (fun n => ?_)
  rcases n with _ | m
  · rw [coeff_zero_bernoulliPowerSeries, map_add, coeff_zero_X_mul, coeff_zero_one, add_zero]
  · rw [map_add, coeff_succ_X_mul, bernoulliTail, coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero m),
      zero_add]

/-- **`u⁻¹ = 1 − w·B̃(log(1+w))`**. -/
theorem uUnit_inv_eq : ((uUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
    = 1 - X * bernoulliTail.subst (log ℂ) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [uUnit_coe]
  have hu : uSeries = 1 + (log ℂ) * bernoulliTail.subst (log ℂ) := by
    rw [uSeries_eq_bernoulli_subst_log, bernoulliPowerSeries_eq_one_add_X_mul_tail,
      PowerSeries.subst_add hasSubst_log, PowerSeries.subst_mul hasSubst_log,
      PowerSeries.subst_X hasSubst_log,
      show ((1 : PowerSeries ℂ)).subst (log ℂ) = 1 from by
        rw [← substLogHom_apply]; exact map_one _]
  have hL : (log ℂ) = X * uSeries := by
    rw [← logOnePlusXSeries_eq_log, logOnePlusX_eq_X_mul_u]
  linear_combination hu + (bernoulliTail.subst (log ℂ)) * hL

/-- **(I2)** the constant-term identity:
`c(k,−1,r) − C(k−1,r+1) − ½C(k−1,r) = Σᶠ_m zhuG(m+1)(0) · c(k,2m+1,r)`. -/
theorem sqBracketCoeffZ_neg_one_eq {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    sqBracketCoeffZ k (-1) r - cbz ((k : ℤ) - 1) ((r : ℤ) + 1) - (1 / 2) * cbz ((k : ℤ) - 1) r
      = ∑ᶠ m : ℕ, zhuG (m + 1) 0 * sqBracketCoeff k (2 * m + 1) r := by
  have hc : sqBracketCoeffZ k (-1) r
      = coeff (r + 1) ((1 + X : PowerSeries ℂ) ^ (k - 1) * (1 - X * bernoulliTail.subst (log ℂ))) := by
    rw [sqBracketCoeffZ, if_pos (by omega), show ((r : ℤ) - (-1)).toNat = r + 1 from by omega,
      onePlusXUnit_zpow_of_one_le hk, zpow_neg_one, uUnit_inv_eq]
  rw [hc, mul_sub, mul_one, map_sub, onePlusX_pow_eq_binomSeries, coeff_binomSeries,
    ← onePlusX_pow_eq_binomSeries, ← mul_assoc, mul_comm _ X, mul_assoc, coeff_succ_X_mul,
    coeff_mul_subst_log]
  have hterm : ∀ n : ℕ, coeff n bernoulliTail * coeff r ((1 + X : PowerSeries ℂ) ^ (k - 1) * (log ℂ) ^ n)
      = (if n = 0 then -(1 / 2) * cbz ((k : ℤ) - 1) r else 0)
        + (if Odd n then -(zhuG (n / 2 + 1) 0 * sqBracketCoeff k n r) else 0) := by
    intro n
    rw [bernoulliTail, coeff_mk, coeff_bernoulliPowerSeries, ← sqBracketCoeff_eq_coeff_pow hk]
    rcases n with _ | n
    · rw [if_pos rfl, if_neg (by decide), add_zero, sqBracketCoeff_zero k r hk, bernoulli_one]
      have : cbz ((k : ℤ) - 1) r = ((k - 1).choose r : ℂ) := by
        rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) from by omega, cbz_apply_nonneg _ (by positivity),
          Int.toNat_natCast, gBinom_natCast]
      rw [this]
      push_cast
      ring
    · rw [if_neg (Nat.succ_ne_zero n), zero_add]
      by_cases hodd : Odd (n + 1)
      · rw [if_pos hodd]
        obtain ⟨j, hj⟩ := hodd
        have hn2 : (n + 1) / 2 = j := by omega
        rw [hn2, zhuG_zero, show 2 * (j + 1) = n + 1 + 1 from by omega]
        ring
      · rw [if_neg hodd, Nat.not_odd_iff_even] at *
        rw [bernoulli_eq_zero_of_odd (by rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact hodd)
          (by omega)]
        simp
  rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (r + 1)) 0, if_pos (Finset.mem_range.mpr (Nat.succ_pos r)),
    sum_range_odd_eq_finsum (fun n => -(zhuG (n / 2 + 1) 0 * sqBracketCoeff k n r)) r
      (fun n hn => by dsimp only; rw [sqBracketCoeff_eq_zero_of_lt k hn, mul_zero, neg_zero])]
  simp only [show ∀ m : ℕ, (2 * m + 1) / 2 = m from fun m => by omega]
  rw [finsum_neg_distrib, show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]
  push_cast
  ring

end VOA

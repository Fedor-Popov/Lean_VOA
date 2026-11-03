/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Newton exponentials and the twisted contraction factor  (Moonshine step M6c, algebra layer)

The twisted vertex operator of `e^α` (FLM ch. 9) is built from exponentials
`exp(Σ_{k ≥ 1} (d_k / k) w^k)` of half-integer moded oscillators, written in the doubled
variable `w = z^{1/2}`.  This file develops the purely algebraic part, over an arbitrary
commutative `ℂ`-algebra `R`.

* `nexp d` — the coefficients of `exp(Σ_{k≥1} (d_k/k) w^k)`, by the Newton recursion
  `(p+1) E_{p+1} = Σ_{k ≤ p} d_{k+1} E_{p-k}` (`nexp_rec`).
* The Euler operator `theta = w d/dw` on `R⟦X⟧` (`theta_mul`: Leibniz), and the characterization
  `theta F = D(d) · F`, `F₀ = 1 ⇒ F = Σ nexp d p Xᵖ` (`eq_nexpPS`).
* Consequences: `nexpPS_add` (`exp(a+b) = exp a · exp b`), `nexp_map` (algebra maps),
  `nexp_scale` (`d_k ↦ tᵏ d_k` scales `E_p` by `tᵖ`), `nexp_derivation` (a derivation hitting a
  single `d_K` by a constant).
* **The twisted contraction factor.**  `fco n = nexp (−2n·[k odd])`, the coefficients of
  `((1 − x)/(1 + x))ⁿ`, which governs `E⁺(−α, w₁) E⁻(−β, w₂)` reordering with `n = ⟨α, β⟩`.
  `fco_mul_one_sub_sq_pow`: for `|n| ≤ N`,
  `((1 − x)/(1 + x))ⁿ (1 − x²)ᴺ = (1 − x)^{N+n} (1 + x)^{N−n}`, a polynomial of degree `2N`
  which is palindromic up to the sign `(−1)^{N+n}` (`gco_palindrome`).  This is the identity behind
  the locality `(z₁ − z₂)ᴺ [Y^T(e^α, z₁), Y^T(e^β, z₂)] = 0` with `N = |⟨α, β⟩|`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open PowerSeries
open scoped BigOperators

section Exp

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-! ## The Newton exponential -/

/-- **The Newton exponential**: `nexp d p` is the coefficient of `wᵖ` in
`exp(Σ_{k ≥ 1} (d_k / k) wᵏ)` (`d 0` is ignored). -/
noncomputable def nexp (d : ℕ → R) : ℕ → R
  | 0 => 1
  | (p + 1) => ((p + 1 : ℂ))⁻¹ • ∑ k ∈ Finset.range (p + 1), d (k + 1) * nexp d (p - k)

@[simp] theorem nexp_zero (d : ℕ → R) : nexp d 0 = 1 := by simp only [nexp]

theorem nexp_succ (d : ℕ → R) (p : ℕ) :
    nexp d (p + 1)
      = ((p + 1 : ℂ))⁻¹ • ∑ k ∈ Finset.range (p + 1), d (k + 1) * nexp d (p - k) := by
  simp only [nexp]

/-- The Newton recursion. -/
theorem nexp_rec (d : ℕ → R) (p : ℕ) :
    ((p + 1 : ℂ)) • nexp d (p + 1) = ∑ k ∈ Finset.range (p + 1), d (k + 1) * nexp d (p - k) := by
  rw [nexp_succ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero p), one_smul]

/-! ## The Euler operator on power series -/

/-- The Euler operator `θ = w d/dw` on `R⟦X⟧`. -/
noncomputable def theta (F : R⟦X⟧) : R⟦X⟧ := PowerSeries.mk fun p => (p : ℂ) • coeff p F

@[simp] theorem coeff_theta (F : R⟦X⟧) (p : ℕ) : coeff p (theta F) = (p : ℂ) • coeff p F := by
  rw [theta, coeff_mk]

theorem theta_add (F G : R⟦X⟧) : theta (F + G) = theta F + theta G := by
  ext p; simp [smul_add]

theorem theta_sub (F G : R⟦X⟧) : theta (F - G) = theta F - theta G := by
  ext p; simp [smul_sub]

/-- **Leibniz rule** for `θ`. -/
theorem theta_mul (F G : R⟦X⟧) : theta (F * G) = theta F * G + F * theta G := by
  ext p
  rw [coeff_theta, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [coeff_theta, coeff_theta, smul_mul_assoc, mul_smul_comm, ← add_smul, ← hij]
  push_cast
  rfl

/-- The logarithmic-derivative series `D(d) = Σ_{k ≥ 1} d_k Xᵏ`. -/
noncomputable def Dser (d : ℕ → R) : R⟦X⟧ := PowerSeries.mk fun k => if k = 0 then 0 else d k

@[simp] theorem coeff_Dser (d : ℕ → R) (k : ℕ) :
    coeff k (Dser d) = if k = 0 then 0 else d k := by rw [Dser, coeff_mk]

theorem Dser_add (d e : ℕ → R) : Dser (d + e) = Dser d + Dser e := by
  ext k; simp only [coeff_Dser, Pi.add_apply, map_add]; split_ifs <;> simp

/-- The Newton exponential as a power series. -/
noncomputable def nexpPS (d : ℕ → R) : R⟦X⟧ := PowerSeries.mk (nexp d)

@[simp] theorem coeff_nexpPS (d : ℕ → R) (p : ℕ) : coeff p (nexpPS d) = nexp d p := by
  rw [nexpPS, coeff_mk]

theorem coeff_Dser_mul_succ (d : ℕ → R) (F : R⟦X⟧) (p : ℕ) :
    coeff (p + 1) (Dser d * F) = ∑ k ∈ Finset.range (p + 1), d (k + 1) * coeff (p - k) F := by
  rw [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (Dser d) * coeff j F),
    Finset.sum_range_succ']
  simp only [coeff_Dser, if_true, zero_mul, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    if_false]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show p + 1 - (k + 1) = p - k by omega]

theorem coeff_Dser_mul_zero (d : ℕ → R) (F : R⟦X⟧) : coeff 0 (Dser d * F) = 0 := by
  rw [coeff_mul]; simp

/-- The Newton exponential solves `θ E = D(d) · E`. -/
theorem theta_nexpPS (d : ℕ → R) : theta (nexpPS d) = Dser d * nexpPS d := by
  ext p
  rcases p with _ | p
  · rw [coeff_theta, coeff_Dser_mul_zero]; simp
  · rw [coeff_theta, coeff_Dser_mul_succ, coeff_nexpPS]
    push_cast
    rw [nexp_rec]
    simp

/-- **Uniqueness**: `θ Z = D(d) · Z` with `Z₀ = 0` forces `Z = 0`. -/
theorem eq_zero_of_theta (d : ℕ → R) (Z : R⟦X⟧) (h : theta Z = Dser d * Z) (h0 : coeff 0 Z = 0) :
    Z = 0 := by
  ext p
  rw [map_zero]
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases p with _ | p
    · exact h0
    · have hp := congrArg (coeff (p + 1)) h
      rw [coeff_theta, coeff_Dser_mul_succ, Finset.sum_eq_zero (fun k hk => by
        rw [ih (p - k) (by omega), mul_zero])] at hp
      have hne : ((p + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
      exact (smul_eq_zero.mp hp).resolve_left hne

/-- **Characterization of the Newton exponential**. -/
theorem eq_nexpPS (d : ℕ → R) (F : R⟦X⟧) (h : theta F = Dser d * F) (h0 : coeff 0 F = 1) :
    F = nexpPS d := by
  have := eq_zero_of_theta d (F - nexpPS d)
    (by rw [theta_sub, h, theta_nexpPS, mul_sub])
    (by rw [map_sub, h0, coeff_nexpPS, nexp_zero, sub_self])
  exact sub_eq_zero.mp this

theorem nexpPS_zero : nexpPS (0 : ℕ → R) = 1 := by
  refine (eq_nexpPS 0 1 ?_ ?_).symm
  · ext p; rcases p with _ | p <;> simp [coeff_one]
  · simp

/-- `exp(a + b) = exp a · exp b`. -/
theorem nexpPS_add (d e : ℕ → R) : nexpPS (d + e) = nexpPS d * nexpPS e := by
  refine (eq_nexpPS (d + e) _ ?_ ?_).symm
  · rw [theta_mul, theta_nexpPS, theta_nexpPS, Dser_add]; ring
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply]
    simp

theorem nexpPS_natCast_smul (m : ℕ) (d : ℕ → R) :
    nexpPS ((m : ℂ) • d) = nexpPS d ^ m := by
  induction m with
  | zero => simp only [Nat.cast_zero, zero_smul, pow_zero]; exact nexpPS_zero
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, nexpPS_add, ih, pow_succ]

/-- Coefficientwise action of an algebra map commutes with `nexp`. -/
theorem nexp_map {S : Type*} [CommRing S] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) (d : ℕ → R) (p : ℕ) :
    φ (nexp d p) = nexp (fun k => φ (d k)) p := by
  have h := eq_nexpPS (fun k => φ (d k)) (PowerSeries.map φ.toRingHom (nexpPS d)) ?_ ?_
  · have := congrArg (coeff p) h
    rw [coeff_map, coeff_nexpPS, coeff_nexpPS] at this
    exact this
  · ext q
    rw [coeff_theta, coeff_map]
    rcases q with _ | q
    · simp [coeff_Dser_mul_zero]
    · rw [coeff_Dser_mul_succ, coeff_nexpPS]
      simp only [coeff_map, coeff_nexpPS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← map_smul, show ((q + 1 : ℕ) : ℂ) = (q : ℂ) + 1 by push_cast; ring, nexp_rec, map_sum]
      simp
  · simp

/-- Scaling: `d_k ↦ tᵏ d_k` multiplies `E_p` by `tᵖ`. -/
theorem nexp_scale (t : R) (d : ℕ → R) (p : ℕ) :
    nexp (fun k => t ^ k * d k) p = t ^ p * nexp d p := by
  have h := eq_nexpPS (fun k => t ^ k * d k) (rescale t (nexpPS d)) ?_ ?_
  · have := congrArg (coeff p) h
    rw [coeff_rescale, coeff_nexpPS, coeff_nexpPS] at this
    exact this.symm
  · have hD : Dser (fun k => t ^ k * d k) = rescale t (Dser d) := by
      ext k; rw [coeff_rescale, coeff_Dser, coeff_Dser]; split_ifs <;> simp
    rw [hD, ← map_mul, ← theta_nexpPS]
    ext q
    rw [coeff_theta, coeff_rescale, coeff_rescale, coeff_theta, mul_smul_comm]
  · rw [coeff_rescale, coeff_nexpPS]; simp

/-! ## Derivations -/

/-- Coefficientwise application of a derivation. -/
noncomputable def dmap (δ : Derivation ℂ R R) (F : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk fun p => δ (coeff p F)

@[simp] theorem coeff_dmap (δ : Derivation ℂ R R) (F : R⟦X⟧) (p : ℕ) :
    coeff p (dmap δ F) = δ (coeff p F) := by rw [dmap, coeff_mk]

theorem dmap_mul (δ : Derivation ℂ R R) (F G : R⟦X⟧) :
    dmap δ (F * G) = dmap δ F * G + F * dmap δ G := by
  ext p
  rw [coeff_dmap, coeff_mul, map_sum, map_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Derivation.leibniz, coeff_dmap, coeff_dmap, smul_eq_mul, smul_eq_mul]
  ring

theorem dmap_theta (δ : Derivation ℂ R R) (F : R⟦X⟧) : dmap δ (theta F) = theta (dmap δ F) := by
  ext p; simp

theorem dmap_sub (δ : Derivation ℂ R R) (F G : R⟦X⟧) : dmap δ (F - G) = dmap δ F - dmap δ G := by
  ext p; simp

/-- **A derivation hitting one logarithmic coefficient.**  If `δ d_k = δ_{k,K} · K · c` with
`K ≥ 1`, then `δ E_p = c · E_{p−K}` (and `0` for `p < K`). -/
theorem nexp_derivation (δ : Derivation ℂ R R) (d : ℕ → R) (K : ℕ) (hK : 0 < K) (c : R)
    (hd : ∀ k, δ (d k) = if k = K then (K : ℂ) • c else 0) (p : ℕ) :
    δ (nexp d p) = if K ≤ p then c * nexp d (p - K) else 0 := by
  set Kser : R⟦X⟧ := PowerSeries.C c * X ^ K with hKs
  have hcK : ∀ k, coeff k Kser = if k = K then c else 0 := by
    intro k; rw [hKs, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
  have hY : dmap δ (nexpPS d) = Kser * nexpPS d := by
    have hdD : dmap δ (Dser d) = theta Kser := by
      ext k
      rw [coeff_dmap, coeff_Dser, coeff_theta, hcK]
      split_ifs with h1 h2 h2
      · subst h1; omega
      · simp
      · subst h2; rw [hd, if_pos rfl]
      · rw [hd, if_neg h2, smul_zero]
    refine sub_eq_zero.mp (eq_zero_of_theta d _ ?_ ?_)
    · rw [theta_sub, ← dmap_theta, theta_nexpPS, dmap_mul, hdD, theta_mul Kser (nexpPS d),
        theta_nexpPS]
      ring
    · rw [map_sub, coeff_dmap, coeff_nexpPS, nexp_zero, Derivation.map_one_eq_zero, coeff_mul]
      simp only [hcK, Finset.antidiagonal_zero, Finset.sum_singleton]
      rw [if_neg (Ne.symm hK.ne'), zero_mul, sub_zero]
  have := congrArg (coeff p) hY
  rw [coeff_dmap, coeff_nexpPS, hKs, mul_assoc, coeff_C_mul, coeff_X_pow_mul'] at this
  rw [this]
  split_ifs <;> simp

end Exp

/-! ## The twisted contraction factor `((1 − x)/(1 + x))ⁿ` -/

section Binomial

/-- Logarithmic coefficients of `1 − x`: `w d/dw log(1 − x) = −Σ xᵏ`. -/
def cOne : ℕ → ℂ := fun _ => -1

/-- Logarithmic coefficients of `1 + x`: `w d/dw log(1 + x) = Σ (−1)^{k+1} xᵏ`. -/
def cTwo : ℕ → ℂ := fun k => (-1) ^ (k + 1)

theorem nexpPS_cOne : nexpPS cOne = 1 - X := by
  refine (eq_nexpPS cOne (1 - X) ?_ ?_).symm
  · have hD : Dser cOne = 1 - PowerSeries.mk 1 := by
      ext k; rw [coeff_Dser, map_sub, coeff_one, coeff_mk]; split_ifs <;> simp [cOne]
    rw [hD, sub_mul, one_mul, mk_one_mul_one_sub_eq_one]
    ext p; rcases p with _ | _ | p <;> simp [coeff_one, coeff_X]
  · simp

theorem nexpPS_cTwo : nexpPS cTwo = 1 + X := by
  have h : cTwo = fun k => (-1 : ℂ) ^ k * cOne k := by
    funext k; simp [cTwo, cOne, pow_succ]
  ext p
  rw [coeff_nexpPS, h, nexp_scale, ← coeff_nexpPS, nexpPS_cOne]
  rcases p with _ | _ | p <;> simp [coeff_one, coeff_X]

/-- The odd indicator `[k odd]`. -/
def oddc : ℕ → ℂ := fun k => if k % 2 = 1 then 1 else 0

/-- **The twisted contraction factor**: `fco n p` is the coefficient of `xᵖ` in
`((1 − x)/(1 + x))ⁿ = exp(−2n Σ_{k odd} xᵏ/k)`. -/
noncomputable def fco (n : ℂ) : ℕ → ℂ := nexp ((-2 * n) • oddc)

theorem fco_zero (n : ℂ) : fco n 0 = 1 := nexp_zero _

theorem oddc_smul_eq (n : ℂ) : (-2 * n) • oddc = n • cOne - n • cTwo := by
  funext k
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, oddc, cOne, cTwo]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_neg (by omega), pow_succ, Even.neg_one_pow ⟨m, rfl⟩]; ring
  · rw [if_pos (by omega), pow_succ, Odd.neg_one_pow ⟨m, rfl⟩]; ring

/-- The polynomial `(1 − x)ᵃ (1 + x)ᵇ`. -/
noncomputable def gpoly (a b : ℕ) : Polynomial ℂ := (1 - Polynomial.X) ^ a * (1 + Polynomial.X) ^ b

theorem coe_gpoly (a b : ℕ) : ((gpoly a b : Polynomial ℂ) : ℂ⟦X⟧) = (1 - X) ^ a * (1 + X) ^ b := by
  simp [gpoly]

/-- `((1 − x)/(1 + x))ⁿ (1 − x²)ᴺ = (1 − x)^{N+n} (1 + x)^{N−n}` for `|n| ≤ N`. -/
theorem fco_mul_one_sub_sq_pow (N : ℕ) (n : ℤ) (h1 : -(N : ℤ) ≤ n) (h2 : n ≤ N) :
    nexpPS ((-2 * (n : ℂ)) • oddc) * (1 - X ^ 2) ^ N
      = ((gpoly (N + n).toNat (N - n).toNat : Polynomial ℂ) : ℂ⟦X⟧) := by
  have hsq : (1 - X ^ 2 : ℂ⟦X⟧) ^ N = nexpPS ((N : ℂ) • cOne + (N : ℂ) • cTwo) := by
    rw [nexpPS_add, nexpPS_natCast_smul, nexpPS_natCast_smul, nexpPS_cOne, nexpPS_cTwo, ← mul_pow]
    ring
  have ha : (((N + n).toNat : ℕ) : ℂ) = (N : ℂ) + n := by
    have : (((N + n).toNat : ℕ) : ℤ) = N + n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hb : (((N - n).toNat : ℕ) : ℂ) = (N : ℂ) - n := by
    have : (((N - n).toNat : ℕ) : ℤ) = N - n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hsq, ← nexpPS_add, coe_gpoly, ← nexpPS_cOne, ← nexpPS_cTwo, ← nexpPS_natCast_smul,
    ← nexpPS_natCast_smul, ← nexpPS_add, oddc_smul_eq, ha, hb]
  congr 1
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem natDegree_gpoly_le (a b : ℕ) : (gpoly a b).natDegree ≤ a + b := by
  rw [gpoly]
  refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ ?_)
  · refine (Polynomial.natDegree_pow_le).trans ?_
    have : (1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_; simp
    nlinarith
  · refine (Polynomial.natDegree_pow_le).trans ?_
    have : (1 + Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_; simp
    nlinarith

theorem reflect_pow_le_one (p : Polynomial ℂ) (hp : p.natDegree ≤ 1) (m : ℕ) :
    Polynomial.reflect m (p ^ m) = Polynomial.reflect 1 p ^ m := by
  induction m with
  | zero => simp [Polynomial.reflect_one]
  | succ m ih =>
    rw [pow_succ,
      Polynomial.reflect_mul _ _ ((Polynomial.natDegree_pow_le).trans (by nlinarith)) hp,
      ih, pow_succ]

/-- **Palindromy** of `(1 − x)ᵃ (1 + x)ᵇ`: reflecting at degree `a + b` multiplies by `(−1)ᵃ`. -/
theorem reflect_gpoly (a b : ℕ) :
    Polynomial.reflect (a + b) (gpoly a b) = (-1 : ℂ) ^ a • gpoly a b := by
  have h1 : (1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_; simp
  have h2 : (1 + Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_; simp
  have r1 : Polynomial.reflect 1 (1 - Polynomial.X : Polynomial ℂ) = Polynomial.X - 1 := by
    rw [Polynomial.reflect_sub, Polynomial.reflect_one, ← pow_one (Polynomial.X : Polynomial ℂ),
      Polynomial.reflect_monomial, Polynomial.revAt_le le_rfl]
    simp
  have r2 : Polynomial.reflect 1 (1 + Polynomial.X : Polynomial ℂ) = Polynomial.X + 1 := by
    rw [Polynomial.reflect_add, Polynomial.reflect_one, ← pow_one (Polynomial.X : Polynomial ℂ),
      Polynomial.reflect_monomial, Polynomial.revAt_le le_rfl]
    simp
  rw [gpoly, Polynomial.reflect_mul _ _ ((Polynomial.natDegree_pow_le).trans (by nlinarith))
    ((Polynomial.natDegree_pow_le).trans (by nlinarith)), reflect_pow_le_one _ h1,
    reflect_pow_le_one _ h2, r1, r2, Polynomial.smul_eq_C_mul,
    show (Polynomial.X - 1 : Polynomial ℂ) = Polynomial.C (-1) * (1 - Polynomial.X) by
      simp, mul_pow, ← Polynomial.C_pow]
  ring

theorem coeff_gpoly_reflect (a b t : ℕ) (ht : t ≤ a + b) :
    (gpoly a b).coeff (a + b - t) = (-1 : ℂ) ^ a * (gpoly a b).coeff t := by
  have := congrArg (fun p => Polynomial.coeff p t) (reflect_gpoly a b)
  simp only [Polynomial.coeff_reflect, Polynomial.revAt_le ht, Polynomial.coeff_smul,
    smul_eq_mul] at this
  exact this

/-- `fco` extended by zero to `ℤ`. -/
noncomputable def fz (n : ℂ) (t : ℤ) : ℂ := if 0 ≤ t then fco n t.toNat else 0

/-- The `ℤ`-indexed coefficients of `(1 − x)ᵃ (1 + x)ᵇ`. -/
noncomputable def gz (a b : ℕ) (t : ℤ) : ℂ := if 0 ≤ t then (gpoly a b).coeff t.toNat else 0

theorem gz_palindrome (a b : ℕ) (t : ℤ) :
    gz a b ((a + b : ℕ) - t) = (-1 : ℂ) ^ a * gz a b t := by
  unfold gz
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ (a + b : ℕ)
    · rw [if_pos (by omega), if_pos h0]
      have := coeff_gpoly_reflect a b t.toNat (by omega)
      rw [show (((a + b : ℕ) : ℤ) - t).toNat = a + b - t.toNat by omega, this]
    · rw [if_neg (by omega), if_pos h0,
        Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_gpoly_le a b).trans_lt (by omega)),
        mul_zero]
  · rw [if_neg h0, mul_zero, if_pos (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_gpoly_le a b).trans_lt (by omega))]

/-- The binomial convolution of the `P`-side of the locality computation equals `gz`. -/
theorem sum_binom_fz_eq_gz (N : ℕ) (n : ℤ) (h1 : -(N : ℤ) ≤ n) (h2 : n ≤ N) (t : ℤ) :
    ∑ r ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - r) * (N.choose r : ℂ)) * fz n (t - 2 * (N - r : ℕ))
      = gz (N + n).toNat (N - n).toNat t := by
  have hG := congrArg (coeff t.toNat) (fco_mul_one_sub_sq_pow N n h1 h2)
  rw [Polynomial.coeff_coe] at hG
  rw [← Finset.sum_range_reflect]
  have hpow : (1 - X ^ 2 : ℂ⟦X⟧) ^ N
      = ∑ m ∈ Finset.range (N + 1),
          PowerSeries.C ((-1 : ℂ) ^ m * (N.choose m : ℂ)) * X ^ (2 * m) := by
    rw [sub_eq_neg_add, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, neg_pow, ← pow_mul, map_mul, map_pow, map_neg, map_one]
    simp only [map_natCast]
    ring
  rw [hpow, Finset.mul_sum, map_sum] at hG
  unfold gz
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, ← hG]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← mul_assoc, coeff_mul_X_pow', show N + 1 - 1 - m = N - m by omega,
      show N - (N - m) = m by omega, Nat.choose_symm (by omega : m ≤ N)]
    unfold fz
    split_ifs with h3 h4 h4
    · rw [coeff_mul_C, coeff_nexpPS]
      unfold fco
      rw [show (t - 2 * ((m : ℕ) : ℤ)).toNat = t.toNat - 2 * m by omega]
      ring
    · omega
    · omega
    · simp
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun m _ => ?_
    unfold fz
    rw [if_neg (by omega), mul_zero]

/-- **The palindromic cancellation** behind twisted lattice locality: for `|n| ≤ N` the
`P`-side and `Q`-side binomial convolutions of the contraction factor agree up to `(−1)ⁿ`. -/
theorem sum_binom_fz_symm (N : ℕ) (n : ℤ) (h1 : -(N : ℤ) ≤ n) (h2 : n ≤ N) (t : ℤ) :
    ∑ r ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - r) * (N.choose r : ℂ)) * fz n (t - 2 * (N - r : ℕ))
      = (-1 : ℂ) ^ n.natAbs *
        ∑ r ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - r) * (N.choose r : ℂ)) *
          fz n (2 * (N - r : ℕ) - t) := by
  rw [sum_binom_fz_eq_gz N n h1 h2]
  -- the `Q`-side, reflected, is the `P`-side at `2N - t`
  have hQ : ∑ r ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - r) * (N.choose r : ℂ)) *
        fz n (2 * (N - r : ℕ) - t)
      = (-1 : ℂ) ^ N * gz (N + n).toNat (N - n).toNat (2 * N - t) := by
    rw [← sum_binom_fz_eq_gz N n h1 h2, Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [show N + 1 - 1 - r = N - r by omega, show N - (N - r) = r by omega,
      Nat.choose_symm_of_eq_add (by omega : N = (N - r) + r)]
    rw [show (2 : ℤ) * (N : ℤ) - t - 2 * ((N - r : ℕ) : ℤ) = 2 * ((r : ℕ) : ℤ) - t by omega]
    have : (-1 : ℂ) ^ r = (-1) ^ N * (-1) ^ (N - r) := by
      rw [← pow_add]
      rcases Nat.even_or_odd r with hr' | hr' <;> rcases Nat.even_or_odd (N + (N - r)) with hs | hs
      · rw [hr'.neg_one_pow, hs.neg_one_pow]
      · exfalso; obtain ⟨a, ha⟩ := hr'; obtain ⟨b, hb⟩ := hs; omega
      · exfalso; obtain ⟨a, ha⟩ := hr'; obtain ⟨b, hb⟩ := hs; omega
      · rw [hr'.neg_one_pow, hs.neg_one_pow]
    rw [this]; ring
  rw [hQ]
  have hsum : ((N + n).toNat + (N - n).toNat : ℕ) = 2 * N := by omega
  have hpal := gz_palindrome (N + n).toNat (N - n).toNat t
  rw [hsum] at hpal
  push_cast at hpal
  rw [hpal, ← mul_assoc, ← mul_assoc]
  have hsign : (-1 : ℂ) ^ n.natAbs * (-1) ^ N * (-1) ^ (N + n).toNat = 1 := by
    rw [← pow_add, ← pow_add]
    exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  rw [hsign, one_mul]

end Binomial

end VOA.Moonshine.LatticeTwisted

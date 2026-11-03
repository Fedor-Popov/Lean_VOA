/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.IndicialGrowth
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Frobenius theory with logarithms: formal solutions (formal part)

A Fuchsian equation at `y = 0`,

  `θ^s F + Σ_{i<s} cᵢ(y) θ^i F = 0`,   `θ = y d/dy`,  `cᵢ ∈ ℂ⟦y⟧`,

has in general solutions with **logarithms**: `F = y^λ Σ_n yⁿ pₙ(log y)` with `pₙ ∈ ℂ[ℓ]`.  This
file is the formal half of the Frobenius–Fuchs theory *with logarithms*, which associativity
of intertwining operators needs to expand a product of intertwiners at the iterate point `z₀/z₂ = 0`
before the logarithms are shown to
vanish.  VOA equations are *always* resonant (exponents from one intermediate module differ by
integers), so the non-resonant theory is not enough.

## The method: one surjectivity lemma handles every resonance

Since `θ(y^{λ+n} ℓ^k) = (λ+n) y^{λ+n} ℓ^k + k y^{λ+n} ℓ^{k−1}` (`ℓ = log y`), on the coefficient
`pₙ ∈ ℂ[ℓ]` of `y^{λ+n}` the operator `θ` acts as `λ + n + D`, `D = d/dℓ`.  Writing `T(D)` for
`aeval D T` (`dOp T`), the `y^{λ+n}`-coefficient of the equation is

  `P_n(D) pₙ + Σ_{m<n} Σ_{i<s} c_{i,n−m} (X + λ + m)^i(D) pₘ = 0`,

with `P_n = (X + λ + n)^s + Σ_{i<s} c_{i,0} (X + λ + n)^i` (`indPoly`; its constant term is the
indicial polynomial at `λ + n`).  **`T(D)` is surjective on `ℂ[ℓ]` for every `T ≠ 0`**
(`dOp_surjective`): factor `T = X^μ U` with `U(0) ≠ 0`; `D^μ` is surjective (antiderivatives), and
`U(D)` is invertible because `U` is invertible modulo `X^{d+1}` (`IsCoprime`), while `D^{d+1}`
kills polynomials of degree `≤ d`.  So the recursion can always be solved — at a resonance
(`P_n(0) = 0` with multiplicity `μ`) the `ℓ`-degree simply rises — and no Jordan form, shearing
or case distinction is needed.

## Main results

* `dOp`, `dOp_mul`, `natDegree_dOp_le` (`T(D)` never raises the degree),
  `derivative_surjective`, `dOp_surjective_of_coeff_zero_ne` / `natDegree_le_of_coeff_zero_ne`
  (`U(D)` invertible, degree-preserving, when `U(0) ≠ 0`), `dOp_surjective` (`T ≠ 0`).
* `thetaL`, `psMul`, `LogFuchsianEq` (the equation on log-series `p : ℕ → ℂ[ℓ]`),
  `thetaL_iterate`, `indPoly`, `indPoly_monic`, `coeff_zero_indPoly`,
  `logFuchsianEq_iff` (the coefficient recursion).
* `exists_logFuchsianEq`: for every `n₀` and every `r ∈ ker P_{n₀}(D)` there is a formal
  log-solution with `pₘ = 0` for `m < n₀` and `p_{n₀} = r` (for every resonance pattern).
* `exists_natDegree_bound`: every formal log-solution has bounded `ℓ`-degree (beyond the last
  root of the indicial polynomial on `λ + ℕ` the degree cannot grow).

Convergence of these solutions is `Huang/FrobeniusLogConv.lean`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.FrobeniusLog

open Polynomial
open scoped BigOperators

/-! ## Polynomials in `D = d/dℓ` acting on `ℂ[ℓ]` -/

/-- `T(D)`: the polynomial `T` evaluated at the derivation `D = d/dℓ` of `ℂ[ℓ]`. -/
noncomputable def dOp (T : ℂ[X]) : Module.End ℂ ℂ[X] :=
  aeval (derivative : Module.End ℂ ℂ[X]) T

theorem dOp_mul (S T : ℂ[X]) : dOp (S * T) = dOp S * dOp T := map_mul _ _ _

theorem dOp_add (S T : ℂ[X]) : dOp (S + T) = dOp S + dOp T := map_add _ _ _

theorem dOp_one : dOp 1 = 1 := map_one _

theorem dOp_C_mul (a : ℂ) (T : ℂ[X]) (q : ℂ[X]) :
    dOp (Polynomial.C a * T) q = a • dOp T q := by
  rw [dOp_mul, Module.End.mul_apply]
  simp [dOp, Module.algebraMap_end_eq_smul_id]

theorem dOp_sum_apply {ι : Type*} (S : Finset ι) (T : ι → ℂ[X]) (q : ℂ[X]) :
    dOp (∑ i ∈ S, T i) q = ∑ i ∈ S, dOp (T i) q := by
  rw [dOp, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  rfl

theorem dOp_X_pow_apply (k : ℕ) (q : ℂ[X]) : dOp (X ^ k) q = derivative^[k] q := by
  rw [dOp, map_pow, aeval_X, Module.End.pow_apply]

theorem dOp_apply_comm (S T q : ℂ[X]) : dOp S (dOp T q) = dOp T (dOp S q) := by
  rw [← Module.End.mul_apply, ← dOp_mul, mul_comm, dOp_mul, Module.End.mul_apply]

/-- `T(D)` as an explicit finite sum of iterated derivatives. -/
theorem dOp_apply_eq_sum (T q : ℂ[X]) :
    dOp T q = ∑ i ∈ Finset.range (T.natDegree + 1), T.coeff i • derivative^[i] q := by
  rw [dOp, aeval_eq_sum_range, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Module.End.pow_apply]

/-- `T(D)` never raises the degree. -/
theorem natDegree_dOp_le (T q : ℂ[X]) : (dOp T q).natDegree ≤ q.natDegree := by
  rw [dOp_apply_eq_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (natDegree_smul_le _ _) ?_
  exact le_trans (natDegree_iterate_derivative q i) (Nat.sub_le _ _)

/-- `D = d/dℓ` is surjective on `ℂ[ℓ]` (antiderivatives). -/
theorem derivative_surjective : Function.Surjective (derivative : ℂ[X] → ℂ[X]) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, by simp⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / ((n : ℂ) + 1)), ?_⟩
    rw [derivative_monomial]
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    congr 1
    field_simp

/-- `U` is invertible modulo `X^{d+1}` when `U(0) ≠ 0`. -/
theorem exists_inv_mod {U : ℂ[X]} (hU : U.coeff 0 ≠ 0) (d : ℕ) :
    ∃ S E : ℂ[X], S * U = 1 + E * X ^ (d + 1) := by
  have hX : ¬ (X : ℂ[X]) ∣ U := by rw [X_dvd_iff]; exact hU
  have hc : IsCoprime (X : ℂ[X]) U := (irreducible_X.coprime_iff_not_dvd).mpr hX
  obtain ⟨a, b, hab⟩ := hc.pow_left (m := d + 1)
  exact ⟨b, -a, by linear_combination hab⟩

/-- The error term `E(D) D^{d+1}` kills polynomials of degree `≤ d`. -/
theorem dOp_mul_X_pow_eq_zero (E : ℂ[X]) {d : ℕ} {q : ℂ[X]} (hq : q.natDegree ≤ d) :
    dOp (E * X ^ (d + 1)) q = 0 := by
  rw [dOp_mul, Module.End.mul_apply, dOp_X_pow_apply,
    iterate_derivative_eq_zero (by omega), map_zero]

/-- **`U(D)` has a left inverse on each degree piece**: `q = S(D) U(D) q`. -/
theorem exists_left_inv {U : ℂ[X]} (hU : U.coeff 0 ≠ 0) (q : ℂ[X]) :
    ∃ S : ℂ[X], dOp S (dOp U q) = q := by
  obtain ⟨S, E, hSE⟩ := exists_inv_mod hU q.natDegree
  refine ⟨S, ?_⟩
  rw [← Module.End.mul_apply, ← dOp_mul, hSE, dOp_add, LinearMap.add_apply, dOp_one,
    Module.End.one_apply, dOp_mul_X_pow_eq_zero E le_rfl, add_zero]

/-- **`U(D)` is surjective when `U(0) ≠ 0`.** -/
theorem dOp_surjective_of_coeff_zero_ne {U : ℂ[X]} (hU : U.coeff 0 ≠ 0) :
    Function.Surjective (dOp U) := by
  intro t
  obtain ⟨S, E, hSE⟩ := exists_inv_mod hU t.natDegree
  refine ⟨dOp S t, ?_⟩
  rw [← Module.End.mul_apply, ← dOp_mul, mul_comm, hSE, dOp_add, LinearMap.add_apply, dOp_one,
    Module.End.one_apply, dOp_mul_X_pow_eq_zero E le_rfl, add_zero]

/-- **`U(D)` preserves the degree when `U(0) ≠ 0`.** -/
theorem natDegree_le_of_coeff_zero_ne {U : ℂ[X]} (hU : U.coeff 0 ≠ 0) (q : ℂ[X]) :
    q.natDegree ≤ (dOp U q).natDegree := by
  obtain ⟨S, hS⟩ := exists_left_inv hU q
  calc q.natDegree = (dOp S (dOp U q)).natDegree := by rw [hS]
    _ ≤ (dOp U q).natDegree := natDegree_dOp_le _ _

/-- **`T(D)` is surjective on `ℂ[ℓ]` for every nonzero `T`.**  This is what makes the
log-Frobenius recursion solvable at every resonance. -/
theorem dOp_surjective {T : ℂ[X]} (hT : T ≠ 0) : Function.Surjective (dOp T) := by
  obtain ⟨U, hTU, hU⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd T hT 0
  rw [map_zero, sub_zero] at hTU hU
  have hU0 : U.coeff 0 ≠ 0 := by rwa [X_dvd_iff] at hU
  rw [hTU, dOp_mul]
  have h1 : Function.Surjective (dOp (X ^ T.rootMultiplicity 0)) := by
    intro t
    obtain ⟨q, hq⟩ := (derivative_surjective.iterate (T.rootMultiplicity 0)) t
    exact ⟨q, by rw [dOp_X_pow_apply, hq]⟩
  exact h1.comp (dOp_surjective_of_coeff_zero_ne hU0)

/-! ## Log-series and the equation -/

/-- `θ_λ` on log-series: `p n ∈ ℂ[ℓ]` is the coefficient of `y^{λ+n}`, and
`θ(y^{λ+n} p(ℓ)) = y^{λ+n} ((λ+n) p + p')`. -/
noncomputable def thetaL (lam : ℂ) (p : ℕ → ℂ[X]) : ℕ → ℂ[X] :=
  fun n => dOp (X + Polynomial.C (lam + n)) (p n)

theorem thetaL_iterate (lam : ℂ) (i : ℕ) (p : ℕ → ℂ[X]) (n : ℕ) :
    (thetaL lam)^[i] p n = dOp ((X + Polynomial.C (lam + n)) ^ i) (p n) := by
  induction i with
  | zero => simp [dOp_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', thetaL]
    rw [ih, ← Module.End.mul_apply, ← dOp_mul, pow_succ']

/-- Multiplication of a log-series by a power series `c(y)`. -/
noncomputable def psMul (c : PowerSeries ℂ) (p : ℕ → ℂ[X]) : ℕ → ℂ[X] :=
  fun n => ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff (n - m) c • p m

/-- **The Fuchsian equation on log-series**: `θ_λ^s p + Σ_{i<s} cᵢ · θ_λ^i p = 0`, i.e.
`F = y^λ Σ_n yⁿ pₙ(log y)` solves `θ^s F + Σ_{i<s} cᵢ(y) θ^i F = 0` formally. -/
def LogFuchsianEq (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (p : ℕ → ℂ[X]) : Prop :=
  ∀ n, (thetaL lam)^[s] p n + ∑ i ∈ Finset.range s, psMul (c i) ((thetaL lam)^[i] p) n = 0

/-- The shifted indicial polynomial `P_n(X) = (X+λ+n)^s + Σ_{i<s} c_{i,0} (X+λ+n)^i`; its
constant term is the indicial polynomial at `λ + n`. -/
noncomputable def indPoly (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n : ℕ) : ℂ[X] :=
  (X + Polynomial.C (lam + n)) ^ s
    + ∑ i ∈ Finset.range s,
        Polynomial.C (PowerSeries.coeff 0 (c i)) * (X + Polynomial.C (lam + n)) ^ i

/-- The lower-order part of the recursion: the contribution of `pₘ`, `m < n`. -/
noncomputable def tailL (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (p : ℕ → ℂ[X]) (n : ℕ) :
    ℂ[X] :=
  ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
    PowerSeries.coeff (n - m) (c i) • dOp ((X + Polynomial.C (lam + m)) ^ i) (p m)

theorem indPoly_monic (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n : ℕ) :
    (indPoly lam s c n).Monic := by
  have hm : ((X + Polynomial.C (lam + n)) ^ s : ℂ[X]).Monic := (monic_X_add_C _).pow s
  have hdeg : ((X + Polynomial.C (lam + n)) ^ s : ℂ[X]).degree = s := by
    rw [degree_pow, degree_X_add_C, nsmul_one]
  refine hm.add_of_left ?_
  rw [hdeg]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe s)).mpr fun i hi => ?_
  have hi' : i < s := Finset.mem_range.mp hi
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  refine lt_of_le_of_lt (add_le_add degree_C_le (degree_pow_le _ _)) ?_
  rw [degree_X_add_C, zero_add, nsmul_one]
  exact Nat.cast_lt.mpr hi'

theorem indPoly_ne_zero (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n : ℕ) :
    indPoly lam s c n ≠ 0 :=
  (indPoly_monic lam s c n).ne_zero

/-- The constant term of `P_n` is the library's indicial polynomial `indicialP` at `λ + n`. -/
theorem coeff_zero_indPoly (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n : ℕ) :
    (indPoly lam s c n).coeff 0
      = VOA.indicialP lam s (fun i k => PowerSeries.coeff k (c i)) n := by
  rw [coeff_zero_eq_eval_zero, indPoly, VOA.indicialP]
  simp [eval_finsetSum]

/-- **The coefficient recursion.** -/
theorem logFuchsianEq_iff {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ} {p : ℕ → ℂ[X]} :
    LogFuchsianEq lam s c p ↔ ∀ n, dOp (indPoly lam s c n) (p n) + tailL lam s c p n = 0 := by
  refine forall_congr' fun n => ?_
  have hL : (thetaL lam)^[s] p n + ∑ i ∈ Finset.range s, psMul (c i) ((thetaL lam)^[i] p) n
      = dOp (indPoly lam s c n) (p n) + tailL lam s c p n := by
    simp only [psMul, thetaL_iterate, Finset.sum_range_succ, Nat.sub_self, indPoly, dOp_add,
      LinearMap.add_apply, dOp_sum_apply, dOp_C_mul, tailL]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    abel
  rw [hL]

/-! ## Existence of log-solutions -/

/-- Strong recursion on `ℕ`. -/
noncomputable def strongSeq {α : Type*} (step : (n : ℕ) → (Fin n → α) → α) : ℕ → α
  | n => step n (fun m => strongSeq step m)
termination_by n => n
decreasing_by exact m.isLt

theorem strongSeq_eq {α : Type*} (step : (n : ℕ) → (Fin n → α) → α) (n : ℕ) :
    strongSeq step n = step n (fun m => strongSeq step m) := by
  rw [strongSeq]

/-- One step of the recursion: zero below `n₀`, `r` at `n₀`, and above `n₀` a preimage of the
right-hand side under `P_n(D)` (which exists by `dOp_surjective`). -/
noncomputable def solStep (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n₀ : ℕ) (r : ℂ[X])
    (n : ℕ) (prev : Fin n → ℂ[X]) : ℂ[X] :=
  if n < n₀ then 0 else if n = n₀ then r else
    Function.surjInv (dOp_surjective (indPoly_ne_zero lam s c n))
      (-∑ m : Fin n, ∑ i ∈ Finset.range s,
        PowerSeries.coeff (n - m) (c i) • dOp ((X + Polynomial.C (lam + (m : ℕ))) ^ i) (prev m))

/-- **Existence of formal log-solutions, for every resonance pattern.**  For every `n₀` and
every `r ∈ ker P_{n₀}(D)` (e.g. `r ≠ 0` constant when `λ + n₀` is an indicial root), there is a
formal log-solution `p` with `pₘ = 0` for `m < n₀` and `p_{n₀} = r`. -/
theorem exists_logFuchsianEq (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n₀ : ℕ) (r : ℂ[X])
    (hr : dOp (indPoly lam s c n₀) r = 0) :
    ∃ p : ℕ → ℂ[X], LogFuchsianEq lam s c p ∧ (∀ m < n₀, p m = 0) ∧ p n₀ = r := by
  set p := strongSeq (solStep lam s c n₀ r) with hpdef
  have hp : ∀ n, p n = solStep lam s c n₀ r n (fun m => p m) := fun n => strongSeq_eq _ n
  have hlow : ∀ m < n₀, p m = 0 := fun m hm => by rw [hp, solStep, if_pos hm]
  have hn₀ : p n₀ = r := by rw [hp, solStep, if_neg (lt_irrefl _), if_pos rfl]
  refine ⟨p, logFuchsianEq_iff.mpr fun n => ?_, hlow, hn₀⟩
  have htail : tailL lam s c p n
      = ∑ m : Fin n, ∑ i ∈ Finset.range s,
          PowerSeries.coeff (n - m) (c i) • dOp ((X + Polynomial.C (lam + (m : ℕ))) ^ i) (p m) := by
    rw [tailL, ← Fin.sum_univ_eq_sum_range
      (fun m => ∑ i ∈ Finset.range s,
        PowerSeries.coeff (n - m) (c i) • dOp ((X + Polynomial.C (lam + (m : ℕ))) ^ i) (p m))]
  rcases lt_trichotomy n n₀ with hn | rfl | hn
  · rw [hlow n hn, map_zero, zero_add, tailL]
    refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun i _ => ?_
    rw [hlow m (lt_trans (Finset.mem_range.mp hm) hn), map_zero, smul_zero]
  · rw [hn₀, hr, zero_add, tailL]
    refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun i _ => ?_
    rw [hlow m (Finset.mem_range.mp hm), map_zero, smul_zero]
  · have hpn := hp n
    rw [solStep, if_neg (by omega), if_neg (by omega)] at hpn
    rw [hpn, Function.surjInv_eq (dOp_surjective (indPoly_ne_zero lam s c n)), htail]
    exact neg_add_cancel _

/-! ## The `ℓ`-degree of a log-solution is bounded -/

/-- Beyond some `N`, `λ + n` is never an indicial root. -/
theorem eventually_indicialP_ne_zero (lam : ℂ) {s : ℕ} (hs : 1 ≤ s) (c : ℕ → PowerSeries ℂ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (indPoly lam s c n).coeff 0 ≠ 0 := by
  have ht := VOA.tendsto_indicialDivisor_atTop lam hs (fun i k => PowerSeries.coeff k (c i))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨N, fun n hn h0 => ?_⟩
  have h1 := hN n hn
  rw [coeff_zero_indPoly] at h0
  rw [VOA.indicialDivisor, h0, norm_zero, zero_div] at h1
  linarith

/-- **Formal log-solutions have bounded `ℓ`-degree.** -/
theorem exists_natDegree_bound {lam : ℂ} {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    {p : ℕ → ℂ[X]} (h : LogFuchsianEq lam s c p) : ∃ K : ℕ, ∀ n, (p n).natDegree ≤ K := by
  obtain ⟨N, hN⟩ := eventually_indicialP_ne_zero lam hs c
  refine ⟨(Finset.range N).sup fun m => (p m).natDegree, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · exact Finset.le_sup (f := fun m => (p m).natDegree) (Finset.mem_range.mpr hn)
    · push Not at hn
      have heq := logFuchsianEq_iff.mp h n
      have h1 := natDegree_le_of_coeff_zero_ne (hN n hn) (p n)
      rw [eq_neg_of_add_eq_zero_left heq, natDegree_neg] at h1
      refine le_trans h1 ?_
      refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine le_trans (natDegree_smul_le _ _) (le_trans (natDegree_dOp_le _ _) ?_)
      exact ih m (Finset.mem_range.mp hm)

end VOA.Huang.FrobeniusLog

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FrobeniusLog
import VOA.Huang.FuchsianODE

/-!
# Frobenius theory with logarithms: convergence (convergence part)

A formal log-solution `F = y^λ Σ_n yⁿ pₙ(log y)` (`FrobeniusLog.LogFuchsianEq`) of a Fuchsian
equation whose coefficients converge on the unit disc converges there: **every `ℓ`-coefficient
sequence `n ↦ coeff k (pₙ)` is subexponential** (`subexponential_coeff_of_logFuchsianEq`).  So
`F = y^λ Σ_{k ≤ K} (log y)^k h_k(y)` with `h_k(y) = Σ_n coeff k (pₙ) yⁿ` holomorphic on `|y| < 1`.

## Method (no matrix majorant needed)

The `ℓ`-degree is bounded (`exists_natDegree_bound`), so one argues by **downward induction on
`k`**.  The `ℓᵏ`-coefficient of the `y^{λ+n}`-equation is the scalar indicial recursion for
`χₙ = coeff k (pₙ)` — exactly the one of `Modularity.IndicialRecursion` — plus an inhomogeneity
built from the higher coefficients `coeff (k+j+1) (pₘ)`, `m ≤ n`, which are subexponential by
induction.  The inhomogeneity carries polynomial weights `(λ+m)^{i−j−1}` of degree `≤ s − 1`, which
the library's normalisation `(max ‖λ‖ 1 + n)^{s−1}` absorbs; the inhomogeneous majorant theorem
(`subexponential_of_majorant_recursion`, which already allows an inhomogeneity) closes it.

## Main results
* `coeff_dOp_X_add_C_pow` — the `ℓᵏ`-coefficient of `(X + a)^i(D) q`: `aⁱ qₖ + remainder`.
* `subexponential_of_indicial_recursion_inhom` — the library's indicial-recursion lemma with an
  inhomogeneity `‖eₙ‖ ≤ (max ‖λ‖ 1 + n)^{s−1} bₙ`, `b` subexponential.
* `subexponential_coeff_of_logFuchsianEq` — convergence of formal log-solutions.
* `summable_coeff_of_logFuchsianEq` — each `h_k` converges absolutely on `‖y‖ < 1`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.FrobeniusLog

open Polynomial Filter
open scoped BigOperators

/-! ## The inhomogeneous indicial recursion -/

/-- **The indicial recursion with an inhomogeneity gives subexponential coefficients.**  As
`VOA.subexponential_of_indicial_recursion`, with an extra term `eₙ` bounded by
`(max ‖λ‖ 1 + n)^{s−1} · bₙ`, `b` subexponential. -/
theorem subexponential_of_indicial_recursion_inhom {χ e : ℕ → ℂ} {b : ℕ → ℝ} (lam : ℂ) {s : ℕ}
    (hs : 1 ≤ s) (g : ℕ → ℕ → ℂ) (hg : ∀ i, Subexponential (fun k => ‖g i k‖))
    (hb0 : ∀ n, 0 ≤ b n) (hb : Subexponential b)
    (he : ∀ n : ℕ, ‖e n‖ ≤ (max ‖lam‖ 1 + (n : ℝ)) ^ (s - 1) * b n)
    (hrec : ∀ n : ℕ, indicialP lam s g n * χ n
      = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          g i (n - m) * (lam + (m : ℂ)) ^ i * χ m + e n) :
    Subexponential (fun n => ‖χ n‖) := by
  classical
  set B : ℝ := max ‖lam‖ 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hBn : ∀ n : ℕ, (1 : ℝ) ≤ B + (n : ℝ) := fun n => by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hBnpos : ∀ n : ℕ, (0 : ℝ) < (B + (n : ℝ)) ^ (s - 1) := fun n =>
    pow_pos (by linarith [hBn n]) _
  refine subexponential_of_majorant_recursion
    (χ := fun n => ‖χ n‖) (a := indicialKernel s g) (b := b)
    (p := indicialDivisor lam s g)
    (fun n => norm_nonneg _) (indicialKernel_nonneg s g) hb0
    (subexponential_indicialKernel s g hg) hb
    (tendsto_indicialDivisor_atTop lam hs g) 0 ?_
  intro n _
  have hnorm : ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖
        + (B + (n : ℝ)) ^ (s - 1) * b n := by
    have h1 : ‖indicialP lam s g n‖ * ‖χ n‖
        = ‖- ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            g i (n - m) * (lam + (m : ℂ)) ^ i * χ m + e n‖ := by
      rw [← norm_mul, hrec n]
    rw [h1]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ (he n))
    rw [norm_neg]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmn : m < n := Finset.mem_range.mp hm
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range s,
        ‖g i (n - m) * (lam + (m : ℂ)) ^ i * χ m‖
          ≤ (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by
      intro i hi
      have his : i ≤ s - 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hlm : ‖lam + (m : ℂ)‖ ≤ B + (n : ℝ) := by
        refine le_trans (norm_add_le _ _) ?_
        have : ‖(m : ℂ)‖ = (m : ℝ) := by simp
        rw [this]
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hmn
        have : ‖lam‖ ≤ B := le_max_left _ _
        linarith
      have hpow : ‖lam + (m : ℂ)‖ ^ i ≤ (B + (n : ℝ)) ^ (s - 1) := by
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hlm i) ?_
        exact pow_le_pow_right₀ (hBn n) his
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖g i (n - m)‖ * ‖lam + (m : ℂ)‖ ^ i * ‖χ m‖
          ≤ ‖g i (n - m)‖ * (B + (n : ℝ)) ^ (s - 1) * ‖χ m‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by ring
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [← Finset.mul_sum, indicialKernel, Finset.sum_mul]
  rw [indicialDivisor, div_mul_eq_mul_div, div_le_iff₀ (hBnpos n)]
  calc ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖
        + (B + (n : ℝ)) ^ (s - 1) * b n := hnorm
    _ = ((∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖) + b n)
          * (B + (n : ℝ)) ^ (s - 1) := by ring

/-! ## The `ℓᵏ`-coefficient of `(X + a)^i(D) q` -/

/-- The remainder of the `ℓᵏ`-coefficient of `(X + a)^i(D) q`: the contribution of the higher
coefficients `q_{k+j+1}`, `j < i`. -/
noncomputable def remL (a : ℂ) (i k : ℕ) (q : ℂ[X]) : ℂ :=
  ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℂ) * a ^ (i - (j + 1))
    * ((k + (j + 1)).descFactorial (j + 1) : ℂ) * q.coeff (k + (j + 1))

/-- **The `ℓᵏ`-coefficient of `(X + a)^i(D) q`** is `aⁱ qₖ` plus the remainder `remL`. -/
theorem coeff_dOp_X_add_C_pow (a : ℂ) (i k : ℕ) (q : ℂ[X]) :
    (dOp ((X + Polynomial.C a) ^ i) q).coeff k = a ^ i * q.coeff k + remL a i k q := by
  have hdeg : ((X + Polynomial.C a) ^ i : ℂ[X]).natDegree < i + 1 := by
    refine lt_of_le_of_lt natDegree_pow_le ?_
    rw [natDegree_X_add_C, mul_one]
    omega
  rw [dOp, aeval_eq_sum_range' hdeg, LinearMap.coe_sum, Finset.sum_apply, finsetSum_coeff,
    Finset.sum_range_succ', remL]
  simp only [LinearMap.smul_apply, Module.End.pow_apply, coeff_smul, coeff_iterate_derivative,
    coeff_X_add_C_pow, smul_eq_mul, nsmul_eq_mul]
  rw [add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- A crude bound for the remainder. -/
theorem norm_remL_le {a : ℂ} {M : ℝ} (hM : 1 ≤ M) (ha : ‖a‖ ≤ M) {i s : ℕ} (his : i ≤ s)
    (k : ℕ) (q : ℂ[X]) :
    ‖remL a i k q‖ ≤ M ^ (s - 1) * ((2 : ℝ) ^ s * ((k + s : ℕ) : ℝ) ^ s)
      * ∑ j ∈ Finset.range s, ‖q.coeff (k + (j + 1))‖ := by
  rw [remL]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr his)
    fun _ _ _ => norm_nonneg _) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  have hjs : j < s := Finset.mem_range.mp hj
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  have h1 : ‖((i.choose (j + 1) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ s := by
    rw [Complex.norm_natCast]
    have := Nat.choose_le_two_pow i (j + 1)
    have h2 : (2 : ℕ) ^ i ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) his
    exact_mod_cast le_trans this h2
  have h2 : ‖a‖ ^ (i - (j + 1)) ≤ M ^ (s - 1) := by
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) ha _) ?_
    exact pow_le_pow_right₀ hM (by omega)
  have h3 : ‖(((k + (j + 1)).descFactorial (j + 1) : ℕ) : ℂ)‖ ≤ ((k + s : ℕ) : ℝ) ^ s := by
    rw [Complex.norm_natCast]
    have := Nat.descFactorial_le_pow (k + (j + 1)) (j + 1)
    have h4 : (k + (j + 1)) ^ (j + 1) ≤ (k + s) ^ s := by
      calc (k + (j + 1)) ^ (j + 1) ≤ (k + s) ^ (j + 1) :=
            Nat.pow_le_pow_left (by omega) _
        _ ≤ (k + s) ^ s := by
            rcases Nat.eq_zero_or_pos (k + s) with h0 | hpos
            · omega
            · exact Nat.pow_le_pow_right hpos (by omega)
    exact_mod_cast le_trans this h4
  have hM0 : 0 ≤ M ^ (s - 1) := pow_nonneg (by linarith) _
  calc ‖((i.choose (j + 1) : ℕ) : ℂ)‖ * ‖a‖ ^ (i - (j + 1))
        * ‖(((k + (j + 1)).descFactorial (j + 1) : ℕ) : ℂ)‖ * ‖q.coeff (k + (j + 1))‖
      ≤ (2 : ℝ) ^ s * M ^ (s - 1) * ((k + s : ℕ) : ℝ) ^ s * ‖q.coeff (k + (j + 1))‖ := by
        gcongr
    _ = M ^ (s - 1) * ((2 : ℝ) ^ s * ((k + s : ℕ) : ℝ) ^ s) * ‖q.coeff (k + (j + 1))‖ := by ring

/-! ## Convergence of log-solutions -/

theorem logFuchsianEq_congr {lam : ℂ} {s : ℕ} {c c' : ℕ → PowerSeries ℂ}
    (hcc : ∀ i < s, c i = c' i) {p : ℕ → ℂ[X]} :
    LogFuchsianEq lam s c p ↔ LogFuchsianEq lam s c' p := by
  unfold LogFuchsianEq
  refine forall_congr' fun n => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [hcc i (Finset.mem_range.mp hi)]]

/-- Real convolutions of nonnegative subexponential sequences are subexponential. -/
theorem subexponential_conv {u v : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hu : Subexponential u) (hv : Subexponential v) :
    Subexponential fun n => ∑ m ∈ Finset.range n, v (n - m) * u m := by
  have hc := subexponential_cauchy (a := fun m => (u m : ℂ)) (b := fun m => (v m : ℂ))
    (by simpa [abs_of_nonneg (hu0 _)] using hu) (by simpa [abs_of_nonneg (hv0 _)] using hv)
  refine Subexponential.of_le (fun n => ?_) hc
  have hnn : 0 ≤ ∑ m ∈ Finset.range (n + 1), u m * v (n - m) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hu0 m) (hv0 _)
  have heq : ‖∑ m ∈ Finset.range (n + 1), (u m : ℂ) * (v (n - m) : ℂ)‖
      = ∑ m ∈ Finset.range (n + 1), u m * v (n - m) := by
    have hcast : ∑ m ∈ Finset.range (n + 1), (u m : ℂ) * (v (n - m) : ℂ)
        = ((∑ m ∈ Finset.range (n + 1), u m * v (n - m) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg hnn]
  rw [heq, Finset.sum_range_succ]
  have : 0 ≤ u n * v (n - n) := mul_nonneg (hu0 n) (hv0 _)
  have hs : ∑ m ∈ Finset.range n, v (n - m) * u m = ∑ m ∈ Finset.range n, u m * v (n - m) :=
    Finset.sum_congr rfl fun m _ => mul_comm _ _
  linarith

/-- The induction step: if all higher coefficients are subexponential, so is the `k`-th. -/
theorem subexponential_coeff_step {lam : ℂ} {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i, c i ∈ SubexpPS) {p : ℕ → ℂ[X]} (h : LogFuchsianEq lam s c p) (k : ℕ)
    (hhigh : ∀ j, Subexponential fun n => ‖(p n).coeff (k + (j + 1))‖) :
    Subexponential fun n => ‖(p n).coeff k‖ := by
  classical
  set g : ℕ → ℕ → ℂ := fun i t => PowerSeries.coeff t (c i) with hg
  have hgsub : ∀ i, Subexponential (fun t => ‖g i t‖) := fun i => (mem_subexpPS).mp (hc i)
  set B : ℝ := max ‖lam‖ 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  set Ck : ℝ := (2 : ℝ) ^ s * ((k + s : ℕ) : ℝ) ^ s with hCk
  have hCk0 : 0 ≤ Ck := by positivity
  set H : ℕ → ℝ := fun m => ∑ j ∈ Finset.range s, ‖(p m).coeff (k + (j + 1))‖ with hH
  have hH0 : ∀ m, 0 ≤ H m := fun m => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hHsub : Subexponential H :=
    Subexponential.finsetSum _ _ fun j _ => hhigh j
  set C0 : ℝ := 1 + ∑ i ∈ Finset.range s, ‖g i 0‖ with hC0
  have hC00 : 0 ≤ C0 := by
    have : 0 ≤ ∑ i ∈ Finset.range s, ‖g i 0‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set b : ℕ → ℝ := fun n => Ck * (C0 * H n
      + ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * H m) with hbdef
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg hCk0 (add_nonneg (mul_nonneg hC00 (hH0 n))
    (Finset.sum_nonneg fun m _ => mul_nonneg (indicialKernel_nonneg s g _) (hH0 m)))
  have hbsub : Subexponential b :=
    ((hHsub.const_mul hC00).add (subexponential_conv hH0 (indicialKernel_nonneg s g) hHsub
      (subexponential_indicialKernel s g hgsub))).const_mul hCk0
  -- the inhomogeneity
  set e : ℕ → ℂ := fun n => -(remL (lam + n) s k (p n)
      + ∑ i ∈ Finset.range s, g i 0 * remL (lam + n) i k (p n)
      + ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s, g i (n - m) * remL (lam + m) i k (p m))
    with hedef
  refine subexponential_of_indicial_recursion_inhom (e := e) (b := b) lam hs g hgsub hb0 hbsub
    ?_ ?_
  · -- the bound on `e`
    intro n
    have hBn : (1 : ℝ) ≤ B + n := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hnorm_n : ‖lam + (n : ℂ)‖ ≤ B + n := by
      refine le_trans (norm_add_le _ _) ?_
      rw [Complex.norm_natCast]
      have : ‖lam‖ ≤ B := le_max_left _ _
      linarith
    have hP : (0 : ℝ) ≤ (B + n) ^ (s - 1) := by positivity
    have e1 : ‖remL (lam + n) s k (p n)‖ ≤ (B + n) ^ (s - 1) * Ck * H n :=
      norm_remL_le hBn hnorm_n le_rfl k (p n)
    have e2 : ‖∑ i ∈ Finset.range s, g i 0 * remL (lam + n) i k (p n)‖
        ≤ (B + n) ^ (s - 1) * Ck * ((∑ i ∈ Finset.range s, ‖g i 0‖) * H n) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul]
      have := norm_remL_le hBn hnorm_n (le_of_lt (Finset.mem_range.mp hi)) k (p n)
      calc ‖g i 0‖ * ‖remL (lam + n) i k (p n)‖
          ≤ ‖g i 0‖ * ((B + n) ^ (s - 1) * Ck * H n) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = (B + n) ^ (s - 1) * Ck * (‖g i 0‖ * H n) := by ring
    have e3 : ‖∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          g i (n - m) * remL (lam + m) i k (p m)‖
        ≤ (B + n) ^ (s - 1) * Ck * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * H m := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m hm => ?_
      have hmn : m < n := Finset.mem_range.mp hm
      have hnorm_m : ‖lam + (m : ℂ)‖ ≤ B + n := by
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_natCast]
        have : ‖lam‖ ≤ B := le_max_left _ _
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
        linarith
      refine le_trans (norm_sum_le _ _) ?_
      rw [indicialKernel, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul]
      have := norm_remL_le hBn hnorm_m (le_of_lt (Finset.mem_range.mp hi)) k (p m)
      calc ‖g i (n - m)‖ * ‖remL (lam + m) i k (p m)‖
          ≤ ‖g i (n - m)‖ * ((B + n) ^ (s - 1) * Ck * H m) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = (B + n) ^ (s - 1) * Ck * (‖g i (n - m)‖ * H m) := by ring
    calc ‖e n‖ ≤ ‖remL (lam + n) s k (p n)‖
          + ‖∑ i ∈ Finset.range s, g i 0 * remL (lam + n) i k (p n)‖
          + ‖∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
              g i (n - m) * remL (lam + m) i k (p m)‖ := by
          rw [hedef]
          simp only [norm_neg]
          exact le_trans (norm_add_le _ _) (add_le_add_left (norm_add_le _ _) _)
      _ ≤ (B + n) ^ (s - 1) * Ck * H n
          + (B + n) ^ (s - 1) * Ck * ((∑ i ∈ Finset.range s, ‖g i 0‖) * H n)
          + (B + n) ^ (s - 1) * Ck
              * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * H m := by
          gcongr
      _ = (B + n) ^ (s - 1) * b n := by rw [hbdef, hC0]; ring
  · -- the recursion
    intro n
    have heq := congrArg (fun q => q.coeff k) (logFuchsianEq_iff.mp h n)
    simp only [coeff_add, coeff_zero] at heq
    rw [indPoly, dOp_add, LinearMap.add_apply, coeff_add, dOp_sum_apply, finsetSum_coeff,
      coeff_dOp_X_add_C_pow, tailL, finsetSum_coeff] at heq
    simp only [dOp_C_mul, coeff_smul, smul_eq_mul, finsetSum_coeff,
      coeff_dOp_X_add_C_pow] at heq
    rw [indicialP, hedef]
    simp only [hg]
    have hsplit1 : ∑ i ∈ Finset.range s, PowerSeries.coeff 0 (c i)
          * ((lam + n) ^ i * (p n).coeff k + remL (lam + n) i k (p n))
        = (∑ i ∈ Finset.range s, PowerSeries.coeff 0 (c i) * (lam + n) ^ i) * (p n).coeff k
          + ∑ i ∈ Finset.range s, PowerSeries.coeff 0 (c i) * remL (lam + n) i k (p n) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit2 : ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s, PowerSeries.coeff (n - m) (c i)
          * ((lam + m) ^ i * (p m).coeff k + remL (lam + m) i k (p m))
        = ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            PowerSeries.coeff (n - m) (c i) * (lam + m) ^ i * (p m).coeff k
          + ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            PowerSeries.coeff (n - m) (c i) * remL (lam + m) i k (p m) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit1, hsplit2] at heq
    linear_combination heq

/-- **Formal log-solutions of a Fuchsian equation converge.**  If the coefficients `cᵢ`,
`i < s`, converge on the unit disc (`SubexpPS`), then every `ℓ`-coefficient sequence of every
formal log-solution is subexponential. -/
theorem subexponential_coeff_of_logFuchsianEq {lam : ℂ} {s : ℕ} (hs : 1 ≤ s)
    {c : ℕ → PowerSeries ℂ} (hc : ∀ i < s, c i ∈ SubexpPS) {p : ℕ → ℂ[X]}
    (h : LogFuchsianEq lam s c p) (k : ℕ) :
    Subexponential fun n => ‖(p n).coeff k‖ := by
  classical
  set c' : ℕ → PowerSeries ℂ := fun i => if i < s then c i else 0 with hc'
  have h' : LogFuchsianEq lam s c' p :=
    (logFuchsianEq_congr (fun i hi => by simp [hc', hi])).mp h
  have hc'sub : ∀ i, c' i ∈ SubexpPS := fun i => by
    by_cases hi : i < s
    · simpa [hc', hi] using hc i hi
    · simp [hc', hi, SubexpPS.zero_mem]
  obtain ⟨K, hK⟩ := exists_natDegree_bound hs h'
  have key : ∀ t k, K < k + t → Subexponential fun n => ‖(p n).coeff k‖ := by
    intro t
    induction t with
    | zero =>
      intro k hk
      refine Subexponential.of_le (fun n => le_of_eq ?_) (subexponential_const 0)
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hK n) (by omega)), norm_zero]
    | succ t ih =>
      intro k hk
      exact subexponential_coeff_step hs hc'sub h' k fun j => ih _ (by omega)
  exact key (K + 1) k (by omega)

/-- Each `h_k(y) = Σ_n coeff k (pₙ) yⁿ` converges absolutely on `‖y‖ < 1`. -/
theorem summable_coeff_of_logFuchsianEq {lam : ℂ} {s : ℕ} (hs : 1 ≤ s)
    {c : ℕ → PowerSeries ℂ} (hc : ∀ i < s, c i ∈ SubexpPS) {p : ℕ → ℂ[X]}
    (h : LogFuchsianEq lam s c p) (k : ℕ) {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun n => ‖(p n).coeff k * y ^ n‖ := by
  have := summable_of_subexponential (fun n => norm_nonneg _)
    (subexponential_coeff_of_logFuchsianEq hs hc h k) (norm_nonneg y) hy
  simpa [norm_mul, norm_pow] using this

end VOA.Huang.FrobeniusLog

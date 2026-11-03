/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FrobeniusAnalytic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Frobenius theory with logarithms: independence via monodromy

On the universal cover `y = e^t`, `Re t < 0`, of the punctured disc, the monodromy around `y = 0`
is the translation `t ↦ t + 2πi`.  It acts on `logFun λ p` (`Huang/FrobeniusAnalytic.lean`) by
`e^{2πiλ}` times the Taylor shift `pₙ(ℓ) ↦ pₙ(ℓ + 2πi)` (`logFun_translate`).  Hence
`T − e^{2πiλ}` lowers the `ℓ`-degree (`logFun_monodromy`), and an elementary
generalized-eigenspace argument shows:

* `eq_zero_of_logFun_eq_zero`: if `logFun λ p ≡ 0` on `Re t < 0`, then `p = 0` (the functions
  `y^{λ+n} (log y)^k` are linearly independent, in the strong summable sense);
* `eq_zero_of_sum_logFun_eq_zero`: the same for a finite sum of log-series whose exponents are
  pairwise **non-congruent mod `ℤ`** (distinct local monodromy eigenvalues `e^{2πiλⱼ}`).

These are the independence inputs of the fundamental-system theorem
(`Huang/FrobeniusFundamental.lean`).

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.FrobeniusLog

open Polynomial Filter Topology
open scoped BigOperators

/-- `2πi`. -/
noncomputable def twoPiI : ℂ := 2 * Real.pi * Complex.I

/-- The local monodromy eigenvalue `e^{2πiλ}`. -/
noncomputable def monoEig (lam : ℂ) : ℂ := Complex.exp (lam * twoPiI)

theorem monoEig_ne_zero (lam : ℂ) : monoEig lam ≠ 0 := Complex.exp_ne_zero _

theorem add_twoPiI_mem {t : ℂ} (ht : t ∈ halfPlane) : t + twoPiI ∈ halfPlane := by
  simp only [halfPlane, Set.mem_setOf_eq, twoPiI, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im] at ht ⊢
  simpa using ht

/-- The Taylor shift `pₙ(ℓ) ↦ pₙ(ℓ + 2πi)`. -/
noncomputable def shiftL (p : ℕ → ℂ[X]) : ℕ → ℂ[X] := fun n => taylor twoPiI (p n)

theorem LogGood.shiftL {p : ℕ → ℂ[X]} (hp : LogGood p) : LogGood (shiftL p) :=
  hp.map (taylor twoPiI) fun q => le_of_eq (natDegree_taylor q _)

/-- **The monodromy**: `logFun λ p (t + 2πi) = e^{2πiλ} logFun λ (shiftL p) t`. -/
theorem logFun_translate (lam : ℂ) (p : ℕ → ℂ[X]) (t : ℂ) :
    logFun lam p (t + twoPiI) = monoEig lam * logFun lam (shiftL p) t := by
  rw [logFun, logFun, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [shiftL, taylor_eval, monoEig]
  have h1 : Complex.exp ((lam + n) * (t + twoPiI))
      = Complex.exp (lam * twoPiI) * Complex.exp ((lam + n) * t)
        * Complex.exp (n * twoPiI) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [h1, twoPiI, Complex.exp_nat_mul_two_pi_mul_I]
  ring

/-! ## Polynomial facts -/

theorem natDegree_taylor_sub_le (a : ℂ) {q : ℂ[X]} {K : ℕ} (hq : q.natDegree ≤ K) :
    (taylor a q - q).natDegree ≤ K - 1 := by
  have h1 : (taylor a q - q).natDegree ≤ q.natDegree := by
    refine le_trans (natDegree_sub_le _ _) ?_
    rw [natDegree_taylor, max_self]
  have h2 : (taylor a q - q).coeff q.natDegree = 0 := by
    rw [coeff_sub, coeff_taylor_natDegree, leadingCoeff, sub_self]
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
  · have : taylor a q - q = 0 := by
      rw [eq_C_of_natDegree_eq_zero h0, taylor_C, sub_self]
    rw [this, natDegree_zero]; exact Nat.zero_le _
  · by_contra hlt
    push Not at hlt
    have heq : (taylor a q - q).natDegree = q.natDegree := by omega
    have : (taylor a q - q).leadingCoeff = 0 := by rw [leadingCoeff, heq, h2]
    rw [leadingCoeff_eq_zero] at this
    rw [this, natDegree_zero] at heq
    omega

theorem taylor_sub_eq_zero_of_natDegree_eq_zero (a : ℂ) {q : ℂ[X]} (hq : q.natDegree ≤ 0) :
    taylor a q - q = 0 := by
  rw [eq_C_of_natDegree_le_zero hq, taylor_C, sub_self]

/-- A polynomial invariant under a nonzero translation is constant. -/
theorem eq_C_of_taylor_eq {a : ℂ} (ha : a ≠ 0) {q : ℂ[X]} (h : taylor a q = q) :
    q = Polynomial.C (q.coeff 0) := by
  have hev : ∀ n : ℕ, q.eval ((n : ℂ) * a) = q.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := congrArg (Polynomial.eval ((n : ℂ) * a)) h
      rw [taylor_eval] at this
      rw [Nat.cast_succ, add_mul, one_mul, this, ih]
  apply eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * a) ?_ ?_
  · intro m n hmn
    have := mul_right_cancel₀ ha hmn
    exact_mod_cast this
  · intro n
    simp only [Set.mem_setOf_eq, eval_C, hev n, coeff_zero_eq_eval_zero]

/-- A twisted difference with distinct eigenvalues is injective. -/
theorem eq_zero_of_twisted {a μ μ' : ℂ} (hμ : μ' ≠ μ) {q : ℂ[X]}
    (h : μ' • taylor a q - μ • q = 0) : q = 0 := by
  have hc := congrArg (fun r => Polynomial.coeff r q.natDegree) h
  simp only [coeff_sub, coeff_smul, coeff_taylor_natDegree, smul_eq_mul, coeff_zero] at hc
  have : (μ' - μ) * q.leadingCoeff = 0 := by rw [leadingCoeff] at hc ⊢; linear_combination hc
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hμ
  · exact leadingCoeff_eq_zero.mp h0

/-! ## The monodromy lowers the degree -/

/-- `Δp = shiftL p − p`. -/
noncomputable def deltaL (p : ℕ → ℂ[X]) : ℕ → ℂ[X] := shiftL p - p

theorem LogGood.deltaL {p : ℕ → ℂ[X]} (hp : LogGood p) : LogGood (deltaL p) :=
  hp.shiftL.sub hp

/-- `logFun λ p (t + 2πi) − e^{2πiλ} logFun λ p t = e^{2πiλ} logFun λ (Δp) t`. -/
theorem logFun_monodromy {p : ℕ → ℂ[X]} (hp : LogGood p) (lam : ℂ) {t : ℂ}
    (ht : t ∈ halfPlane) :
    logFun lam p (t + twoPiI) - monoEig lam * logFun lam p t
      = monoEig lam * logFun lam (deltaL p) t := by
  rw [logFun_translate, deltaL, logFun_sub hp.shiftL hp lam ht]
  ring

/-! ## Power series vanishing on `(0, 1)` -/

/-- A power series with subexponential coefficients vanishing on `(0, 1)` is zero. -/
theorem eq_zero_of_tsum_pow_eq_zero {a : ℕ → ℂ} (ha : Subexponential fun n => ‖a n‖)
    (h : ∀ y : ℝ, 0 < y → y < 1 → ∑' n, a n * (y : ℂ) ^ n = 0) : ∀ n, a n = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hsh : Subexponential fun m => ‖a (m + (N + 1))‖ := ha.shift (N + 1)
  set B : ℝ := ∑' m, ‖a (m + (N + 1))‖ * (1 / 2 : ℝ) ^ m with hB
  have hBs : Summable fun m => ‖a (m + (N + 1))‖ * (1 / 2 : ℝ) ^ m :=
    summable_of_subexponential (fun _ => norm_nonneg _) hsh (by norm_num) (by norm_num)
  have hB0 : 0 ≤ B := tsum_nonneg fun m => by positivity
  have key : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → ‖a N‖ ≤ y * B := by
    intro y hy0 hy1
    have hy1' : y < 1 := by linarith
    have hsum : Summable fun n => a n * (y : ℂ) ^ n := by
      refine Summable.of_norm ?_
      have := summable_of_subexponential (fun _ => norm_nonneg _) ha hy0.le hy1'
      refine this.congr fun n => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
    rw [h y hy0 hy1', Finset.sum_range_succ,
      Finset.sum_eq_zero (fun i hi => by rw [ih i (Finset.mem_range.mp hi), zero_mul]),
      zero_add] at hsplit
    have htail : ∑' m, a (m + (N + 1)) * (y : ℂ) ^ (m + (N + 1))
        = (y : ℂ) ^ (N + 1) * ∑' m, a (m + (N + 1)) * (y : ℂ) ^ m := by
      rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
    rw [htail] at hsplit
    set S := ∑' m, a (m + (N + 1)) * (y : ℂ) ^ m with hS
    have hyN : (y : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast hy0.ne')
    have haN : a N = -(y : ℂ) * S := by
      have : (y : ℂ) ^ N * (a N + (y : ℂ) * S) = 0 := by linear_combination hsplit
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hyN
      · linear_combination h0
    have hSle : ‖S‖ ≤ B := by
      have hs1 : Summable fun m => ‖a (m + (N + 1)) * (y : ℂ) ^ m‖ := by
        have := summable_of_subexponential (fun _ => norm_nonneg _) hsh hy0.le hy1'
        refine this.congr fun m => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]
      refine le_trans (norm_tsum_le_tsum_norm hs1) (hs1.tsum_le_tsum (fun m => ?_) hBs)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]
      gcongr
    rw [haN, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    exact mul_le_mul_of_nonneg_left hSle hy0.le
  by_contra hne
  have hpos : 0 < ‖a N‖ := norm_pos_iff.mpr hne
  set y : ℝ := min (1 / 2) (‖a N‖ / (2 * (B + 1))) with hy
  have hy0 : 0 < y := lt_min (by norm_num) (by positivity)
  have h1 := key y hy0 (min_le_left _ _)
  have h2 : y * B ≤ ‖a N‖ / (2 * (B + 1)) * B :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hB0
  have h3 : ‖a N‖ / (2 * (B + 1)) * B < ‖a N‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Constant-in-`ℓ` log-series: `logFun λ (C ∘ a) ≡ 0` forces `a = 0`. -/
theorem eq_zero_of_logFun_const {a : ℕ → ℂ} (ha : Subexponential fun n => ‖a n‖) (lam : ℂ)
    (h : ∀ t ∈ halfPlane, logFun lam (fun n => Polynomial.C (a n)) t = 0) : ∀ n, a n = 0 := by
  refine eq_zero_of_tsum_pow_eq_zero ha fun y hy0 hy1 => ?_
  set t : ℂ := (Real.log y : ℂ) with ht
  have htH : t ∈ halfPlane := by
    simp only [halfPlane, Set.mem_setOf_eq, ht, Complex.ofReal_re]
    exact Real.log_neg hy0 hy1
  have hexp : Complex.exp t = y := by
    rw [ht, ← Complex.ofReal_exp, Real.exp_log hy0]
  have h1 := h t htH
  rw [logFun] at h1
  have h2 : ∑' n : ℕ, Complex.exp ((lam + n) * t) * (Polynomial.C (a n)).eval t
      = Complex.exp (lam * t) * ∑' n, a n * (y : ℂ) ^ n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [eval_C, ← hexp, ← Complex.exp_nat_mul, add_mul, Complex.exp_add]
    ring
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Complex.exp_ne_zero _)

/-! ## Independence -/

/-- **One exponent class**: `logFun λ p ≡ 0` on `Re t < 0` forces `p = 0`. -/
theorem eq_zero_of_logFun_eq_zero {lam : ℂ} {p : ℕ → ℂ[X]} (hp : LogGood p)
    (h : ∀ t ∈ halfPlane, logFun lam p t = 0) : ∀ n, p n = 0 := by
  obtain ⟨K, hK⟩ := hp.deg
  induction K generalizing p with
  | zero =>
    have hpC : ∀ n, p n = Polynomial.C ((p n).coeff 0) := fun n => eq_C_of_natDegree_le_zero (hK n)
    have h' : ∀ t ∈ halfPlane, logFun lam (fun n => Polynomial.C ((p n).coeff 0)) t = 0 :=
      fun t ht => by rw [← logFun_congr hpC]; exact h t ht
    have := eq_zero_of_logFun_const (hp.coeff 0) lam h'
    intro n; rw [hpC n, this n, map_zero]
  | succ K ih =>
    have hΔ : ∀ n, deltaL p n = 0 := by
      refine ih hp.deltaL (fun t ht => ?_) (fun n => ?_)
      · have := logFun_monodromy hp lam ht
        rw [h t ht, h _ (add_twoPiI_mem ht), mul_zero, sub_zero] at this
        exact ((mul_eq_zero.mp this.symm).resolve_left (monoEig_ne_zero lam))
      · exact natDegree_taylor_sub_le twoPiI (hK n)
    have hpC : ∀ n, p n = Polynomial.C ((p n).coeff 0) := fun n => by
      refine eq_C_of_taylor_eq (a := twoPiI) ?_ ?_
      · simp [twoPiI, Real.pi_ne_zero, Complex.I_ne_zero]
      · have := hΔ n
        simp only [deltaL, shiftL, Pi.sub_apply, sub_eq_zero] at this
        exact this
    have h' : ∀ t ∈ halfPlane, logFun lam (fun n => Polynomial.C ((p n).coeff 0)) t = 0 :=
      fun t ht => by rw [← logFun_congr hpC]; exact h t ht
    have := eq_zero_of_logFun_const (hp.coeff 0) lam h'
    intro n; rw [hpC n, this n, map_zero]

/-- The twisted family `μⱼ • shiftL pⱼ − μ • pⱼ`, i.e. the effect of `T − μ` on each summand. -/
noncomputable def twistL (μ : ℂ) (lam : ℂ) (p : ℕ → ℂ[X]) : ℕ → ℂ[X] :=
  monoEig lam • shiftL p - μ • p

theorem LogGood.twistL {p : ℕ → ℂ[X]} (hp : LogGood p) (μ lam : ℂ) :
    LogGood (FrobeniusLog.twistL μ lam p) :=
  (hp.shiftL.smul _).sub (hp.smul _)

theorem logFun_twistL {p : ℕ → ℂ[X]} (hp : LogGood p) (μ lam : ℂ) {t : ℂ} (ht : t ∈ halfPlane) :
    logFun lam (twistL μ lam p) t = logFun lam p (t + twoPiI) - μ * logFun lam p t := by
  rw [twistL, logFun_sub (hp.shiftL.smul _) (hp.smul _) lam ht, logFun_smul, logFun_smul,
    logFun_translate]

/-- **Several exponent classes**: if the exponents `λⱼ`, `j ∈ S`, have pairwise distinct
monodromy eigenvalues `e^{2πiλⱼ}` (i.e. are pairwise non-congruent mod `ℤ`) and
`Σ_{j∈S} logFun λⱼ pⱼ ≡ 0` on `Re t < 0`, then every `pⱼ = 0`. -/
theorem eq_zero_of_sum_logFun_eq_zero {ι : Type*} (S : Finset ι)
    (lam : ι → ℂ) (hdist : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → monoEig (lam i) ≠ monoEig (lam j))
    (p : ι → ℕ → ℂ[X]) (hp : ∀ j ∈ S, LogGood (p j))
    (h : ∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p j) t = 0) :
    ∀ j ∈ S, ∀ n, p j n = 0 := by
  classical
  induction S using Finset.induction_on generalizing p with
  | empty => simp
  | insert a S haS ihS =>
    have hdistS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → monoEig (lam i) ≠ monoEig (lam j) :=
      fun i hi j hj hij => hdist i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    -- inner induction on the degree of `p a`
    have inner : ∀ K : ℕ, ∀ p : ι → ℕ → ℂ[X], (∀ j ∈ insert a S, LogGood (p j)) →
        (∀ n, (p a n).natDegree ≤ K) →
        (∀ t ∈ halfPlane, ∑ j ∈ insert a S, logFun (lam j) (p j) t = 0) →
        ∀ j ∈ S, ∀ n, p j n = 0 := by
      intro K
      induction K with
      | zero =>
        intro p hp hK h
        set μ := monoEig (lam a)
        set p' : ι → ℕ → ℂ[X] := fun j => twistL μ (lam j) (p j) with hp'
        have hp'a : ∀ n, p' a n = 0 := fun n => by
          simp only [hp', twistL, shiftL, Pi.sub_apply, Pi.smul_apply, μ, ← smul_sub]
          rw [taylor_sub_eq_zero_of_natDegree_eq_zero _ (hK n), smul_zero]
        have hsum : ∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p' j) t = 0 := by
          intro t ht
          have e1 : ∑ j ∈ insert a S, logFun (lam j) (p' j) t
              = ∑ j ∈ insert a S, logFun (lam j) (p j) (t + twoPiI)
                - μ * ∑ j ∈ insert a S, logFun (lam j) (p j) t := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j hj => logFun_twistL (hp j hj) μ (lam j) ht
          rw [h t ht, h _ (add_twoPiI_mem ht), mul_zero, sub_zero, Finset.sum_insert haS,
            logFun_congr hp'a, logFun_zero, zero_add] at e1
          exact e1
        have h' := ihS hdistS p' (fun j hj => (hp j (Finset.mem_insert_of_mem hj)).twistL _ _) hsum
        intro j hj n
        refine eq_zero_of_twisted (a := twoPiI) (μ := μ) (μ' := monoEig (lam j)) ?_ ?_
        · exact hdist j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self _ _)
            (fun hja => haS (hja ▸ hj))
        · have := h' j hj n
          simpa [hp', twistL, shiftL] using this
      | succ K ihK =>
        intro p hp hK h
        set μ := monoEig (lam a)
        set p' : ι → ℕ → ℂ[X] := fun j => twistL μ (lam j) (p j) with hp'
        have hp'good : ∀ j ∈ insert a S, LogGood (p' j) := fun j hj => (hp j hj).twistL _ _
        have hp'deg : ∀ n, (p' a n).natDegree ≤ K := fun n => by
          have e : p' a n = μ • (taylor twoPiI (p a n) - p a n) := by
            simp only [hp', twistL, shiftL, Pi.sub_apply, Pi.smul_apply, μ, smul_sub]
          rw [e]
          exact le_trans (natDegree_smul_le _ _) (natDegree_taylor_sub_le _ (hK n))
        have hsum : ∀ t ∈ halfPlane, ∑ j ∈ insert a S, logFun (lam j) (p' j) t = 0 := by
          intro t ht
          have e1 : ∑ j ∈ insert a S, logFun (lam j) (p' j) t
              = ∑ j ∈ insert a S, logFun (lam j) (p j) (t + twoPiI)
                - μ * ∑ j ∈ insert a S, logFun (lam j) (p j) t := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j hj => logFun_twistL (hp j hj) μ (lam j) ht
          rw [h t ht, h _ (add_twoPiI_mem ht), mul_zero, sub_zero] at e1
          exact e1
        have h' := ihK p' hp'good hp'deg hsum
        intro j hj n
        refine eq_zero_of_twisted (a := twoPiI) (μ := μ) (μ' := monoEig (lam j)) ?_ ?_
        · exact hdist j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self _ _)
            (fun hja => haS (hja ▸ hj))
        · have := h' j hj n
          simpa [hp', twistL, shiftL] using this
    obtain ⟨K, hK⟩ := (hp a (Finset.mem_insert_self _ _)).deg
    have hS := inner K p hp hK h
    have ha : ∀ n, p a n = 0 := by
      refine eq_zero_of_logFun_eq_zero (lam := lam a) (hp a (Finset.mem_insert_self _ _))
        fun t ht => ?_
      have := h t ht
      rw [Finset.sum_insert haS, Finset.sum_eq_zero fun j hj => ?_, add_zero] at this
      · exact this
      · rw [logFun_congr (hS j hj)]; exact logFun_zero _ _
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ha
    · exact hS j hj

end VOA.Huang.FrobeniusLog

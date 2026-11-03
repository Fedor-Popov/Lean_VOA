/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FrobeniusFundamental

/-!
# Coefficients of finite log-expansions

The Huang–Lepowsky route to associativity compares the
expansion of a product of intertwining operators at the iterate point,
`Σⱼ y^{λⱼ} Σₙ yⁿ pⱼₙ(log y)` (Huang (3.3), `HuangODEIterPoint.prod_frobenius_expansion_holds`),
with sums of iterates.  Every route (log removal, identification with iterates) works with the
**coefficient of `y^μ (log y)^k`** of such an expansion.  This file makes that coefficient a
well-defined, linear function of the *function* (not of the chosen expansion), VOA-free.

On the universal cover `y = e^t` (`Re t < 0`) the term `y^{λ+n} (log y)^k` is `e^{(λ+n)t} t^k`;
`exCoeff λ p μ k` is the coefficient of `e^{μ t} t^k` in `logFun λ p`.

## Main results
* `exCoeff`, `exCoeff_add_nat` (`exCoeff (λ+N) p = exCoeff λ (shiftIdx N p)`), linearity.
* `exists_normalForm`: any finite sum of log-series equals, with the same coefficients, a sum
  over pairwise non-congruent (mod `ℤ`) exponents.
* `coeff_eq_zero_of_eval_eq_zero` / `eval_eq_zero_of_coeff_eq_zero`: a finite sum of
  log-series vanishes on `Re t < 0` iff all its coefficients vanish.
* `eval_eq_zero_on_halfPlane`: vanishing on a nonempty open subset of `Re t < 0` suffices
  (identity theorem).
* `LogExp`, `IsExpOn`, `HasLogExp`, `logCoeff U F μ k`, `logCoeff_eq` (independent of the
  expansion), `logCoeff_add`, `logCoeff_smul`, `logCoeff_logFun`, `exCoeff_C`
  (log-free series), `eqOn_of_logCoeff_eq` (functions with the same coefficients agree).

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.LogRemovalCoeff

open VOA.Huang.FrobeniusLog Polynomial Filter Topology
open scoped BigOperators

/-! ## The coefficient of `e^{μt} t^k` in one log-series -/

/-- The coefficient of `e^{μ t} t^k` (i.e. of `y^μ (log y)^k`) in `logFun λ p`. -/
noncomputable def exCoeff (lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) : ℂ := by
  classical
  exact if h : ∃ n : ℕ, lam + n = μ then (p h.choose).coeff k else 0

theorem exCoeff_of_eq (lam : ℂ) (p : ℕ → ℂ[X]) (n : ℕ) (k : ℕ) :
    exCoeff lam p (lam + n) k = (p n).coeff k := by
  have h : ∃ m : ℕ, lam + m = lam + n := ⟨n, rfl⟩
  unfold exCoeff
  rw [dif_pos h]
  have : h.choose = n := by
    have := h.choose_spec
    exact_mod_cast add_left_cancel this
  rw [this]

theorem exCoeff_of_forall_ne {lam μ : ℂ} (h : ∀ n : ℕ, lam + n ≠ μ) (p : ℕ → ℂ[X]) (k : ℕ) :
    exCoeff lam p μ k = 0 := by
  unfold exCoeff
  rw [dif_neg (fun ⟨n, hn⟩ => h n hn)]

theorem exCoeff_zero (lam μ : ℂ) (k : ℕ) : exCoeff lam (fun _ => 0) μ k = 0 := by
  unfold exCoeff; split_ifs <;> simp

theorem exCoeff_of_eq_zero {lam : ℂ} {p : ℕ → ℂ[X]} (hp : ∀ n, p n = 0) (μ : ℂ) (k : ℕ) :
    exCoeff lam p μ k = 0 := by
  unfold exCoeff; split_ifs <;> simp [hp]

theorem exCoeff_add (lam : ℂ) (p q : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (p + q) μ k = exCoeff lam p μ k + exCoeff lam q μ k := by
  unfold exCoeff; split_ifs <;> simp

theorem exCoeff_smul (a lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (a • p) μ k = a * exCoeff lam p μ k := by
  unfold exCoeff; split_ifs <;> simp

theorem exCoeff_neg (lam : ℂ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (-p) μ k = -exCoeff lam p μ k := by
  unfold exCoeff; split_ifs <;> simp

theorem exCoeff_sum {ι : Type*} (S : Finset ι) (lam : ℂ) (p : ι → ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff lam (∑ i ∈ S, p i) μ k = ∑ i ∈ S, exCoeff lam (p i) μ k := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using exCoeff_zero lam μ k
  | insert i S hi ih => rw [Finset.sum_insert hi, exCoeff_add, ih, Finset.sum_insert hi]

/-- Shifting the exponent by `N ∈ ℕ` is the index shift `shiftIdx N`. -/
theorem exCoeff_add_nat (lam : ℂ) (N : ℕ) (p : ℕ → ℂ[X]) (μ : ℂ) (k : ℕ) :
    exCoeff (lam + N) p μ k = exCoeff lam (shiftIdx N p) μ k := by
  by_cases h : ∃ n : ℕ, lam + N + n = μ
  · obtain ⟨n, rfl⟩ := h
    rw [exCoeff_of_eq, show lam + (N : ℂ) + n = lam + ((N + n : ℕ) : ℂ) by push_cast; ring,
      exCoeff_of_eq]
    simp [shiftIdx]
  · rw [exCoeff_of_forall_ne (fun n hn => h ⟨n, hn⟩)]
    by_cases h' : ∃ m : ℕ, lam + m = μ
    · obtain ⟨m, rfl⟩ := h'
      rw [exCoeff_of_eq]
      have hmN : ¬ N ≤ m := by
        intro hle
        exact h ⟨m - N, by push_cast [Nat.cast_sub hle]; ring⟩
      simp [shiftIdx, hmN]
    · rw [exCoeff_of_forall_ne (fun n hn => h' ⟨n, hn⟩)]

/-- A log-free series: `exCoeff λ (C ∘ a) (λ + n) k = a n` if `k = 0`, else `0`. -/
theorem exCoeff_C (lam : ℂ) (a : ℕ → ℂ) (n k : ℕ) :
    exCoeff lam (fun m => Polynomial.C (a m)) (lam + n) k = if k = 0 then a n else 0 := by
  rw [exCoeff_of_eq, Polynomial.coeff_C]

/-! ## Monodromy classes -/

theorem monoEig_add_int (x : ℂ) (m : ℤ) : monoEig (x + m) = monoEig x := by
  unfold monoEig twoPiI
  rw [add_mul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem monoEig_sub_nat (x : ℂ) (m : ℕ) : monoEig (x - m) = monoEig x := by
  have := monoEig_add_int x (-(m : ℤ))
  rw [← this]; congr 1; push_cast; ring

/-- If `λ + m = μ + n` with `m, n ∈ ℕ`, the monodromy eigenvalues agree. -/
theorem monoEig_eq_of_add_nat_eq {lam μ : ℂ} {m n : ℕ} (h : lam + m = μ + n) :
    monoEig lam = monoEig μ := by
  have : lam = μ + ((n : ℤ) - m : ℤ) := by push_cast; linear_combination h
  rw [this, monoEig_add_int]

/-! ## Normal form -/

/-- **Normal form.**  A finite sum of log-series equals (on `Re t < 0`), with the same
coefficients, a finite sum over exponents with pairwise distinct monodromy eigenvalues. -/
theorem exists_normalForm {ι : Type*} (S : Finset ι) (lam : ι → ℂ) (p : ι → ℕ → ℂ[X])
    (hp : ∀ j ∈ S, LogGood (p j)) :
    ∃ (E : Finset ℂ) (ρ : ℂ → ℂ) (q : ℂ → ℕ → ℂ[X]),
      (∀ e ∈ E, monoEig (ρ e) = e) ∧
      (∀ e ∈ E, LogGood (q e)) ∧
      (∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p j) t = ∑ e ∈ E, logFun (ρ e) (q e) t) ∧
      (∀ μ k, ∑ j ∈ S, exCoeff (lam j) (p j) μ k = ∑ e ∈ E, exCoeff (ρ e) (q e) μ k) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · exact ⟨∅, id, fun _ _ => 0, by simp, by simp, by simp, by simp⟩
  haveI : Nonempty ι := ⟨j₀⟩
  set E : Finset ℂ := S.image (fun j => monoEig (lam j)) with hE
  have hrep : ∀ e ∈ E, ∃ j ∈ S, monoEig (lam j) = e := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact ⟨j, hj, rfl⟩
  choose! jOf hjOfS hjOf using hrep
  have hd : ∀ j ∈ S, ∃ m : ℤ, lam j - lam (jOf (monoEig (lam j))) = m := by
    intro j hj
    exact exists_int_of_monoEig_eq
      (hjOf _ (Finset.mem_image_of_mem _ hj)).symm
  choose! dInt hdInt using hd
  set M : ℕ := S.sup (fun j => (dInt j).natAbs) with hM
  set ρ : ℂ → ℂ := fun e => lam (jOf e) - M with hρ
  set n : ι → ℕ := fun j => (dInt j + M).toNat with hn
  have hlam : ∀ j ∈ S, lam j = ρ (monoEig (lam j)) + n j := by
    intro j hj
    have hle : (dInt j).natAbs ≤ M := Finset.le_sup (f := fun j => (dInt j).natAbs) hj
    have h0 : 0 ≤ dInt j + M := by omega
    have hcast : ((n j : ℕ) : ℂ) = ((dInt j : ℂ) + M) := by
      simp only [hn]
      have : (((dInt j + M).toNat : ℕ) : ℤ) = dInt j + M := Int.toNat_of_nonneg h0
      exact_mod_cast this
    rw [hcast]
    simp only [hρ]
    linear_combination hdInt j hj
  set q : ℂ → ℕ → ℂ[X] := fun e =>
    ∑ j ∈ S.filter (fun j => monoEig (lam j) = e), shiftIdx (n j) (p j) with hq
  have hmaps : ∀ j ∈ S, monoEig (lam j) ∈ E := fun j hj => Finset.mem_image_of_mem _ hj
  refine ⟨E, ρ, q, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [hρ, monoEig_sub_nat]
    exact hjOf e he
  · intro e _
    exact LogGood.sum _ fun j hj => (hp j (Finset.mem_filter.mp hj).1).shiftIdx _
  · intro t ht
    calc ∑ j ∈ S, logFun (lam j) (p j) t
        = ∑ j ∈ S, logFun (ρ (monoEig (lam j))) (shiftIdx (n j) (p j)) t := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hlam j hj, logFun_add_nat, ← hlam j hj]
      _ = ∑ e ∈ E, ∑ j ∈ S.filter (fun j => monoEig (lam j) = e),
            logFun (ρ (monoEig (lam j))) (shiftIdx (n j) (p j)) t :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ e ∈ E, logFun (ρ e) (q e) t := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hq]
          simp only
          rw [logFun_sum _ (fun j hj => (hp j (Finset.mem_filter.mp hj).1).shiftIdx _) _ ht]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2]
  · intro μ k
    calc ∑ j ∈ S, exCoeff (lam j) (p j) μ k
        = ∑ j ∈ S, exCoeff (ρ (monoEig (lam j))) (shiftIdx (n j) (p j)) μ k := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hlam j hj, exCoeff_add_nat, ← hlam j hj]
      _ = ∑ e ∈ E, ∑ j ∈ S.filter (fun j => monoEig (lam j) = e),
            exCoeff (ρ (monoEig (lam j))) (shiftIdx (n j) (p j)) μ k :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ e ∈ E, exCoeff (ρ e) (q e) μ k := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hq]
          simp only
          rw [exCoeff_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2]

/-! ## Uniqueness of coefficients -/

/-- **Uniqueness**: a finite sum of log-series vanishing on `Re t < 0` has all coefficients
zero. -/
theorem coeff_eq_zero_of_eval_eq_zero {ι : Type*} (S : Finset ι) (lam : ι → ℂ)
    (p : ι → ℕ → ℂ[X]) (hp : ∀ j ∈ S, LogGood (p j))
    (h : ∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p j) t = 0) :
    ∀ μ k, ∑ j ∈ S, exCoeff (lam j) (p j) μ k = 0 := by
  obtain ⟨E, ρ, q, hρ, hq, heval, hcoeff⟩ := exists_normalForm S lam p hp
  have hz := eq_zero_of_sum_logFun_eq_zero E ρ
    (fun i hi j hj hij => by rw [hρ i hi, hρ j hj]; exact hij) q hq
    (fun t ht => by rw [← heval t ht]; exact h t ht)
  intro μ k
  rw [hcoeff]
  exact Finset.sum_eq_zero fun e he => exCoeff_of_eq_zero (hz e he) μ k

/-- **Determination by coefficients**: a finite sum of log-series all of whose coefficients
vanish is identically zero on `Re t < 0`. -/
theorem eval_eq_zero_of_coeff_eq_zero {ι : Type*} (S : Finset ι) (lam : ι → ℂ)
    (p : ι → ℕ → ℂ[X]) (hp : ∀ j ∈ S, LogGood (p j))
    (h : ∀ μ k, ∑ j ∈ S, exCoeff (lam j) (p j) μ k = 0) :
    ∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p j) t = 0 := by
  classical
  obtain ⟨E, ρ, q, hρ, hq, heval, hcoeff⟩ := exists_normalForm S lam p hp
  have hzero : ∀ e ∈ E, ∀ m, q e m = 0 := by
    intro e he m
    ext k
    have h1 := h (ρ e + m) k
    rw [hcoeff, Finset.sum_eq_single_of_mem e he] at h1
    · rw [exCoeff_of_eq] at h1
      simpa using h1
    · intro e' he' hne
      refine exCoeff_of_forall_ne (fun m' hm' => hne ?_) _ _
      rw [← hρ e' he', ← hρ e he]
      exact monoEig_eq_of_add_nat_eq hm'
  intro t ht
  rw [heval t ht]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [logFun_congr (hzero e he)]
  exact logFun_zero _ _

/-- **Identity theorem**: a finite sum of log-series vanishing on a nonempty open subset of
`Re t < 0` vanishes on all of `Re t < 0`. -/
theorem eval_eq_zero_on_halfPlane {ι : Type*} (S : Finset ι) (lam : ι → ℂ)
    (p : ι → ℕ → ℂ[X]) (hp : ∀ j ∈ S, LogGood (p j)) {U : Set ℂ} (hU : IsOpen U)
    (hsub : U ⊆ halfPlane) {t₀ : ℂ} (ht₀ : t₀ ∈ U)
    (h : ∀ t ∈ U, ∑ j ∈ S, logFun (lam j) (p j) t = 0) :
    ∀ t ∈ halfPlane, ∑ j ∈ S, logFun (lam j) (p j) t = 0 := by
  set F : ℂ → ℂ := fun t => ∑ j ∈ S, logFun (lam j) (p j) t with hF
  have hd : DifferentiableOn ℂ F halfPlane := by
    have : DifferentiableOn ℂ (∑ j ∈ S, logFun (lam j) (p j)) halfPlane :=
      DifferentiableOn.sum fun j hj => differentiableOn_logFun (hp j hj) (lam j)
    refine this.congr fun t _ => ?_
    simp [hF]
  have han := hd.analyticOnNhd isOpen_halfPlane
  have hev : F =ᶠ[𝓝 t₀] 0 :=
    Filter.eventually_of_mem (hU.mem_nhds ht₀) fun t ht => h t ht
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_halfPlane
    (hsub ht₀) hev
  intro t ht
  exact this ht

/-! ## Expansions of functions -/

/-- A finite log-expansion datum `Σⱼ logFun (λⱼ) (pⱼ)`. -/
structure LogExp where
  /-- The index type. -/
  ι : Type
  /-- Finiteness. -/
  [fin : Fintype ι]
  /-- The exponents. -/
  lam : ι → ℂ
  /-- The log-series. -/
  p : ι → ℕ → ℂ[X]
  /-- Each series is good (bounded log-degree, subexponential coefficients). -/
  good : ∀ j, LogGood (p j)

attribute [instance] LogExp.fin

namespace LogExp

/-- The function `t ↦ Σⱼ logFun λⱼ pⱼ t`. -/
noncomputable def eval (E : LogExp) (t : ℂ) : ℂ := ∑ j, logFun (E.lam j) (E.p j) t

/-- The coefficient of `e^{μt} t^k`. -/
noncomputable def coeff (E : LogExp) (μ : ℂ) (k : ℕ) : ℂ := ∑ j, exCoeff (E.lam j) (E.p j) μ k

/-- One log-series. -/
def single (lam : ℂ) (p : ℕ → ℂ[X]) (hp : LogGood p) : LogExp where
  ι := Unit
  lam := fun _ => lam
  p := fun _ => p
  good := fun _ => hp

/-- The sum of two expansions. -/
def add (E E' : LogExp) : LogExp where
  ι := E.ι ⊕ E'.ι
  lam := Sum.elim E.lam E'.lam
  p := Sum.elim E.p E'.p
  good := fun j => by cases j <;> simp [E.good, E'.good]

/-- A scalar multiple. -/
noncomputable def smul (a : ℂ) (E : LogExp) : LogExp where
  ι := E.ι
  lam := E.lam
  p := fun j => a • E.p j
  good := fun j => (E.good j).smul a

theorem eval_single (lam : ℂ) (p : ℕ → ℂ[X]) (hp : LogGood p) (t : ℂ) :
    (single lam p hp).eval t = logFun lam p t := by
  simp [eval, single]

theorem coeff_single (lam : ℂ) (p : ℕ → ℂ[X]) (hp : LogGood p) (μ : ℂ) (k : ℕ) :
    (single lam p hp).coeff μ k = exCoeff lam p μ k := by
  simp [coeff, single]

theorem eval_add (E E' : LogExp) (t : ℂ) : (E.add E').eval t = E.eval t + E'.eval t := by
  change ∑ j : E.ι ⊕ E'.ι, logFun (Sum.elim E.lam E'.lam j) (Sum.elim E.p E'.p j) t = _
  rw [Fintype.sum_sum_type]; rfl

theorem coeff_add (E E' : LogExp) (μ : ℂ) (k : ℕ) :
    (E.add E').coeff μ k = E.coeff μ k + E'.coeff μ k := by
  change ∑ j : E.ι ⊕ E'.ι, exCoeff (Sum.elim E.lam E'.lam j) (Sum.elim E.p E'.p j) μ k = _
  rw [Fintype.sum_sum_type]; rfl

theorem eval_smul (a : ℂ) (E : LogExp) (t : ℂ) : (E.smul a).eval t = a * E.eval t := by
  simp only [eval, smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => logFun_smul a _ _ _

theorem coeff_smul (a : ℂ) (E : LogExp) (μ : ℂ) (k : ℕ) :
    (E.smul a).coeff μ k = a * E.coeff μ k := by
  simp only [coeff, smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => exCoeff_smul a _ _ _ _

/-- The difference datum `E − E'`, as a family over `E.ι ⊕ E'.ι`. -/
theorem sub_eval_coeff (E E' : LogExp) :
    (∀ t ∈ halfPlane, ∑ j : E.ι ⊕ E'.ι, logFun (Sum.elim E.lam E'.lam j)
        (Sum.elim E.p (fun i => -E'.p i) j) t = E.eval t - E'.eval t) ∧
    (∀ μ k, ∑ j : E.ι ⊕ E'.ι, exCoeff (Sum.elim E.lam E'.lam j)
        (Sum.elim E.p (fun i => -E'.p i) j) μ k = E.coeff μ k - E'.coeff μ k) := by
  refine ⟨fun t _ => ?_, fun μ k => ?_⟩
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, logFun_neg,
      Finset.sum_neg_distrib, eval]
    ring
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, exCoeff_neg,
      Finset.sum_neg_distrib, coeff]
    ring

/-- Two expansions agreeing on a nonempty open subset of `Re t < 0` have the same
coefficients. -/
theorem coeff_eq_of_eval_eq (E E' : LogExp) {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane)
    {t₀ : ℂ} (ht₀ : t₀ ∈ U) (h : ∀ t ∈ U, E.eval t = E'.eval t) (μ : ℂ) (k : ℕ) :
    E.coeff μ k = E'.coeff μ k := by
  obtain ⟨hev, hco⟩ := sub_eval_coeff E E'
  have hgood : ∀ j ∈ (Finset.univ : Finset (E.ι ⊕ E'.ι)),
      LogGood (Sum.elim E.p (fun i => -E'.p i) j) := by
    intro j _; cases j with
    | inl j => exact E.good j
    | inr j => exact (E'.good j).neg
  have hzU : ∀ t ∈ U, ∑ j : E.ι ⊕ E'.ι, logFun (Sum.elim E.lam E'.lam j)
      (Sum.elim E.p (fun i => -E'.p i) j) t = 0 := by
    intro t ht; rw [hev t (hsub ht), h t ht, sub_self]
  have hz := eval_eq_zero_on_halfPlane _ _ _ hgood hU hsub ht₀ hzU
  have := coeff_eq_zero_of_eval_eq_zero _ _ _ hgood hz μ k
  rw [hco] at this
  exact sub_eq_zero.mp this

/-- Two expansions with the same coefficients agree on `Re t < 0`. -/
theorem eval_eq_of_coeff_eq (E E' : LogExp) (h : ∀ μ k, E.coeff μ k = E'.coeff μ k) :
    ∀ t ∈ halfPlane, E.eval t = E'.eval t := by
  obtain ⟨hev, hco⟩ := sub_eval_coeff E E'
  have hgood : ∀ j ∈ (Finset.univ : Finset (E.ι ⊕ E'.ι)),
      LogGood (Sum.elim E.p (fun i => -E'.p i) j) := by
    intro j _; cases j with
    | inl j => exact E.good j
    | inr j => exact (E'.good j).neg
  have hz := eval_eq_zero_of_coeff_eq_zero _ _ _ hgood
    (fun μ k => by rw [hco, h, sub_self])
  intro t ht
  have := hz t ht
  rw [hev t ht] at this
  exact sub_eq_zero.mp this

end LogExp

/-- `E` is an expansion of `F` on `U`. -/
def IsExpOn (U : Set ℂ) (F : ℂ → ℂ) (E : LogExp) : Prop := ∀ t ∈ U, F t = E.eval t

/-- `F` has a finite log-expansion on `U`. -/
def HasLogExp (U : Set ℂ) (F : ℂ → ℂ) : Prop := ∃ E : LogExp, IsExpOn U F E

/-- **The coefficient of `y^μ (log y)^k` of a function** with a finite log-expansion on `U`
(junk value `0` otherwise).  Well defined on nonempty open `U ⊆ {Re t < 0}` (`logCoeff_eq`). -/
noncomputable def logCoeff (U : Set ℂ) (F : ℂ → ℂ) (μ : ℂ) (k : ℕ) : ℂ := by
  classical
  exact if h : HasLogExp U F then h.choose.coeff μ k else 0

/-- **The coefficients do not depend on the expansion.** -/
theorem logCoeff_eq {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} {E : LogExp} (hE : IsExpOn U F E) (μ : ℂ) (k : ℕ) :
    logCoeff U F μ k = E.coeff μ k := by
  have h : HasLogExp U F := ⟨E, hE⟩
  unfold logCoeff
  rw [dif_pos h]
  obtain ⟨t₀, ht₀⟩ := hne
  exact LogExp.coeff_eq_of_eval_eq _ _ hU hsub ht₀
    (fun t ht => by rw [← h.choose_spec t ht, hE t ht]) μ k

theorem hasLogExp_add {U : Set ℂ} {F G : ℂ → ℂ} (hF : HasLogExp U F) (hG : HasLogExp U G) :
    HasLogExp U (F + G) := by
  obtain ⟨E, hE⟩ := hF
  obtain ⟨E', hE'⟩ := hG
  exact ⟨E.add E', fun t ht => by rw [LogExp.eval_add, ← hE t ht, ← hE' t ht]; rfl⟩

theorem hasLogExp_smul {U : Set ℂ} {F : ℂ → ℂ} (a : ℂ) (hF : HasLogExp U F) :
    HasLogExp U (fun t => a * F t) := by
  obtain ⟨E, hE⟩ := hF
  exact ⟨E.smul a, fun t ht => by rw [LogExp.eval_smul, ← hE t ht]⟩

theorem logCoeff_add {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F G : ℂ → ℂ} (hF : HasLogExp U F) (hG : HasLogExp U G) (μ : ℂ) (k : ℕ) :
    logCoeff U (F + G) μ k = logCoeff U F μ k + logCoeff U G μ k := by
  obtain ⟨E, hE⟩ := hF
  obtain ⟨E', hE'⟩ := hG
  have hS : IsExpOn U (F + G) (E.add E') :=
    fun t ht => by rw [LogExp.eval_add, ← hE t ht, ← hE' t ht]; rfl
  rw [logCoeff_eq hU hsub hne hS, logCoeff_eq hU hsub hne hE, logCoeff_eq hU hsub hne hE',
    LogExp.coeff_add]

theorem logCoeff_smul {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} (a : ℂ) (hF : HasLogExp U F) (μ : ℂ) (k : ℕ) :
    logCoeff U (fun t => a * F t) μ k = a * logCoeff U F μ k := by
  obtain ⟨E, hE⟩ := hF
  have hS : IsExpOn U (fun t => a * F t) (E.smul a) :=
    fun t ht => by rw [LogExp.eval_smul, ← hE t ht]
  rw [logCoeff_eq hU hsub hne hS, logCoeff_eq hU hsub hne hE, LogExp.coeff_smul]

/-- The coefficients of one log-series. -/
theorem logCoeff_logFun {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane) (hne : U.Nonempty)
    {F : ℂ → ℂ} {lam : ℂ} {p : ℕ → ℂ[X]} (hp : LogGood p) (hF : ∀ t ∈ U, F t = logFun lam p t)
    (μ : ℂ) (k : ℕ) : logCoeff U F μ k = exCoeff lam p μ k := by
  have hS : IsExpOn U F (LogExp.single lam p hp) :=
    fun t ht => by rw [LogExp.eval_single, hF t ht]
  rw [logCoeff_eq hU hsub hne hS, LogExp.coeff_single]

/-- **Functions with finite log-expansions and the same coefficients agree** on `U`. -/
theorem eqOn_of_logCoeff_eq {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ halfPlane)
    (hne : U.Nonempty) {F G : ℂ → ℂ} (hF : HasLogExp U F) (hG : HasLogExp U G)
    (h : ∀ μ k, logCoeff U F μ k = logCoeff U G μ k) : ∀ t ∈ U, F t = G t := by
  obtain ⟨E, hE⟩ := hF
  obtain ⟨E', hE'⟩ := hG
  have hc : ∀ μ k, E.coeff μ k = E'.coeff μ k := fun μ k => by
    rw [← logCoeff_eq hU hsub hne hE, ← logCoeff_eq hU hsub hne hE', h]
  intro t ht
  rw [hE t ht, hE' t ht]
  exact LogExp.eval_eq_of_coeff_eq E E' hc t (hsub ht)

end VOA.Huang.LogRemovalCoeff

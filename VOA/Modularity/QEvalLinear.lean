/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.EisensteinAnalytic
import VOA.Modularity.QEvalConv

/-!
# `qEvalC` is linear where it converges

`Modularity.QEvalHolomorphic` evaluates a formal `q`-series as a holomorphic function; but
`qEvalC` is a `tsum`, so **additivity is not free** — it holds exactly where the defining series
converge.  Zhu's block conditions are equalities between *sums* of `q`-series, so transporting them
to the analytic side needs precisely this bookkeeping, collected here once:

* `summable_qTerm`, `summable_qTerm_qDeriv`, `summable_qTerm_qConv` — the three summability facts
  (the last is the Cauchy product, `summable_norm_sum_mul_range_of_summable_norm`);
* `qEvalC_add`, `qEvalC_smul`, `qEvalC_zero`, `qEvalC_sum`, `qEvalC_finsum` — linearity;
* `qEvalC_qDeriv` — `qEvalC (qDeriv χ) h z = (2πi)⁻¹·(d/dz) qEvalC χ h z`, the `deriv_qEvalC`
  bridge in the form Zhu's condition (iii) wants.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators

/-! ## Summability of the defining series -/

/-- The bare summability of the `q`-series at a point of `ℍ`. -/
theorem summable_qTerm (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable (fun n : ℕ => qTerm χ h n z) := by
  have hz0 : (0 : ℝ) < z.im := hz
  have hc : 0 < z.im / 2 := by linarith
  have hzc : z ∈ imGT (z.im / 2) := by show z.im / 2 < z.im; linarith
  refine (summable_pow_mul_qTerm χ h hsub hc hzc 0).congr (fun n => ?_)
  simp

theorem summable_norm_qTerm (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable (fun n : ℕ => ‖qTerm χ h n z‖) :=
  summable_norm_iff.mpr (summable_qTerm χ h hsub hz)

/-- The `q`-series of the formal Euler derivative is summable. -/
theorem summable_qTerm_qDeriv (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable (fun n : ℕ => qTerm (qDeriv χ) h n z) := by
  have hz0 : (0 : ℝ) < z.im := hz
  have hc : 0 < z.im / 2 := by linarith
  have hzc : z ∈ imGT (z.im / 2) := by show z.im / 2 < z.im; linarith
  have h0 := summable_pow_mul_qTerm χ h hsub hc hzc 0
  have h1 := summable_pow_mul_qTerm χ h hsub hc hzc 1
  have h0' : Summable (fun n : ℕ => qTerm χ h n z) := h0.congr (fun n => by simp)
  have h1' : Summable (fun n : ℕ => (n : ℂ) * qTerm χ h n z) := h1.congr (fun n => by simp)
  refine ((h0'.mul_left h).add h1').congr (fun n => ?_)
  rw [qTerm, qTerm, qDeriv]
  ring

/-! ## Linearity -/

@[simp] theorem qEvalC_zero (h : ℂ) (z : ℂ) : qEvalC 0 h z = 0 := by
  rw [qEvalC, qSeriesC]
  have : ∀ n : ℕ, qTerm (0 : FormalQSeries) h n z = 0 := by
    intro n; rw [qTerm]; simp
  rw [tsum_congr this, tsum_zero, mul_zero]

theorem qEvalC_add (χ₁ χ₂ : FormalQSeries) (h : ℂ) {z : ℂ}
    (h₁ : Summable (fun n : ℕ => qTerm χ₁ h n z))
    (h₂ : Summable (fun n : ℕ => qTerm χ₂ h n z)) :
    qEvalC (χ₁ + χ₂) h z = qEvalC χ₁ h z + qEvalC χ₂ h z := by
  have hterm : ∀ n : ℕ, qTerm (χ₁ + χ₂) h n z = qTerm χ₁ h n z + qTerm χ₂ h n z := by
    intro n
    rw [qTerm, qTerm, qTerm]
    show (χ₁ (h + (n : ℂ)) + χ₂ (h + (n : ℂ))) * _ = _
    ring
  rw [qEvalC, qEvalC, qEvalC, qSeriesC, qSeriesC, qSeriesC, tsum_congr hterm, h₁.tsum_add h₂]
  ring

theorem qEvalC_smul (c : ℂ) (χ : FormalQSeries) (h : ℂ) (z : ℂ) :
    qEvalC (c • χ) h z = c * qEvalC χ h z := by
  have hterm : ∀ n : ℕ, qTerm (c • χ) h n z = c * qTerm χ h n z := by
    intro n
    rw [qTerm, qTerm]
    show (c * χ (h + (n : ℂ))) * _ = _
    ring
  rw [qEvalC, qEvalC, qSeriesC, qSeriesC, tsum_congr hterm, tsum_mul_left]
  ring

theorem summable_qTerm_finset {ι : Type*} (s : Finset ι) (g : ι → FormalQSeries) (h : ℂ) (z : ℂ)
    (hsum : ∀ i ∈ s, Summable (fun n : ℕ => qTerm (g i) h n z)) :
    Summable (fun n : ℕ => qTerm (∑ i ∈ s, g i) h n z) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hz : ∀ n : ℕ, qTerm (∑ i ∈ (∅ : Finset ι), g i) h n z = 0 := by
        intro n; rw [qTerm]; simp
      exact summable_zero.congr (fun n => (hz n).symm)
  | insert a s ha ih =>
      have hstep : ∀ n : ℕ, qTerm (∑ i ∈ insert a s, g i) h n z
          = qTerm (g a) h n z + qTerm (∑ i ∈ s, g i) h n z := by
        intro n
        rw [Finset.sum_insert ha, qTerm, qTerm, qTerm]
        show ((g a + ∑ i ∈ s, g i) (h + (n : ℂ))) * _ = _
        rw [Pi.add_apply]
        ring
      exact ((hsum a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hsum i (Finset.mem_insert_of_mem hi)))).congr (fun n => (hstep n).symm)

theorem qEvalC_sum {ι : Type*} (s : Finset ι) (g : ι → FormalQSeries) (h : ℂ) {z : ℂ}
    (hsum : ∀ i ∈ s, Summable (fun n : ℕ => qTerm (g i) h n z)) :
    qEvalC (∑ i ∈ s, g i) h z = ∑ i ∈ s, qEvalC (g i) h z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        qEvalC_add _ _ _ (hsum a (Finset.mem_insert_self a s))
          (summable_qTerm_finset s g h z (fun i hi => hsum i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hsum i (Finset.mem_insert_of_mem hi))]

/-- **`qEvalC` commutes with a finitely-supported `finsum`** — the shape Zhu's recursion
produces. -/
theorem qEvalC_finsum {ι : Type*} (g : ι → FormalQSeries) (h : ℂ) {z : ℂ}
    (hfin : (Function.support g).Finite)
    (hsum : ∀ i, Summable (fun n : ℕ => qTerm (g i) h n z)) :
    qEvalC (∑ᶠ i, g i) h z = ∑ᶠ i, qEvalC (g i) h z := by
  classical
  have hs : Function.support g ⊆ (hfin.toFinset : Set ι) := by
    intro i hi; simpa using hi
  have hs2 : (Function.support fun i => qEvalC (g i) h z) ⊆ (hfin.toFinset : Set ι) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq]
    intro h0
    exact hi (by rw [h0]; exact qEvalC_zero h z)
  rw [finsum_eq_finsetSum_of_support_subset _ hs, finsum_eq_finsetSum_of_support_subset _ hs2,
    qEvalC_sum]
  exact fun i _ => hsum i

/-! ## The Euler derivative -/

/-- **`q d/dq` becomes `(2πi)⁻¹ d/dz`.**  The `deriv_qEvalC` bridge, solved for the formal side —
this is how Zhu's condition (iii) turns into a differential equation. -/
theorem qEvalC_qDeriv (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + (n : ℂ))‖)) {z : ℂ} (hz : z ∈ imGT 0) :
    qEvalC (qDeriv χ) h z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (qEvalC χ h) z := by
  rw [deriv_qEvalC χ h hsub hz, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-! ## The convolution -/

/-- The Cauchy product of two absolutely convergent `q`-series is summable. -/
theorem summable_qTerm_qConv (f : ℕ → ℂ) (χ : FormalQSeries) (h : ℂ) {z : ℂ}
    (hsupp : ∀ i : ℤ, i < 0 → χ (h + (i : ℂ)) = 0)
    (hf : Summable fun n : ℕ => ‖f n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖)
    (hχ : Summable fun n : ℕ => ‖qTerm χ h n z‖) :
    Summable (fun n : ℕ => qTerm (qConv f χ) h n z) := by
  classical
  have hcauchy := summable_norm_sum_mul_range_of_summable_norm hf hχ
  refine summable_norm_iff.mp (hcauchy.congr (fun m => ?_))
  congr 1
  symm
  rw [qTerm, qConv_apply_of_support f χ h hsupp m, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_range] at hn
  have hle : n ≤ m := by omega
  rw [qTerm]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m - n : ℕ) : ℕ) : ℂ) * z)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * z) := by
    rw [← Complex.exp_add]
    congr 1
    have hc : ((m - n : ℕ) : ℂ) = (m : ℂ) - (n : ℂ) := by
      push_cast [Nat.cast_sub hle]; ring
    rw [hc]; ring
  rw [← hexp]
  ring

end VOA

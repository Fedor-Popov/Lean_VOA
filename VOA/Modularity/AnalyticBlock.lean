/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QEvalLinear

/-!
# Zhu's block conditions on the analytic side

`Modularity.ZhuBlockConditions` proves that the trace functions of a module satisfy Zhu's three
genus-one block conditions as identities of **formal** `q`-series
(`torusOnePointHom_isFormalBlock`).  This file transports them along the dictionary

* `Modularity.QEvalHolomorphic.deriv_qEvalC`  — `q d/dq ↦ (2πi)⁻¹ d/dz`,
* `Modularity.QEvalConv.qEvalC_qConv`         — `⋆ ↦ ·`,
* `Modularity.EisensteinAnalytic.zhuGC`       — the coefficient family `↦` an Eisenstein function,

into identities between **honest holomorphic functions** on the upper half-plane:

  `isAnalyticBlock_of_isFormalBlock`.

## The analytic conditions (`IsAnalyticBlock`)

For `F : 𝒱 → (ℂ → ℂ)`, holomorphic on `imGT 0`, linear in `v`:

* (i)   `F(a[0]v) = 0`;
* (ii)  `F(a[−2]v)(z) + Σ_{k≥1}(2k−1)·G_{2k}(z)·F(a[2k−2]v)(z) = 0`;
* (iii) `F(L[−2]v)(z) = (2πi)⁻¹·F(v)′(z) + Σ_{k≥1} G_{2k}(z)·F(L[2k−2]v)(z)`.

`Modularity.BlockSlash` then shows these are `SL₂(ℤ)`-covariant.

## Convention

`F v` is *extended by zero* off `imGT 0` (`Set.indicator`).  That is what makes linearity in `v`
hold **unconditionally** — a `tsum` outside its half-plane of convergence is a junk value — while
changing nothing on `imGT 0`, which is open, so `deriv` is unaffected (`anEval_deriv`).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Two named growth/support data are consumed
(`OnePointSupported`, derived from `HasConformalWeight`; `OnePointSubexp`, the general-`v`
strengthening of `Modularity.ConvergenceBridge.SubexponentialCoeffs`).
-/

namespace VOA

open Complex
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Eventual vanishing of the square-bracket tails -/

section Tails

variable {W : VertexOperatorAlgebra 𝒱}

/-- `L[2k−2]v = 0` for all large `k` — the `ω`-case of `vSqZ_eventually_zero`. -/
theorem Lsq_tail_eventually_zero (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → Lsq W (2 * (m + 1) - 2 : ℤ) v = 0 := by
  obtain ⟨Nb, hNb⟩ := vSqZ_eventually_zero W W.conformalVector 2 v
  refine ⟨Nb.toNat, fun m hm => ?_⟩
  have hodd : Lsq W (2 * (m + 1) - 2 : ℤ) v
      = vSqZ W W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) v := by
    rw [Lsq_apply, show (2 * ((m : ℤ) + 1) - 2 : ℤ) + 1 = 2 * ((m : ℤ) + 1) - 1 from by ring,
      sqBracketCoeffZ_vacuum_of_ne _ (by omega), mul_zero, zero_smul, sub_zero]
  rw [hodd, hNb _ (by omega)]

/-- `a[2k−2]v = 0` for all large `k`. -/
theorem vSqZ_tail_eventually_zero (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (ka : ℕ) (v : 𝒱) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v = 0 := by
  obtain ⟨Nb, hNb⟩ := vSqZ_eventually_zero W a ka v
  exact ⟨Nb.toNat, fun m hm => hNb _ (by omega)⟩

end Tails

/-! ## The support and growth data -/

section Data

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The support datum**: the one-point functions of `N` live in degrees `h + ℕ`. -/
def OnePointSupported (N : OrdVModule W M) (h : ℂ) : Prop :=
  ∀ (v : 𝒱) (i : ℤ), i < 0 → torusOnePoint N v (h + (i : ℂ)) = 0

/-- **The growth datum**, for *every* `v` — the general-`v` strengthening of
`Modularity.ConvergenceBridge.SubexponentialCoeffs` (which is the case `v = 𝟙`). -/
def OnePointSubexp (N : OrdVModule W M) (h : ℂ) : Prop :=
  ∀ v : 𝒱, Subexponential (fun n : ℕ => ‖torusOnePoint N v (h + (n : ℂ))‖)

/-- **The support datum is free from the conformal weight.**  A module with conformal weight `h`
has no weight spaces below `h`, so every graded trace vanishes in degrees `< h − c/24`. -/
theorem onePointSupported_of_hasConformalWeight (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) :
    OnePointSupported N (hw - W.centralCharge / 24) := by
  intro v i hi
  refine gradedTraceOp_eq_zero_of_weight_bot N (oMod N v) _ ?_
  by_contra hbot
  obtain ⟨n, hn⟩ := hcw.2 _ hbot
  have hcast : ((i : ℤ) : ℂ) = ((n : ℕ) : ℂ) := by
    have : hw - W.centralCharge / 24 + (i : ℂ) + W.centralCharge / 24 = hw + (n : ℂ) := hn
    linear_combination this
  have : (i : ℤ) = (n : ℤ) := by exact_mod_cast hcast
  omega

end Data

/-! ## The analytic evaluation -/

section AnEval

variable {W : VertexOperatorAlgebra 𝒱}

/-- The analytic evaluation of a formal family, extended by zero off the upper half-plane. -/
noncomputable def anEval (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) (v : 𝒱) : ℂ → ℂ :=
  Set.indicator (imGT 0) (qEvalC (S v) h)

theorem anEval_of_mem (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    anEval S h v z = qEvalC (S v) h z := Set.indicator_of_mem hz _

theorem anEval_eventuallyEq (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) (v : 𝒱) {z : ℂ}
    (hz : z ∈ imGT 0) : anEval S h v =ᶠ[nhds z] qEvalC (S v) h := by
  filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw using anEval_of_mem S h v hw

theorem anEval_deriv (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (anEval S h v) z = _root_.deriv (qEvalC (S v) h) z :=
  Filter.EventuallyEq.deriv_eq (anEval_eventuallyEq S h v hz)

@[simp] theorem anEval_zero (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) : anEval S h 0 = 0 := by
  funext z
  rw [anEval, map_zero]
  by_cases hz : z ∈ imGT 0
  · rw [Set.indicator_of_mem hz, qEvalC_zero]; rfl
  · rw [Set.indicator_of_notMem hz]; rfl

theorem anEval_smul (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ) (c : ℂ) (v : 𝒱) (z : ℂ) :
    anEval S h (c • v) z = c * anEval S h v z := by
  by_cases hz : z ∈ imGT 0
  · rw [anEval_of_mem _ _ _ hz, anEval_of_mem _ _ _ hz, map_smul, qEvalC_smul]
  · rw [anEval, anEval, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

end AnEval

/-! ## The analytic block conditions -/

/-- **Zhu's genus-one conformal-block conditions, analytically** — for a family of
holomorphic functions on the upper half-plane, with the Eisenstein *functions* `zhuGC` in place of
the formal convolution. -/
structure IsAnalyticBlock (W : VertexOperatorAlgebra 𝒱) (F : 𝒱 → ℂ → ℂ) : Prop where
  /-- Each `F v` is holomorphic on the upper half-plane. -/
  holo : ∀ v : 𝒱, DifferentiableOn ℂ (F v) (imGT 0)
  /-- Linearity in `v`. -/
  addv : ∀ (v w : 𝒱) (z : ℂ), F (v + w) z = F v z + F w z
  /-- Homogeneity in `v`. -/
  smulv : ∀ (c : ℂ) (v : 𝒱) (z : ℂ), F (c • v) z = c * F v z
  /-- (i) `F(a[0]v) = 0`. -/
  vanish : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, F (vSqZ W a ka 0 v) = 0
  /-- (ii) Zhu's `[−2]`-identity. -/
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (v : 𝒱), ∀ z ∈ imGT 0,
    F (vSqZ W a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z) = 0
  /-- (iii) The `ω`-recursion — the seed of the modular differential equation. -/
  omega : ∀ (v : 𝒱), ∀ z ∈ imGT 0,
    F (Lsq W (-2) v) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z

theorem IsAnalyticBlock.zerov {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}
    (hF : IsAnalyticBlock W F) (z : ℂ) : F 0 z = 0 := by
  have h := hF.smulv 0 0 z
  rw [zero_smul, zero_mul] at h
  exact h

/-! ## The transport -/

section Transport

variable {W : VertexOperatorAlgebra 𝒱}

/-- The single-term transport: `qEvalC` of a Zhu convolution is multiplication by `zhuGC`. -/
theorem qEvalC_qConv_zhuG (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ)
    (hsupp : ∀ (v : 𝒱) (i : ℤ), i < 0 → S v (h + (i : ℂ)) = 0)
    (hsub : ∀ v : 𝒱, Subexponential (fun n : ℕ => ‖S v (h + (n : ℂ))‖))
    (j : ℕ) (w : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    qEvalC (qConv (zhuG j) (S w)) h z = zhuGC j z * qEvalC (S w) h z :=
  qEvalC_qConv (zhuG j) (S w) h (hsupp w) (summable_norm_zhuG_qexp j hz)
    (summable_norm_qTerm (S w) h (hsub w) hz)

theorem summable_qTerm_qConv_zhuG (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ)
    (hsupp : ∀ (v : 𝒱) (i : ℤ), i < 0 → S v (h + (i : ℂ)) = 0)
    (hsub : ∀ v : 𝒱, Subexponential (fun n : ℕ => ‖S v (h + (n : ℂ))‖))
    (j : ℕ) (w : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable (fun n : ℕ => qTerm (qConv (zhuG j) (S w)) h n z) :=
  summable_qTerm_qConv (zhuG j) (S w) h (hsupp w) (summable_norm_zhuG_qexp j hz)
    (summable_norm_qTerm (S w) h (hsub w) hz)

/-- **The transport.**  A formal genus-one block whose coefficients are supported in
`h + ℕ` and grow subexponentially evaluates to an **analytic** genus-one block. -/
theorem isAnalyticBlock_of_isFormalBlock (S : 𝒱 →ₗ[ℂ] FormalQSeries) (h : ℂ)
    (hsupp : ∀ (v : 𝒱) (i : ℤ), i < 0 → S v (h + (i : ℂ)) = 0)
    (hsub : ∀ v : 𝒱, Subexponential (fun n : ℕ => ‖S v (h + (n : ℂ))‖))
    (hS : IsFormalBlock W S) :
    IsAnalyticBlock W (anEval S h) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- holomorphy
    intro v z hz
    have hd : DifferentiableAt ℂ (qEvalC (S v) h) z := by
      have hz0 : (0 : ℝ) < z.im := hz
      have hc : 0 < z.im / 2 := by linarith
      have hzc : z ∈ imGT (z.im / 2) := by show z.im / 2 < z.im; linarith
      exact (hasDerivAt_qEvalC (S v) h (hsub v) hc hzc).differentiableAt
    exact ((hd.congr_of_eventuallyEq
      (anEval_eventuallyEq S h v hz)).differentiableWithinAt)
  · -- additivity
    intro v w z
    by_cases hz : z ∈ imGT 0
    · rw [anEval_of_mem _ _ _ hz, anEval_of_mem _ _ _ hz, anEval_of_mem _ _ _ hz, map_add,
        qEvalC_add _ _ _ (summable_qTerm (S v) h (hsub v) hz) (summable_qTerm (S w) h (hsub w) hz)]
    · rw [anEval, anEval, anEval, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
        Set.indicator_of_notMem hz, add_zero]
  · exact anEval_smul S h
  · -- (i)
    intro ka hka a ha v
    funext z
    rw [anEval, hS.vanish ka hka a ha v]
    by_cases hz : z ∈ imGT 0
    · rw [Set.indicator_of_mem hz, qEvalC_zero]; rfl
    · rw [Set.indicator_of_notMem hz]; rfl
  · -- (ii)
    intro ka hka a ha v z hz
    obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a ka v
    have hfin : (Function.support fun m : ℕ => ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v))).Finite := by
      refine Set.Finite.subset (Set.finite_Iio K) (fun m hm => ?_)
      simp only [Function.mem_support, ne_eq] at hm
      simp only [Set.mem_Iio]
      by_contra hc
      push_neg at hc
      exact hm (by rw [hK m hc, map_zero, qConv_zero_right, smul_zero])
    have hlaw := hS.negTwo ka hka a ha v
    have hsum1 : Summable (fun n : ℕ => qTerm (S (vSqZ W a ka (-2) v)) h n z) :=
      summable_qTerm _ h (hsub _) hz
    have hsum2 : ∀ m : ℕ, Summable (fun n : ℕ => qTerm (((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      intro m
      refine ((summable_qTerm_qConv_zhuG S h hsupp hsub (m + 1)
        (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) hz).mul_left
        (((2 * (m + 1) - 1 : ℕ) : ℂ))).congr (fun n => ?_)
      rw [qTerm, qTerm, Pi.smul_apply, smul_eq_mul]
      ring
    have hsumfin : Summable (fun n : ℕ => qTerm (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      have hs : Function.support (fun m : ℕ => ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)))
          ⊆ (hfin.toFinset : Set ℕ) := by intro m hm; simpa using hm
      rw [finsum_eq_finsetSum_of_support_subset _ hs]
      exact summable_qTerm_finset _ _ h z (fun m _ => hsum2 m)
    have hev := congrArg (fun χ : FormalQSeries => qEvalC χ h z) hlaw
    simp only at hev
    rw [qEvalC_add _ _ _ hsum1 hsumfin, qEvalC_zero,
      qEvalC_finsum _ h hfin hsum2] at hev
    rw [anEval_of_mem _ _ _ hz, ← hev]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [qEvalC_smul, qEvalC_qConv_zhuG S h hsupp hsub (m + 1)
      (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) hz, anEval_of_mem _ _ _ hz]
  · -- (iii)
    intro v z hz
    obtain ⟨K, hK⟩ := Lsq_tail_eventually_zero W v
    have hfin : (Function.support fun m : ℕ =>
        qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v))).Finite := by
      refine Set.Finite.subset (Set.finite_Iio K) (fun m hm => ?_)
      simp only [Function.mem_support, ne_eq] at hm
      simp only [Set.mem_Iio]
      by_contra hc
      push_neg at hc
      exact hm (by rw [hK m hc, map_zero, qConv_zero_right])
    have hlaw := hS.omega v
    have hsumD : Summable (fun n : ℕ => qTerm (qDeriv (S v)) h n z) :=
      summable_qTerm_qDeriv (S v) h (hsub v) hz
    have hsum2 : ∀ m : ℕ, Summable (fun n : ℕ =>
        qTerm (qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v))) h n z) :=
      fun m => summable_qTerm_qConv_zhuG S h hsupp hsub (m + 1)
        (Lsq W (2 * (m + 1) - 2 : ℤ) v) hz
    have hsumfin : Summable (fun n : ℕ => qTerm (∑ᶠ m : ℕ,
        qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      have hs : Function.support (fun m : ℕ =>
          qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v)))
          ⊆ (hfin.toFinset : Set ℕ) := by intro m hm; simpa using hm
      rw [finsum_eq_finsetSum_of_support_subset _ hs]
      exact summable_qTerm_finset _ _ h z (fun m _ => hsum2 m)
    have hev := congrArg (fun χ : FormalQSeries => qEvalC χ h z) hlaw
    simp only at hev
    rw [qEvalC_add _ _ _ hsumD hsumfin, qEvalC_qDeriv (S v) h (hsub v) hz,
      qEvalC_finsum _ h hfin hsum2] at hev
    rw [anEval_of_mem _ _ _ hz, hev, anEval_deriv S h v hz]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [qEvalC_qConv_zhuG S h hsupp hsub (m + 1) (Lsq W (2 * (m + 1) - 2 : ℤ) v) hz,
      anEval_of_mem _ _ _ hz]

end Transport

/-! ## The trace functions of a module -/

section Trace

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The trace functions of a module are analytic genus-one blocks** (Zhu Thm 5.3.1) —
given the support and growth data. -/
theorem torusOnePoint_isAnalyticBlock (N : OrdVModule W M) (h : ℂ)
    (hsupp : OnePointSupported N h) (hsub : OnePointSubexp N h) :
    IsAnalyticBlock W (anEval (torusOnePointHom N) h) :=
  isAnalyticBlock_of_isFormalBlock (torusOnePointHom N) h hsupp hsub
    (torusOnePointHom_isFormalBlock N)

end Trace

end VOA

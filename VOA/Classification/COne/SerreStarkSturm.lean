/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkCusp
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Serre–Stark, stage S2-2: a Sturm bound and finite dimensionality for θ-type forms

* `thetaTypeCoeff f n`: the `n`-th `q`-expansion coefficient; `IsThetaTypeForm.hasSum_coeff`;
* `IsThetaTypeForm.eq_zero_of_coeff_lt`: **Sturm bound.** For `4 ∣ N`, a θ-type form of level `N`
  whose first `sturmBound N` coefficients vanish is zero on `ℍ`. Proof: `F = f θ` is a weight-one
  form for `Γ₁(N)` (`weightOneForm`); its norm to `SL₂(ℤ)` (Mathlib `ModularForm.norm`) is a
  level-one form of weight `[SL₂(ℤ) : Γ₁(N)]`, of size `O(e^{-2πBy})`; the coefficient integral
  kills its first `B` coefficients and `sturm_bound_levelOne` kills it; then `F = 0`.
* `thetaTypeSpace N`: the θ-type forms as functions on `ℍ` (an `IsThetaTypeForm` is unconstrained
  for `Im τ ≤ 0`, so `IsThetaTypeForm.submodule` itself is infinite-dimensional);
  `finrank_thetaTypeSpace_le`, `finiteDimensional_thetaTypeSpace`.
-/

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos ofComplex_apply_of_im_nonpos qExpansion
  IsBoundedAtImInfty isBoundedAtImInfty_iff hasSum_qExpansion cuspFunction
  analyticAt_cuspFunction_zero qExpansion_coeff_unique)
open scoped MatrixGroups ModularForm Manifold UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

/-! ## Coefficients -/

/-- The `n`-th `q`-expansion coefficient of a function on the upper half plane. -/
def thetaTypeCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 (fun τ : ℍ => f τ)).coeff n

namespace IsThetaTypeForm

variable {N : ℕ} {f g : ℂ → ℂ}

theorem periodic (hf : IsThetaTypeForm N f) :
    Function.Periodic ((fun τ : ℍ => f τ) ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  intro w
  change f (ofComplex (w + ((1 : ℝ) : ℂ))) = f (ofComplex w)
  rw [Complex.ofReal_one]
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    exact hf.add_one hw
  · have hw' : (w + 1).im ≤ 0 := by simpa using hw
    rw [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

theorem mdiff (hf : IsThetaTypeForm N f) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine hf.holo.congr fun z hz => ?_
  simp [ofComplex_apply_of_im_pos hz]

theorem bdd (hf : IsThetaTypeForm N f) : IsBoundedAtImInfty (fun τ : ℍ => f τ) := by
  rw [isBoundedAtImInfty_iff]
  obtain ⟨C, hC⟩ := hf.bounded
  exact ⟨C, 1, fun z hz => hC z hz⟩

theorem analyticAt (hf : IsThetaTypeForm N f) :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ => f τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos hf.periodic hf.mdiff hf.bdd

theorem qParam_one_pow (τ : ℍ) (n : ℕ) :
    Function.Periodic.qParam 1 (τ : ℂ) ^ n = cexp (2 * Real.pi * I * n * τ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **q-expansion with the canonical coefficients.** -/
theorem hasSum_coeff (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * τ)) (f τ) := by
  have h := hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bdd ⟨τ, hτ⟩
  simp only [smul_eq_mul] at h
  have e : ∀ n : ℕ, Function.Periodic.qParam 1 ((⟨τ, hτ⟩ : ℍ) : ℂ) ^ n =
      cexp (2 * Real.pi * I * n * τ) := fun n => qParam_one_pow ⟨τ, hτ⟩ n
  simp only [e] at h
  exact h

/-- Coefficients are determined by any `q`-expansion. -/
theorem coeff_eq_of_hasSum (hf : IsThetaTypeForm N f) {c : ℕ → ℂ}
    (hc : ∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ => c n * cexp (2 * Real.pi * I * n * τ)) (f τ))
    (n : ℕ) : thetaTypeCoeff f n = c n := by
  have hs : ∀ τ : ℍ, HasSum (fun m : ℕ => c m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      ((fun τ : ℍ => f τ) τ) := by
    intro τ
    have e : ∀ m : ℕ, c m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m =
        c m * cexp (2 * Real.pi * I * m * τ) := fun m => by
      rw [smul_eq_mul, qParam_one_pow]
    simp only [e]
    exact hc τ τ.2
  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hf.analyticAt
    hs).hasFPowerSeriesAt
  have h2 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hf.analyticAt
    (hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bdd)).hasFPowerSeriesAt
  have := congrArg (fun p => p.coeff n) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at this
  rw [thetaTypeCoeff]
  exact this.symm

theorem coeff_add (hf : IsThetaTypeForm N f) (hg : IsThetaTypeForm N g) (n : ℕ) :
    thetaTypeCoeff (f + g) n = thetaTypeCoeff f n + thetaTypeCoeff g n := by
  refine (hf.add hg).coeff_eq_of_hasSum
    (c := fun n => thetaTypeCoeff f n + thetaTypeCoeff g n) (fun τ hτ => ?_) n
  have := (hf.hasSum_coeff hτ).add (hg.hasSum_coeff hτ)
  simpa [add_mul] using this

theorem coeff_smul (hf : IsThetaTypeForm N f) (a : ℂ) (n : ℕ) :
    thetaTypeCoeff (a • f) n = a * thetaTypeCoeff f n := by
  refine (hf.smul a).coeff_eq_of_hasSum (c := fun n => a * thetaTypeCoeff f n) (fun τ hτ => ?_) n
  have := (hf.hasSum_coeff hτ).mul_left a
  simpa [mul_assoc] using this

/-! ## Growth from vanishing coefficients -/

/-- If the first `B` coefficients vanish, `‖f(τ)‖ ≤ K e^{-2πB Im τ}` on `Im τ ≥ 1`. -/
theorem norm_le_of_coeff_lt (hf : IsThetaTypeForm N f) (B : ℕ)
    (hc : ∀ n < B, thetaTypeCoeff f n = 0) :
    ∃ K : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖f τ‖ ≤ K * Real.exp (-(2 * Real.pi * B * τ.im)) := by
  -- `|a_n| e^{-π n} ≤ K₀` from convergence at `τ₀ = i/2`
  have h0 : 0 < (I / 2 : ℂ).im := by simp
  have hs := (hf.hasSum_coeff h0).summable
  have hterm : ∀ n : ℕ, ‖thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * (I / 2))‖ =
      ‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have : (2 * (Real.pi : ℂ) * I * n * (I / 2)) = ((-(Real.pi * n) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, Complex.ofReal_re]
  obtain ⟨K₀, hK₀⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
  have hK₀' : ∀ n, ‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n)) ≤ K₀ := fun n => by
    rw [← hterm]; exact hK₀ ⟨n, rfl⟩
  have hK₀0 : 0 ≤ K₀ := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hK₀' 0)
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  refine ⟨K₀ * Real.exp (2 * Real.pi * B) * (1 - Real.exp (-Real.pi))⁻¹, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := by linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)))
  have hfin : K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
      (1 - Real.exp (-Real.pi))⁻¹ = K₀ * Real.exp (2 * Real.pi * B) *
      (1 - Real.exp (-Real.pi))⁻¹ * Real.exp (-(2 * Real.pi * B * τ.im)) := by ring
  rw [← hfin]
  refine (hf.hasSum_coeff hτ0).norm_le_of_bounded hg fun n => ?_
  by_cases hn : n < B
  · rw [hc n hn, zero_mul, norm_zero]
    positivity
  · push Not at hn
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * I * n * τ).re = -(2 * Real.pi * n * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp : Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im)) ≤
        Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hnB : (B : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hnB))
        (sub_nonneg.2 hτ)]
    have h1 : Real.exp (-(Real.pi * n)) * Real.exp (Real.pi * n) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc ‖thetaTypeCoeff f n‖ * Real.exp (-(2 * Real.pi * n * τ.im))
        = (‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n))) *
          (Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im))) := by
          linear_combination (-(‖thetaTypeCoeff f n‖ *
            Real.exp (-(2 * Real.pi * n * τ.im)))) * h1
      _ ≤ K₀ * (Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n) :=
          mul_le_mul (hK₀' n) hexp (by positivity) hK₀0
      _ = K₀ * Real.exp (2 * Real.pi * B) * Real.exp (-(2 * Real.pi * B * τ.im)) *
          Real.exp (-Real.pi) ^ n := by ring

end IsThetaTypeForm

/-! ## Level-one lemmas: translates are bounded, and fast decay kills coefficients -/

section LevelOne

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- Every translate `F ∣ h⁻¹`, `h ∈ SL₂(ℤ)`, of a modular form is bounded at `i∞`. -/
theorem quotientFunc_bounded (F : ModularForm Γ k) (q : 𝒮ℒ ⧸ Γ.subgroupOf 𝒮ℒ) :
    ∃ M A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖SlashInvariantForm.quotientFunc F q τ‖ ≤ M := by
  induction q using Quotient.inductionOn with
  | h h =>
    have hmem : h.val⁻¹ ∈ 𝒮ℒ := inv_mem h.2
    obtain ⟨g, hg⟩ := hmem
    have hb := ModularFormClass.bdd_at_infty_slash F g
    rw [isBoundedAtImInfty_iff] at hb
    obtain ⟨M, A, hMA⟩ := hb
    refine ⟨M, A, fun τ hτ => ?_⟩
    have e : SlashInvariantForm.quotientFunc F ⟦h⟧ = (⇑F ∣[k] g) := by
      rw [SlashInvariantForm.quotientFunc_mk, ModularForm.SL_slash, ← hg]
      rfl
    rw [e]
    exact hMA τ hτ

/-- Decay `O(e^{-2πBy})` of a level-one form kills its first `B` coefficients. -/
theorem coeff_eq_zero_of_decay {k' : ℤ} (G : ModularForm 𝒮ℒ k') (B : ℕ) {L T : ℝ}
    (hG : ∀ τ : ℍ, T ≤ τ.im → ‖G τ‖ ≤ L * Real.exp (-(2 * Real.pi * B * τ.im)))
    (n : ℕ) (hn : n < B) : (qExpansion 1 G).coeff n = 0 := by
  have hper : Function.Periodic (⇑G ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex G one_mem_strictPeriods_SL
  have hhol := ModularFormClass.holo G
  have hbdd := ModularFormClass.bdd_at_infty G
  have hbound : ∀ t : ℝ, max T 1 ≤ t →
      ‖(qExpansion 1 G).coeff n‖ ≤ L * Real.exp (-(2 * Real.pi * t)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    rw [UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral one_pos hper hhol hbdd n ht0]
    have hL : 0 ≤ L := by
      have := hG ⟨Complex.I * t, by simpa using ht0⟩ (by
        simpa using (le_max_left _ _).trans ht)
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (Real.exp_pos _)
    rw [Complex.ofReal_one, one_div_one, one_mul]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := L * Real.exp (-(2 * Real.pi * t))) fun u _ => ?_).trans ?_
    · have hzim : ((u : ℂ) + t * (UpperHalfPlane.I : ℂ)).im = t := by simp
      have hτ : T ≤ ((u : ℂ) + t * (UpperHalfPlane.I : ℂ)).im := by
        rw [hzim]; exact (le_max_left _ _).trans ht
      have hGt := hG ⟨(u : ℂ) + t * (UpperHalfPlane.I : ℂ), by rw [hzim]; exact ht0⟩ hτ
      change ‖G _‖ ≤ L * Real.exp (-(2 * Real.pi * B * ((u : ℂ) + t * (UpperHalfPlane.I : ℂ)).im))
        at hGt
      have e : L * Real.exp (-(2 * Real.pi * B * ((u : ℂ) + t * (UpperHalfPlane.I : ℂ)).im)) =
          L * Real.exp (-(2 * Real.pi * B * t)) := by rw [hzim]
      replace hGt := hGt.trans_eq e
      rw [norm_mul, norm_div, norm_one, norm_pow, Function.Periodic.norm_qParam, hzim]
      refine (mul_le_mul_of_nonneg_left hGt (by positivity)).trans ?_
      rw [div_one, ← Real.exp_nat_mul, one_div, ← Real.exp_neg, mul_left_comm, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hL
      have hnB : (n : ℝ) + 1 ≤ B := by exact_mod_cast hn
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht0.le) (sub_nonneg.2 hnB)]
    · simp
  have hlim : Tendsto (fun t : ℝ => L * Real.exp (-(2 * Real.pi * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * Real.pi * t) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul L
  have h0 : ‖(qExpansion 1 G).coeff n‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop (max T 1)).mono hbound)
  exact norm_le_zero_iff.1 h0

end LevelOne

/-! ## The Sturm bound -/

/-- `[SL₂(ℤ) : Γ₁(N)]`, as the cardinality entering Mathlib's norm map. -/
def gamma1Index (N : ℕ) : ℕ :=
  Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)

/-- The Sturm bound for weight-`½` θ-type forms of level `N`. -/
def sturmBound (N : ℕ) : ℕ := gamma1Index N / 12 + 1

namespace IsThetaTypeForm

variable {N : ℕ} {f : ℂ → ℂ}

/-- A θ-type form vanishing on `Im τ ≥ ½` vanishes on `ℍ`. -/
theorem eq_zero_of_eq_zero_of_half_le (hf : IsThetaTypeForm N f)
    (h : ∀ τ : ℂ, 1 / 2 < τ.im → f τ = 0) : ∀ τ : ℂ, 0 < τ.im → f τ = 0 := by
  have hga : AnalyticOnNhd ℂ f upperSet :=
    hf.holo.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hI : (Complex.I : ℂ) ∈ upperSet := by simp
  have hev : f =ᶠ[𝓝 Complex.I] 0 := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.im} := isOpen_lt continuous_const continuous_im
    filter_upwards [hopen.mem_nhds (by simp; norm_num)] with z hz
    exact h z hz
  intro τ hτ
  exact hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_upperSet hI hev hτ

/-- **Sturm bound.** For `4 ∣ N`, a θ-type form of level `N` whose first `sturmBound N`
`q`-expansion coefficients vanish is zero on the upper half plane. -/
theorem eq_zero_of_coeff_lt (h4 : 4 ∣ N) [NeZero N] (hf : IsThetaTypeForm N f)
    (hc : ∀ n < sturmBound N, thetaTypeCoeff f n = 0) : ∀ τ : ℂ, 0 < τ.im → f τ = 0 := by
  classical
  set B := sturmBound N
  set F := weightOneForm h4 hf
  set G := ModularForm.norm 𝒮ℒ F
  -- bounds for the other translates
  choose M A hMA using quotientFunc_bounded F
  obtain ⟨K, hK⟩ := hf.norm_le_of_coeff_lt B hc
  set q₀ : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ :=
    ⟦(1 : 𝒮ℒ)⟧
  letI := Fintype.ofFinite
    (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  set P := ∏ q ∈ Finset.univ.erase q₀, M q
  set T := max 1 (∑ q, |A q|)
  have hG : ∀ τ : ℍ, T ≤ τ.im → ‖G τ‖ ≤ (2 * K * P) * Real.exp (-(2 * Real.pi * B * τ.im)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ.im := (le_max_left _ _).trans hτ
    have hAq : ∀ q, A q ≤ τ.im := fun q =>
      (le_abs_self _).trans ((Finset.single_le_sum (fun q _ => abs_nonneg (A q))
        (Finset.mem_univ q)).trans ((le_max_right _ _).trans hτ))
    rw [ModularForm.coe_norm, Finset.prod_apply, norm_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀)]
    have hq₀ : SlashInvariantForm.quotientFunc F q₀ τ = f τ * thetaRef τ := by
      simp [q₀, F, weightOneForm_apply]
    rw [hq₀, norm_mul]
    have hθ : ‖thetaRef τ‖ ≤ 2 := by
      have := norm_thetaRef_sub_one_lt (τ := (τ : ℂ)) (by
        have : (1 : ℝ) ≤ (τ : ℂ).im := hτ1
        linarith)
      have h' := norm_sub_norm_le (thetaRef τ) 1
      rw [norm_one] at h'
      linarith
    have hP : ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc F q τ‖ ≤ P :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ => hMA q τ (hAq q))
    have hf' := hK τ hτ1
    have hP0 : 0 ≤ ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc F q τ‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc ‖f τ‖ * ‖thetaRef τ‖ *
          ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc F q τ‖
        ≤ (K * Real.exp (-(2 * Real.pi * B * τ.im))) * 2 * P := by
          refine mul_le_mul (mul_le_mul hf' hθ (norm_nonneg _)
            ((norm_nonneg _).trans hf')) hP hP0 ?_
          exact mul_nonneg ((norm_nonneg _).trans hf') (by norm_num)
      _ = (2 * K * P) * Real.exp (-(2 * Real.pi * B * τ.im)) := by ring
  have hcoeff : ∀ n < B, (qExpansion 1 G).coeff n = 0 :=
    fun n hn => coeff_eq_zero_of_decay G B hG n hn
  have hord : (B : ℕ∞) ≤ (qExpansion 1 G).order := PowerSeries.nat_le_order _ _ hcoeff
  have hG0 : G = 0 := by
    refine ModularForm.sturm_bound_levelOne (lt_of_lt_of_le ?_ hord)
    have : ((1 : ℤ) * (Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma1 N :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℤ)).toNat = gamma1Index N := by
      simp [gamma1Index]
    rw [this]
    exact_mod_cast Nat.lt_succ_self _
  have hF0 : (F : ℍ → ℂ) = 0 := (ModularForm.norm_eq_zero_iff 𝒮ℒ F).1 hG0
  refine hf.eq_zero_of_eq_zero_of_half_le fun τ hτ => ?_
  have hτ0 : 0 < τ.im := lt_trans (by norm_num) hτ
  have h1 := congrFun hF0 ⟨τ, hτ0⟩
  rw [weightOneForm_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_right (thetaRef_ne_zero hτ.le)

end IsThetaTypeForm

/-! ## Finite dimensionality -/

/-- Restriction of functions `ℂ → ℂ` to the upper half plane. -/
def restrictUpper : (ℂ → ℂ) →ₗ[ℂ] (ℍ → ℂ) := LinearMap.funLeft ℂ ℂ (fun τ : ℍ => (τ : ℂ))

theorem restrictUpper_apply (f : ℂ → ℂ) (τ : ℍ) : restrictUpper f τ = f τ := rfl

/-- The space `M_{1/2}(Γ₁(N), θ)` of θ-type forms of level `N`, as functions on `ℍ`. -/
def thetaTypeSpace (N : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  (IsThetaTypeForm.submodule N).map restrictUpper

theorem mem_thetaTypeSpace {N : ℕ} {g : ℍ → ℂ} :
    g ∈ thetaTypeSpace N ↔ ∃ f : ℂ → ℂ, IsThetaTypeForm N f ∧ restrictUpper f = g :=
  Iff.rfl

/-- The first `B` coefficients, as a linear map on `thetaTypeSpace N`. -/
def thetaTypeCoeffMap (N B : ℕ) : thetaTypeSpace N →ₗ[ℂ] (Fin B → ℂ) where
  toFun g n := (qExpansion 1 (g : ℍ → ℂ)).coeff n
  map_add' g h := by
    obtain ⟨f, hf, hfg⟩ := mem_thetaTypeSpace.1 g.2
    obtain ⟨f', hf', hfh⟩ := mem_thetaTypeSpace.1 h.2
    funext n
    have e1 : ((g + h : thetaTypeSpace N) : ℍ → ℂ) = restrictUpper (f + f') := by
      rw [map_add, hfg, hfh]; rfl
    have := hf.coeff_add hf' n
    simp only [thetaTypeCoeff] at this
    simp only [Pi.add_apply, e1, ← hfg, ← hfh]
    exact this
  map_smul' a g := by
    obtain ⟨f, hf, hfg⟩ := mem_thetaTypeSpace.1 g.2
    funext n
    have e1 : ((a • g : thetaTypeSpace N) : ℍ → ℂ) = restrictUpper (a • f) := by
      rw [map_smul, hfg]; rfl
    have := hf.coeff_smul a n
    simp only [thetaTypeCoeff] at this
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e1, ← hfg]
    exact this

theorem thetaTypeCoeffMap_injective {N : ℕ} (h4 : 4 ∣ N) [NeZero N] :
    Function.Injective (thetaTypeCoeffMap N (sturmBound N)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  obtain ⟨f, hf, hfg⟩ := mem_thetaTypeSpace.1 g.2
  have hc : ∀ n < sturmBound N, thetaTypeCoeff f n = 0 := by
    intro n hn
    have := congrFun hg ⟨n, hn⟩
    simp only [thetaTypeCoeffMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [← hfg] at this
    exact this
  have h0 := hf.eq_zero_of_coeff_lt h4 hc
  ext τ
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [← hfg, restrictUpper_apply]
  exact h0 τ τ.2

/-- **Finite dimensionality** of `M_{1/2}(Γ₁(N), θ)` for `4 ∣ N`. -/
theorem finiteDimensional_thetaTypeSpace {N : ℕ} (h4 : 4 ∣ N) [NeZero N] :
    FiniteDimensional ℂ (thetaTypeSpace N) :=
  Module.Finite.of_injective _ (thetaTypeCoeffMap_injective h4)

/-- `dim M_{1/2}(Γ₁(N), θ) ≤ sturmBound N`. -/
theorem finrank_thetaTypeSpace_le {N : ℕ} (h4 : 4 ∣ N) [NeZero N] :
    Module.finrank ℂ (thetaTypeSpace N) ≤ sturmBound N := by
  have := LinearMap.finrank_le_finrank_of_injective (thetaTypeCoeffMap_injective h4)
  simpa using this

end VOA.Classification.COne

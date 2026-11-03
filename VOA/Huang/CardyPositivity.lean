/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.ZhuModData

/-!
# The vacuum column of the `S`-matrix is real and non-negative

For a nice VOA with real central charge and real conformal weights, Zhu's matrix `ρ(S)` satisfies
`S_{a0} ∈ [0, ∞)` for every label `a` (`0` the vacuum). This is the character-level ("Cardy")
half of the positivity package `HuangSPositivityInput`:

* on the imaginary axis every character `ch_a(it)` is a non-negative real (`chi_mem_K`);
* `e^{-2πtc/24} ch_b(it) → δ_{b,0}` as `t → ∞` (`tendsto_vacNormalized`): pseudo-unitarity makes the
  vacuum the only module with lowest weight `0`, and `dim V₀ = 1`;
* so `e^{-2πtc/24} ch_a(i/t) = Σ_b S_ab e^{-2πtc/24} ch_b(it) → S_{a0}`, a limit of non-negative
  reals (`vacColumn_mem_K`).

`#print axioms`: Lean's three.
-/

open Complex Finset Module Filter Topology

noncomputable section

namespace VOA.Huang.CardyPositivity

open VOA VOA.Classification.COne VOA.Huang.ZhuModData

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Non-negative reals inside `ℂ`. -/
def K : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

theorem isClosed_K : IsClosed K :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

theorem ofReal_mem_K {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ∈ K := ⟨by simp, by simpa using hr⟩

theorem mul_mem_K {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) : z * w ∈ K := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_im, hz1, hw1]
  · simp only [Complex.mul_re, hz1, hw1, mul_zero, sub_zero]; exact mul_nonneg hz2 hw2

section Module

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The character term on the imaginary axis is a non-negative real. -/
theorem term_eq (N : OrdVModule W M) {h : ℂ} (hh : h.im = 0)
    (hc : W.centralCharge.im = 0) (τ : UpperHalfPlane) (hτ : (τ : ℂ).re = 0) (n : ℕ) :
    (finrank ℂ (N.weight (h + n)) : ℂ) *
        cexp (2 * Real.pi * I * (h + n - W.centralCharge / 24) * τ)
      = (((finrank ℂ (N.weight (h + n)) : ℝ) *
          Real.exp (-2 * Real.pi * τ.im * (h.re + n - W.centralCharge.re / 24)) : ℝ) : ℂ) := by
  have eh : h = (h.re : ℂ) := Complex.ext (by simp) (by simp [hh])
  have ec : W.centralCharge = (W.centralCharge.re : ℂ) := Complex.ext (by simp) (by simp [hc])
  have eτ : (τ : ℂ) = (τ.im : ℂ) * I := Complex.ext (by simpa using hτ) (by simp)
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  congr 2
  rw [eτ]
  conv_lhs => rw [eh, ec]
  linear_combination (2 * (Real.pi : ℂ) * ((h.re : ℂ) + n - (W.centralCharge.re : ℂ) / 24) *
    (τ.im : ℂ)) * Complex.I_sq

variable (N : OrdVModule W M) {h : ℂ} (hcw : HasConformalWeight N h) (hC2 : C2Cofinite W)
  (hh : h.im = 0) (hc : W.centralCharge.im = 0)

/-- The analytic character. -/
def chi (τ : UpperHalfPlane) : ℂ :=
  qEvalAt (torusOnePoint N W.vacuum) (h - W.centralCharge / 24) τ

include hcw hC2 hh hc in
/-- **Characters are non-negative reals on the imaginary axis.** -/
theorem chi_mem_K (τ : UpperHalfPlane) (hτ : (τ : ℂ).re = 0) : chi N (h := h) τ ∈ K := by
  have hs := hasSum_character N hcw hC2 τ
  simp_rw [term_eq N hh hc τ hτ] at hs
  rw [Complex.hasSum_iff] at hs
  obtain ⟨hre, him⟩ := hs
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  refine ⟨(hasSum_zero.unique him).symm, ?_⟩
  exact hre.nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

/-- The point `i·max t 1` of the upper half plane. -/
def imPt (t : ℝ) : UpperHalfPlane :=
  ⟨I * (max t 1 : ℝ), by simp⟩

theorem imPt_im (t : ℝ) : (imPt t).im = max t 1 := by
  simp [imPt, UpperHalfPlane.im]

theorem imPt_re (t : ℝ) : ((imPt t : UpperHalfPlane) : ℂ).re = 0 := by
  simp [imPt]

/-- The vacuum-normalized character `e^{-2πtc/24} ch(it)`. -/
def vacNormalized (t : ℝ) : ℂ :=
  cexp (-(2 * Real.pi * (max t 1 : ℝ) * W.centralCharge / 24)) * chi N (h := h) (imPt t)

include hcw hC2 hh hc in
/-- **The vacuum-normalized character tends to `Σ_{h+n=0} dim M_{h+n}`.** -/
theorem tendsto_vacNormalized (hpos : 0 ≤ h.re) :
    Tendsto (vacNormalized N (h := h)) atTop
      (𝓝 (∑' n : ℕ, if h.re + n = 0 then (finrank ℂ (N.weight (h + n)) : ℂ) else 0)) := by
  -- series form
  have hform : ∀ t : ℝ, vacNormalized N (h := h) t = ∑' n : ℕ,
      (((finrank ℂ (N.weight (h + n)) : ℝ) *
        Real.exp (-2 * Real.pi * (max t 1) * (h.re + n)) : ℝ) : ℂ) := by
    intro t
    have hs := (hasSum_character N hcw hC2 (imPt t))
    simp_rw [term_eq N hh hc (imPt t) (imPt_re t), imPt_im] at hs
    rw [vacNormalized, chi, ← hs.tsum_eq, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    have ec : W.centralCharge = (W.centralCharge.re : ℂ) := Complex.ext (by simp) (by simp [hc])
    rw [show -(2 * (Real.pi : ℂ) * ((max t 1 : ℝ) : ℂ) * W.centralCharge / 24)
        = ((-(2 * Real.pi * (max t 1) * W.centralCharge.re / 24) : ℝ) : ℂ) by
      conv_lhs => rw [ec]
      push_cast; ring]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
    congr 1
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [show vacNormalized N (h := h) = _ from funext hform]
  -- dominated convergence
  have hsum1 := (hasSum_character N hcw hC2 (imPt 0))
  simp_rw [term_eq N hh hc (imPt 0) (imPt_re 0), imPt_im] at hsum1
  have hsum1' : Summable (fun n : ℕ => (finrank ℂ (N.weight (h + n)) : ℝ) *
      Real.exp (-2 * Real.pi * (max 0 1) * (h.re + n - W.centralCharge.re / 24))) :=
    Complex.summable_ofReal.mp hsum1.summable
  have hbound : Summable (fun n : ℕ => (finrank ℂ (N.weight (h + n)) : ℝ) *
      Real.exp (-2 * Real.pi * (h.re + n))) := by
    refine (hsum1'.mul_left (Real.exp (-2 * Real.pi * W.centralCharge.re / 24))).congr
      (fun n => ?_)
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    simp only [max_eq_right zero_le_one]
    ring
  refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) ?_
  · -- termwise limits
    by_cases hn : h.re + n = 0
    · rw [if_pos hn]
      simp only [hn, mul_zero, Real.exp_zero, mul_one]
      exact tendsto_const_nhds
    · rw [if_neg hn]
      have hn' : 0 < h.re + n := lt_of_le_of_ne (by positivity) (Ne.symm hn)
      have hmax : Tendsto (fun t : ℝ => max t 1) atTop atTop :=
        tendsto_atTop_mono (fun t => le_max_left t 1) tendsto_id
      have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * Real.pi * (max t 1) * (h.re + n)))
          atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have : Tendsto (fun t : ℝ => (max t 1) * (-2 * Real.pi * (h.re + n))) atTop atBot :=
          hmax.atTop_mul_const_of_neg (by nlinarith [Real.pi_pos])
        refine this.congr (fun t => by ring)
      have h2 := hexp.const_mul ((finrank ℂ (N.weight (h + n)) : ℝ))
      rw [mul_zero] at h2
      have := (Complex.continuous_ofReal.tendsto 0).comp h2
      rw [Complex.ofReal_zero] at this
      exact this
  · refine Eventually.of_forall (fun t n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have h1 : (1 : ℝ) ≤ max t 1 := le_max_right t 1
    have h2 : 0 ≤ h.re + n := by positivity
    have key : 0 ≤ 2 * Real.pi * (h.re + n) * (max t 1 - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr h1)
    nlinarith [key]

end Module

/-! ## The vacuum column -/

theorem finrank_grading_zero (hne : W.vacuum ≠ 0) : finrank ℂ (W.grading 0) = 1 := by
  have h : W.grading 0 = ℂ ∙ W.vacuum :=
    le_antisymm (vacuumGradeZero_holds (W := W))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr W.vacuum_mem_grading_zero)
  rw [h, finrank_span_singleton hne]

theorem re_S_smul_imPt (t : ℝ) :
    ((ModularGroup.S • imPt t : UpperHalfPlane) : ℂ).re = 0 := by
  rw [UpperHalfPlane.modular_S_smul]
  change ((-((imPt t : UpperHalfPlane) : ℂ))⁻¹).re = 0
  rw [Complex.inv_re, Complex.neg_re, imPt_re]
  simp

/-- **The vacuum column of Zhu's `S`-matrix is real and non-negative**, for a nice VOA with real
central charge and real conformal weights. -/
theorem vacColumn_mem_K (hNice : Nice W) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D) (hirr : Irredundant D.Mfam)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (hreal : ∀ i, (D.h i).im = 0) (hc : W.centralCharge.im = 0) (a : ι) :
    D.repS a v0 ∈ K := by
  classical
  have hC2 : C2Cofinite W := hNice.1.c2Cofinite
  have hne : W.vacuum ≠ 0 := hNice.1.simple.vacuum_ne_zero
  obtain ⟨f0⟩ := hv0
  have hh0 : D.h v0 = 0 :=
    hasConformalWeight_unique (ModuleEquiv.hasConformalWeight f0 (D.hasWeight v0))
      (hasConformalWeight_adjoint W hne)
  -- non-negativity of the weights (pseudo-unitarity)
  have hposb : ∀ b, b ≠ v0 → 0 < (D.h b).re := by
    intro b hb
    refine hNice.2 _ (D.Mfam b).isMod (D.Mfam b).irreducible ⟨fun g => hb ?_⟩ _ (D.hasWeight b).1
    exact hirr b v0 ⟨g.trans f0.symm⟩
  have hpos : ∀ b, 0 ≤ (D.h b).re := by
    intro b
    by_cases hb : b = v0
    · rw [hb, hh0]; simp
    · exact (hposb b hb).le
  -- the limits
  let L : ι → ℂ := fun b => ∑' n : ℕ,
    if (D.h b).re + n = 0 then (finrank ℂ ((D.Mfam b).isMod.weight (D.h b + n)) : ℂ) else 0
  have hL : ∀ b, L b = if b = v0 then 1 else 0 := by
    intro b
    by_cases hb : b = v0
    · subst hb
      rw [if_pos rfl]
      have : ∀ n : ℕ, (if (D.h b).re + n = 0
          then (finrank ℂ ((D.Mfam b).isMod.weight (D.h b + n)) : ℂ) else 0)
          = if n = 0 then (finrank ℂ ((D.Mfam b).isMod.weight (D.h b + 0)) : ℂ) else 0 := by
        intro n
        rw [hh0]
        by_cases hn : n = 0
        · subst hn; rw [if_pos (by simp), if_pos rfl, Nat.cast_zero]
        · rw [if_neg (by simpa using hn), if_neg hn]
      change (∑' n : ℕ, _) = _
      rw [tsum_congr this, tsum_ite_eq, hh0, add_zero, ModuleEquiv.finrank_weight_eq f0,
        show (0 : ℂ) = ((0 : ℕ) : ℂ) by simp, adjointModule_weight_nat, Nat.cast_zero,
        finrank_grading_zero hne]
      simp
    · rw [if_neg hb]
      have hp := hposb b hb
      refine (tsum_congr (fun n => ?_)).trans tsum_zero
      rw [if_neg]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hlim : ∀ b, Tendsto (vacNormalized (D.Mfam b).isMod (h := D.h b)) atTop (𝓝 (L b)) :=
    fun b => tendsto_vacNormalized _ (D.hasWeight b) hC2 (hreal b) hc (hpos b)
  -- the transformed function
  let F : ℝ → ℂ := fun t => cexp (-(2 * Real.pi * (max t 1 : ℝ) * W.centralCharge / 24)) *
    traceFun D.Mfam D.h a W.vacuum (ModularGroup.S • imPt t)
  have hF : ∀ t, F t = ∑ b, D.repS a b * vacNormalized (D.Mfam b).isMod (h := D.h b) t := by
    intro t
    have hlaw := hZ ModularGroup.S 0 W.vacuum (vacuum_mem_sqWeightSpace_zero W) a (imPt t)
    rw [pow_zero, one_mul, D.rep_S] at hlaw
    simp only [F, hlaw, Finset.mul_sum, Matrix.of_apply, vacNormalized, chi]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [traceFun]
    ring
  have hFlim : Tendsto F atTop (𝓝 (D.repS a v0)) := by
    have : Tendsto (fun t => ∑ b, D.repS a b * vacNormalized (D.Mfam b).isMod (h := D.h b) t)
        atTop (𝓝 (∑ b, D.repS a b * L b)) :=
      tendsto_finsetSum _ (fun b _ => (hlim b).const_mul _)
    simp only [hL, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    exact this.congr (fun t => (hF t).symm)
  have hFK : ∀ t, F t ∈ K := by
    intro t
    refine mul_mem_K ?_ ?_
    · have ec : W.centralCharge = (W.centralCharge.re : ℂ) :=
        Complex.ext (by simp) (by simp [hc])
      rw [ec, show -(2 * (Real.pi : ℂ) * ((max t 1 : ℝ) : ℂ) * (W.centralCharge.re : ℂ) / 24)
          = ((-(2 * Real.pi * (max t 1) * W.centralCharge.re / 24) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      exact ofReal_mem_K (Real.exp_pos _).le
    · exact chi_mem_K (D.Mfam a).isMod (D.hasWeight a) hC2 (hreal a) hc _ (re_S_smul_imPt t)
  exact isClosed_K.mem_of_tendsto hFlim (Eventually.of_forall hFK)

end VOA.Huang.CardyPositivity

/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Moonshine.CharacterDelta
import VOA.Modularity.JInvariantAnalytic
import VOA.Modularity.MoonshineCorollary

/-!
# The formal `JShift` is the `q`-expansion of the analytic `j − 744`

`Modularity/JFunction.lean` defines `J = j − 744` formally, through `JShift = q·J ∈ ℂ⟦q⟧`, and
`Modularity/JInvariantAnalytic.lean` defines the analytic `jInvariant z = E₄(z)³/Δ(z)` on `ℍ`
from Mathlib's `E₄` and `Δ`. This file links the two.

* `qExpansion_qJ : qExpansion 1 qJ = JShift`, where `qJ z = q·(j(z) − 744)` and `q = 𝕢 1 z`;
* `hasSum_JShift (z : ℍ)`: `Σₙ [qⁿ]JShift · qⁿ = q·(j(z) − 744)`, convergent on all of `ℍ`;
* `hasSum_JShift_laurent (z : ℍ)`: `j(z) − 744 = q⁻¹ + Σₙ [q^{n+1}]JShift · qⁿ`, the
  Laurent-expansion form;
* `hasSum_charSeries_of_moonshineCharacter`: for any VOA `W` with `MoonshineCharacter W`, its
  formal character sums to `q·(j(z) − 744)`.

## Method

The function `qJ = 𝕢·(E₄³/Δ − 744)` is `1`-periodic, holomorphic on `ℍ` and bounded at the cusp:
`𝕢/Δ = O(1)` by Mathlib's `exp_isBigO_discriminant`. So it has a convergent `q`-expansion
(`hasSum_qExpansion`). To identify that expansion, note `qJ · Δ = 𝕢 · (E₄³ − 744 Δ)` on `ℍ`.
`qExpansion` is multiplicative on functions with analytic cusp functions (`qExpansion_mul`), and
`qExpansion Δ = deltaSeries = X · deltaOverQ` (`Moonshine.qExpansion_discriminant`). So
`X · (qExpansion qJ · deltaOverQ) = X · (E4Series³ − 744 X deltaOverQ)`. Cancel `X` (`ℂ⟦q⟧` is a
domain), then the unit `deltaOverQ`, and compare with `JShift · deltaOverQ = E4Series³ − 744 X
deltaOverQ`.
-/

open scoped MatrixGroups Manifold

namespace VOA

namespace Moonshine

open PowerSeries UpperHalfPlane ModularForm Filter Topology Asymptotics

local notation "𝕢" => Function.Periodic.qParam

/-- `q = e^{2πiz}` as a function on `ℍ`. -/
noncomputable def qFun (z : ℍ) : ℂ := 𝕢 1 (z : ℂ)

/-- `q·(j − 744)` as a function on `ℍ`. -/
noncomputable def qJ (z : ℍ) : ℂ := qFun z * (jInvariant z - 744)

/-! ## §1  Analytic hygiene: periodicity, holomorphy, boundedness -/

theorem periodic_qFun : Function.Periodic (qFun ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, qFun, ofComplex_apply_of_im_pos hw,
      ofComplex_apply_of_im_pos hw1, UpperHalfPlane.coe_mk]
    simp only [Function.Periodic.qParam, div_one, Complex.ofReal_one]
    rw [mul_add, Complex.exp_add, mul_one, Complex.exp_two_pi_mul_I, mul_one]
  · have hw1 : (w + 1).im ≤ 0 := by simpa using not_lt.mp hw
    simp [ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

theorem periodic_E₄ : Function.Periodic ((E₄ : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL

theorem periodic_Δ : Function.Periodic ((discriminant : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
    one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

theorem periodic_qJ : Function.Periodic (qJ ∘ ofComplex) 1 := by
  intro w
  have h1 := periodic_qFun w
  have h2 := periodic_E₄ w
  have h3 := periodic_Δ w
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  simp only [qJ, jInvariant, h1, h2, h3]

theorem mdiff_qFun : MDiff qFun := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (show Differentiable ℂ (fun w : ℂ => 𝕢 1 w) by
    unfold Function.Periodic.qParam; fun_prop).differentiableOn.congr fun w hw => ?_
  simp [qFun, ofComplex_apply_of_im_pos hw]

theorem mdiff_Δ : MDiff (discriminant : ℍ → ℂ) := by
  have := ModularFormClass.holo CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

theorem mdiff_qJ : MDiff qJ := by
  have hE := ModularFormClass.holo E₄
  have hj : MDiff jInvariant := by
    have h := (hE.pow 3).mul (mdiff_Δ.inv fun z => discriminant_ne_zero z)
    have he : jInvariant = fun z => E₄ z ^ 3 * (discriminant z)⁻¹ := by
      funext z; simp [jInvariant, div_eq_mul_inv]
    rw [he]
    exact h
  exact mdiff_qFun.mul (hj.sub mdifferentiable_const)

theorem norm_qFun (z : ℍ) : ‖qFun z‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp [qFun, Function.Periodic.norm_qParam]

theorem qFun_isBigO : qFun =O[atImInfty] fun z : ℍ => Real.exp (-2 * Real.pi * z.im) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [norm_qFun, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul])

theorem isBoundedAtImInfty_qFun : IsBoundedAtImInfty qFun :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    simp only [Pi.one_apply, norm_one, one_mul, norm_qFun]
    exact Real.exp_le_one_iff.mpr (by nlinarith [z.im_pos, Real.pi_pos]))

theorem isBoundedAtImInfty_qFun_div_Δ :
    IsBoundedAtImInfty fun z : ℍ => qFun z * (discriminant z)⁻¹ := by
  have hinv := exp_isBigO_discriminant.inv_rev
    (Eventually.of_forall fun z h => absurd h (Real.exp_pos _).ne')
  refine (qFun_isBigO.mul hinv).trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [norm_mul, norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le,
    mul_inv_cancel₀ (Real.exp_pos _).ne']
  simp

theorem isBoundedAtImInfty_qJ : IsBoundedAtImInfty qJ := by
  have hE : IsBoundedAtImInfty (E₄ : ℍ → ℂ) := ModularFormClass.bdd_at_infty E₄
  have h := ((hE.mul hE).mul hE).mul isBoundedAtImInfty_qFun_div_Δ |>.sub
    (isBoundedAtImInfty_qFun.const_mul_left 744)
  refine h.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
  simp only [Pi.mul_apply, qJ, jInvariant]
  ring

theorem analyticAt_qFun : AnalyticAt ℂ (cuspFunction 1 qFun) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_qFun mdiff_qFun isBoundedAtImInfty_qFun

theorem analyticAt_qJ : AnalyticAt ℂ (cuspFunction 1 qJ) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_qJ mdiff_qJ isBoundedAtImInfty_qJ

/-! ## §2  The `q`-expansions -/

theorem hasSum_qFun (z : ℍ) :
    HasSum (fun m : ℕ => coeff m (X : PowerSeries ℂ) • 𝕢 1 (z : ℂ) ^ m) (qFun z) := by
  have he : (fun m : ℕ => coeff m (X : PowerSeries ℂ) • 𝕢 1 (z : ℂ) ^ m)
      = fun m => if m = 1 then 𝕢 1 (z : ℂ) else 0 := by
    funext m
    rcases eq_or_ne m 1 with rfl | hm
    · simp
    · simp [coeff_X, hm]
  rw [he]
  exact hasSum_ite_eq 1 _

theorem qExpansion_qFun : qExpansion 1 qFun = X := by
  ext m
  letI : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective' := Function.injective_id }
  exact (qExpansion_coeff_unique (F := ℍ → ℂ) (h := 1) qFun one_pos analyticAt_qFun hasSum_qFun
    m).symm

theorem analyticAt_Δ : AnalyticAt ℂ (cuspFunction 1 (discriminant : ℍ → ℂ)) 0 := by
  have := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

theorem analyticAt_E₄_pow : AnalyticAt ℂ (cuspFunction 1 ((E₄.pow 3 : ModularForm 𝒮ℒ _) : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

/-- `E₄³ − 744 Δ` as a function on `ℍ`. -/
noncomputable def e4CubeSub : ℍ → ℂ :=
  ((E₄.pow 3 : ModularForm 𝒮ℒ _) : ℍ → ℂ) - (744 : ℂ) • (discriminant : ℍ → ℂ)

theorem analyticAt_e4CubeSub : AnalyticAt ℂ (cuspFunction 1 e4CubeSub) 0 := by
  have hs : AnalyticAt ℂ (cuspFunction 1 ((744 : ℂ) • (discriminant : ℍ → ℂ))) 0 := by
    rw [cuspFunction_smul analyticAt_Δ.continuousAt]
    exact analyticAt_Δ.const_smul
  rw [e4CubeSub, cuspFunction_sub analyticAt_E₄_pow.continuousAt hs.continuousAt]
  exact analyticAt_E₄_pow.sub hs

theorem qExpansion_e4CubeSub : qExpansion 1 e4CubeSub = E4Series ^ 3 - (744 : ℂ) • deltaSeries := by
  have hs : AnalyticAt ℂ (cuspFunction 1 ((744 : ℂ) • (discriminant : ℍ → ℂ))) 0 := by
    rw [cuspFunction_smul analyticAt_Δ.continuousAt]
    exact analyticAt_Δ.const_smul
  rw [e4CubeSub, qExpansion_sub analyticAt_E₄_pow hs, qExpansion_smul analyticAt_Δ,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄,
    qExpansion_discriminant]

theorem qJ_mul_Δ : qJ * (discriminant : ℍ → ℂ) = qFun * e4CubeSub := by
  funext z
  have hΔ := discriminant_ne_zero z
  simp only [Pi.mul_apply, qJ, jInvariant, e4CubeSub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ModularForm.coe_pow, Pi.pow_apply]
  field_simp

theorem jShift_mul_deltaOverQ : jShift * deltaOverQ = E4Series ^ 3 := by
  rw [jShift, ← deltaOverQUnit_coe, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    mul_one]

/-- **The `q`-expansion of `q·(j − 744)` is `JShift`.** -/
theorem qExpansion_qJ : qExpansion 1 qJ = JShift := by
  have h := congrArg (qExpansion 1) qJ_mul_Δ
  rw [qExpansion_mul analyticAt_qJ analyticAt_Δ, qExpansion_mul analyticAt_qFun analyticAt_e4CubeSub,
    qExpansion_discriminant, qExpansion_qFun, qExpansion_e4CubeSub, deltaSeries_eq] at h
  have h2 : X * (qExpansion 1 qJ * deltaOverQ) = X * (JShift * deltaOverQ) := by
    rw [JShift, sub_mul, jShift_mul_deltaOverQ]
    simp only [PowerSeries.smul_eq_C_mul] at h ⊢
    linear_combination h
  have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
  exact mul_right_cancel₀ deltaOverQ_isUnit.ne_zero h3

/-- **Moonshine's `J`, analytically.** For every `z ∈ ℍ`, with `q = e^{2πiz}`, the formal series
`JShift` converges to `q·(j(z) − 744)`. -/
theorem hasSum_JShift (z : ℍ) :
    HasSum (fun n : ℕ => coeff n JShift * 𝕢 1 (z : ℂ) ^ n) (𝕢 1 (z : ℂ) * (jInvariant z - 744)) := by
  have h := hasSum_qExpansion one_pos periodic_qJ mdiff_qJ isBoundedAtImInfty_qJ z
  rw [qExpansion_qJ] at h
  simpa [qJ, qFun, smul_eq_mul] using h

/-- **The Laurent form**: `j(z) − 744 = q⁻¹ + Σₙ [q^{n+1}]JShift · qⁿ`, i.e.
`j − 744 = q⁻¹ + 196884 q + 21493760 q² + ⋯`. -/
theorem hasSum_JShift_laurent (z : ℍ) :
    HasSum (fun n : ℕ => coeff (n + 1) JShift * 𝕢 1 (z : ℂ) ^ n)
      (jInvariant z - 744 - (𝕢 1 (z : ℂ))⁻¹) := by
  have hq : 𝕢 1 (z : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_JShift z)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    constantCoeff_JShift, coeff_zero_eq_constantCoeff_apply] at h
  have h2 := h.mul_left (𝕢 1 (z : ℂ))⁻¹
  convert h2 using 1
  · funext n
    rw [pow_succ]
    field_simp
  · field_simp

/-- **A VOA with the Moonshine character has analytic character `j − 744`**: if
`charSeries W = JShift`, then `Σₙ dim Wₙ · qⁿ = q·(j(z) − 744)` for every `z ∈ ℍ`. -/
theorem hasSum_charSeries_of_moonshineCharacter {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (hW : MoonshineCharacter W) (z : ℍ) :
    HasSum (fun n : ℕ => (Module.finrank ℂ (W.grading n) : ℂ) * 𝕢 1 (z : ℂ) ^ n)
      (𝕢 1 (z : ℂ) * (jInvariant z - 744)) := by
  have h := hasSum_JShift z
  rw [← hW] at h
  simpa using h

end Moonshine

end VOA

section AxiomAudit
#print axioms VOA.Moonshine.qExpansion_qJ
#print axioms VOA.Moonshine.hasSum_JShift
#print axioms VOA.Moonshine.hasSum_JShift_laurent
#print axioms VOA.Moonshine.hasSum_charSeries_of_moonshineCharacter
end AxiomAudit

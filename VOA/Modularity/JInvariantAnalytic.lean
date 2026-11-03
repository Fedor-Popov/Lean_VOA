/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The analytic `j`-invariant

Mathlib has the level-one Eisenstein series `ModularForm.E₄ : ModularForm 𝒮ℒ 4` and the modular
discriminant `ModularForm.discriminant` (with `discriminant_ne_zero`, and its weight-`12`
slash-invariance at the two generators `S`, `T`), but **not** the `j`-invariant.  This LEAF file
builds it and proves full `SL₂(ℤ)`-invariance:

  `jInvariant z = E₄(z)³ / Δ(z)`,   `jInvariant (γ • z) = jInvariant z`.

This is the analytic object missing from the hauptmodul step `χ = j + const` of Gannon's
Question 5.3.4 (`Modularity.MoonshineCorollary.MoonshineCharacter`): the repo already has the
*formal* `jShift = q·j` with `[q²] jShift = 196884` (`Modularity.JFunction`) and the `SL₂(ℤ)`
invariance of `χ` (`char_SL2Z_invariant_of_spanning`).

## Method

`Δ ∣[12] γ = Δ` holds at `S` and `T` (Mathlib), and the set of `γ` where it holds is a
**subgroup** — the slash action is a group action — so `SpecialLinearGroup.SL2Z_generators`
propagates it to all of `SL₂(ℤ)` (`discriminant_slash`).  `E₄` is slash-invariant of weight `4`
by construction.  Pointwise (`ModularForm.slash_action_eq'_iff`) this reads
`Δ(γ•z) = (cz+d)^12 Δ(z)` and `E₄(γ•z) = (cz+d)^4 E₄(z)`, and the `(cz+d)^12` cancels in the
quotient.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- **The `j`-invariant** `j = E₄³/Δ` as a function on the upper half-plane. -/
noncomputable def jInvariant (z : ℍ) : ℂ :=
  (ModularForm.E₄ z) ^ 3 / ModularForm.discriminant z

/-- The **weight-`12` slash-invariance of `Δ` for every `γ ∈ SL₂(ℤ)**.  Mathlib supplies the two
generator cases; the slash action being a group action propagates them. -/
theorem discriminant_slash (γ : SL(2, ℤ)) :
    ModularForm.discriminant ∣[(12 : ℤ)] γ = ModularForm.discriminant := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · exact ModularForm.discriminant_S_invariant
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ModularForm.discriminant_T_invariant
  | one => exact SlashAction.slash_one _ _
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ihx =>
      have h : (ModularForm.discriminant ∣[(12 : ℤ)] x) ∣[(12 : ℤ)] x⁻¹
          = ModularForm.discriminant ∣[(12 : ℤ)] x⁻¹ := by rw [ihx]
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at h
      exact h.symm

/-- **Pointwise slash invariance** for any level-one slash-invariant form: for `γ ∈ SL₂(ℤ)`,
`f(γ•z) = (cz+d)^k f(z)`. -/
theorem slashInvariant_smul {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [SlashInvariantFormClass F 𝒮ℒ k] (f : F) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ k * f z := by
  rw [← ModularForm.slash_action_eq'_iff, ModularForm.SL_slash]
  exact congrFun (SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩) z

/-- Pointwise form: `Δ(γ•z) = (cz+d)¹² Δ(z)`. -/
theorem discriminant_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.discriminant (γ • z)
      = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (12 : ℤ) * ModularForm.discriminant z :=
  slashInvariant_smul CuspForm.discriminant γ z

/-- Pointwise form: `E₄(γ•z) = (cz+d)⁴ E₄(z)`. -/
theorem E₄_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.E₄ (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (4 : ℤ) * ModularForm.E₄ z :=
  slashInvariant_smul ModularForm.E₄ γ z

/-- **`j` is `SL₂(ℤ)`-invariant.** -/
theorem jInvariant_smul (γ : SL(2, ℤ)) (z : ℍ) : jInvariant (γ • z) = jInvariant z := by
  have hden : ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
    simpa [UpperHalfPlane.denom] using this
  have h12 : (((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (4 : ℤ)) ^ (3 : ℕ)
      = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (12 : ℤ) := by
    rw [← zpow_natCast (((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (4 : ℤ)) 3, ← zpow_mul]
    norm_num
  rw [jInvariant, jInvariant, E₄_smul, discriminant_smul, mul_pow, h12,
    mul_div_mul_left _ _ (zpow_ne_zero (12 : ℤ) hden)]

/-- `j` never has a zero denominator: it is defined at every point of `ℍ`. -/
theorem jInvariant_eq_iff (z : ℍ) (c : ℂ) :
    jInvariant z = c ↔ (ModularForm.E₄ z) ^ 3 = c * ModularForm.discriminant z := by
  rw [jInvariant, div_eq_iff (ModularForm.discriminant_ne_zero z)]

/-! ## The hauptmodul step -/

/-- **The hauptmodul step, `χ = j + const`.**  Mathlib's
`ModularFormClass.levelOne_weight_zero_const` says a level-one weight-`0` modular form is
constant.  So as soon as `χ − j` *is* such a form — the remaining analytic content: holomorphy of
`χ` on `ℍ` and its boundedness at the cusp, `j` having exactly a simple pole there — the
`SL₂(ℤ)`-invariant `χ` differs from `j` by a constant.

For the Moonshine corollary `χ_{V♮} = J` this is the last step: `char_SL2Z_invariant_of_spanning`
supplies the invariance and `Modularity.JFunction` the normalisation `[q²] jShift = 196884`. -/
theorem eq_jInvariant_add_const (F : ModularForm 𝒮ℒ 0) (χ : ℍ → ℂ)
    (hF : ∀ z, F z = χ z - jInvariant z) : ∃ c : ℂ, ∀ z, χ z = jInvariant z + c := by
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z => ?_⟩
  have h1 : F z = c := by rw [hc]; rfl
  have h2 := hF z
  rw [h1] at h2
  linear_combination -h2

/-- The same, packaged for an `SL₂(ℤ)`-invariant `χ`: the difference is then automatically
`SL₂(ℤ)`-invariant, as `jInvariant_smul` shows. -/
theorem sub_jInvariant_smul {χ : ℍ → ℂ} (hχ : ∀ (γ : SL(2, ℤ)) (z : ℍ), χ (γ • z) = χ z)
    (γ : SL(2, ℤ)) (z : ℍ) : (χ - jInvariant) (γ • z) = (χ - jInvariant) z := by
  simp only [Pi.sub_apply, hχ γ z, jInvariant_smul γ z]

end VOA

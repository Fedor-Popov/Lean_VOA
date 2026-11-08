/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessIso
import VOA.Moonshine.AutFaithfulAssembly

/-!
# The rational Monster `AutO` acts on the Griess algebra of `V♮`

`griessIso : ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] V♮₂` identifies the Griess algebra of `V♮` with Axiom's rational
Griess algebra `SpaceB`, extended to `ℂ`.  Transporting the base change `ℂ ⊗ g` of a `ℚ`-linear
automorphism `g` of `SpaceB` along it gives the **Griess conjugate**

  `griessConj g = griessIso ∘ (ℂ ⊗ g) ∘ griessIso⁻¹ : V♮₂ ≃ₗ[ℂ] V♮₂`.

It is a group homomorphism on all of `GL_ℚ(SpaceB)`, injective because the rational dictionary
`griessNat` is injective (`bform` is positive definite).  For `g ∈ AutO` (`IsAlgAut g` and
`bform`-preservation) it preserves the Griess product of `V♮` (`griessIso_mul`) and the invariant
form `natForm` (`griessIso_form`).

The Griess automorphism group `GriessAutVnat` of `V♮` is defined with the **intrinsic** form
`u₍₃₎v = ⟨u, v⟩₃ · 𝟙` (`GriessAut.griessForm`).  On `V♮₂` that form *is* `natForm`
(`griessForm_eq_natForm`): FHL invariance of `natForm` at weight two, `L₁ V♮₂ = 0`, creation
`u₍₋₁₎𝟙 = u` and `natForm(𝟙, 𝟙) = 1`.  Hence `griessConj` maps `AutO` into `GriessAutVnat`,
and every automorphism of `V♮` preserves `natForm` on `V♮₂` (`natForm_autRestrict`).

## Main results
* `griessBaseChange`, `griessBaseChange_gmul`, `griessBaseChange_bform`.
* ⭐ `griessConj`, `griessConj_griessIso`, `griessConj_griessNat` (`griessConj g (griessNat u) =
  griessNat (g u)`), `griessConjHom : (SpaceB ≃ₗ[ℚ] SpaceB) →* (V♮₂ ≃ₗ[ℂ] V♮₂)`,
  `griessConjHom_injective`.
* ⭐ `griessConj_griessMul`, ⭐ `griessConj_natForm` (for `g ∈ AutO`).
* `griessNat_injective`, ⭐ `griessForm_eq_natForm`, `natForm_autRestrict`.
* ⭐ `griessConjAut : AutO →* GriessAutVnat`, `griessConjAut_injective`.
* `vnatWeightTwoRestrict : AutVnat →* (V♮₂ ≃ₗ[ℂ] V♮₂)`, `vnatWeightTwoRestrict_injective`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterAction

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess
open scoped TensorProduct

/-! ## Base change of a rational automorphism of `SpaceB` -/

/-- The `ℂ`-linear extension `ℂ ⊗ g : ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] ℂ ⊗[ℚ] SpaceB` of a `ℚ`-linear
automorphism `g` of Axiom's Griess algebra. -/
noncomputable def griessBaseChange (g : SpaceB ≃ₗ[ℚ] SpaceB) : ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] ℂ ⊗[ℚ] SpaceB :=
  g.baseChange ℚ ℂ SpaceB SpaceB

@[simp] theorem griessBaseChange_tmul (g : SpaceB ≃ₗ[ℚ] SpaceB) (a : ℂ) (u : SpaceB) :
    griessBaseChange g (a ⊗ₜ u) = a ⊗ₜ g u := rfl

/-- The base change of an algebra automorphism preserves the base-changed product. -/
theorem griessBaseChange_gmul {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : IsAlgAut g) (x y : ℂ ⊗[ℚ] SpaceB) :
    griessBaseChange g (LinearMap.BilinMap.baseChange ℂ gmul x y)
      = LinearMap.BilinMap.baseChange ℂ gmul (griessBaseChange g x) (griessBaseChange g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul b v =>
          rw [LinearMap.BilinMap.baseChange_tmul, griessBaseChange_tmul, griessBaseChange_tmul,
            griessBaseChange_tmul, LinearMap.BilinMap.baseChange_tmul, hg]

/-- The base change of a `bform`-isometry is an isometry of the base-changed form. -/
theorem griessBaseChange_bform {g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hg : ∀ u v, bform (g u) (g v) = bform u v) (x y : ℂ ⊗[ℚ] SpaceB) :
    LinearMap.BilinForm.baseChange ℂ bform (griessBaseChange g x) (griessBaseChange g y)
      = LinearMap.BilinForm.baseChange ℂ bform x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul b v =>
          rw [griessBaseChange_tmul, griessBaseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
            LinearMap.BilinForm.baseChange_tmul, hg]

/-! ## The Griess conjugate -/

/-- ⭐ **The Griess conjugate** of a `ℚ`-linear automorphism `g` of `SpaceB`:
`griessIso ∘ (ℂ ⊗ g) ∘ griessIso⁻¹ : V♮₂ ≃ₗ[ℂ] V♮₂`. -/
noncomputable def griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) :
    VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2 :=
  griessIso.symm ≪≫ₗ griessBaseChange g ≪≫ₗ griessIso

theorem griessConj_apply (g : SpaceB ≃ₗ[ℚ] SpaceB) (v : VnatVOA.grading 2) :
    griessConj g v = griessIso (griessBaseChange g (griessIso.symm v)) := rfl

/-- `griessConj g ∘ griessIso = griessIso ∘ (ℂ ⊗ g)`. -/
theorem griessConj_griessIso (g : SpaceB ≃ₗ[ℚ] SpaceB) (x : ℂ ⊗[ℚ] SpaceB) :
    griessConj g (griessIso x) = griessIso (griessBaseChange g x) := by
  rw [griessConj_apply, LinearEquiv.symm_apply_apply]

/-- ⭐ **On the rational dictionary** `griessConj g` is `g`: `griessConj g (griessNat u) = griessNat (g u)`. -/
theorem griessConj_griessNat (g : SpaceB ≃ₗ[ℚ] SpaceB) (u : SpaceB) :
    griessConj g (griessNat u) = griessNat (g u) := by
  rw [← griessIso_tmul, griessConj_griessIso, griessBaseChange_tmul, griessIso_tmul]

theorem griessConj_one : griessConj 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [griessConj_apply, griessBaseChange, LinearEquiv.baseChange_one]
  change griessIso (griessIso.symm v) = v
  rw [LinearEquiv.apply_symm_apply]

theorem griessBaseChange_mul (g h : SpaceB ≃ₗ[ℚ] SpaceB) :
    griessBaseChange (g * h) = griessBaseChange g * griessBaseChange h := by
  simp only [griessBaseChange, LinearEquiv.baseChange_mul]

theorem griessConj_mul (g h : SpaceB ≃ₗ[ℚ] SpaceB) :
    griessConj (g * h) = griessConj g * griessConj h := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, griessConj_apply h v, griessConj_griessIso, griessConj_apply,
    griessBaseChange_mul, LinearEquiv.mul_apply]

/-- ⭐ **The Griess conjugation homomorphism** `GL_ℚ(SpaceB) →* GL_ℂ(V♮₂)`. -/
noncomputable def griessConjHom : (SpaceB ≃ₗ[ℚ] SpaceB) →* (VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2) where
  toFun := griessConj
  map_one' := griessConj_one
  map_mul' := griessConj_mul

@[simp] theorem griessConjHom_apply (g : SpaceB ≃ₗ[ℚ] SpaceB) : griessConjHom g = griessConj g := rfl

/-- **The rational dictionary is injective**: `natForm (griessNat u) (griessNat u) = 2 bform u u` and
`bform` is positive definite. -/
theorem griessNat_injective : Function.Injective griessNat := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  refine bform_self_eq_zero ?_
  have h := griessNat_form u u
  rw [hu, ZeroMemClass.coe_zero, map_zero] at h
  have h2 : ((bform u u : ℚ) : ℂ) = 0 := by
    have := h.symm
    rwa [mul_eq_zero, or_iff_right (two_ne_zero)] at this
  exact_mod_cast h2

/-- ⭐ **Griess conjugation is injective**: `griessConj g` determines `g`. -/
theorem griessConjHom_injective : Function.Injective griessConjHom := by
  intro g h hgh
  refine LinearEquiv.ext fun u => griessNat_injective ?_
  rw [← griessConj_griessNat, ← griessConj_griessNat]
  exact congrArg (fun k : VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2 => k (griessNat u)) hgh

/-! ## Elements of `AutO` preserve the Griess product and the form of `V♮` -/

/-- ⭐ **`griessConj g` preserves the Griess product of `V♮`** for every algebra automorphism `g`
of `SpaceB`. -/
theorem griessConj_griessMul {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : IsAlgAut g) (u v : VnatVOA.grading 2) :
    griessConj g (VnatVOA.griessMul u v) = VnatVOA.griessMul (griessConj g u) (griessConj g v) := by
  obtain ⟨x, rfl⟩ := griessIso.surjective u
  obtain ⟨y, rfl⟩ := griessIso.surjective v
  rw [← griessIso_mul, griessConj_griessIso, griessConj_griessIso, griessConj_griessIso,
    griessBaseChange_gmul hg, griessIso_mul]

/-- ⭐ **`griessConj g` preserves `natForm` on `V♮₂`** for every `bform`-isometry `g` of `SpaceB`. -/
theorem griessConj_natForm {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : ∀ u v, bform (g u) (g v) = bform u v)
    (u v : VnatVOA.grading 2) :
    SimpleNat.natForm (griessConj g u : Vnat) (griessConj g v : Vnat)
      = SimpleNat.natForm (u : Vnat) (v : Vnat) := by
  obtain ⟨x, rfl⟩ := griessIso.surjective u
  obtain ⟨y, rfl⟩ := griessIso.surjective v
  rw [griessConj_griessIso, griessConj_griessIso, griessIso_form, griessIso_form,
    griessBaseChange_bform hg]

/-! ## The intrinsic Griess form of `V♮` is `natForm` -/

/-- ⭐ **On `V♮₂` the intrinsic Griess form is `natForm`**: `u₍₃₎v = natForm(u, v) · 𝟙`.
FHL invariance of `natForm` at weight two (`natForm_fhl`), `L₁ V♮₂ = 0`, `u₍₋₁₎𝟙 = u` and
`natForm(𝟙, 𝟙) = 1`. -/
theorem griessForm_eq_natForm (u v : VnatVOA.grading 2) :
    GriessAut.griessForm VnatVOA_vacuum_ne_zero u v = SimpleNat.natForm (u : Vnat) (v : Vnat) := by
  have hu : (u : Vnat) ∈ gradingNat 2 := by rw [← VnatVOA_grading]; exact u.2
  have h := SimpleNat.natForm_fhl vnat_twistedLocality 2 (u : Vnat) hu 3 (v : Vnat) VnatVOA.vacuum
  change SimpleNat.natForm (VnatVOA.smul (u : Vnat) 3 (v : Vnat)) VnatVOA.vacuum = (-1 : ℂ) ^ (2 : ℤ) •
      ∑ j ∈ Finset.range ((2 : ℤ).toNat + 1), ((j.factorial : ℂ)⁻¹) •
        SimpleNat.natForm (v : Vnat)
          (VnatVOA.smul ((VnatVOA.L 1 ^ j) (u : Vnat)) (2 * 2 - 3 - 2 - (j : ℤ)) VnatVOA.vacuum) at h
  rw [show (2 : ℤ).toNat + 1 = 3 by rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hL := vnat_L_one_of_two hu
  have h1 : (VnatVOA.L 1 ^ 1) (u : Vnat) = 0 := by rw [pow_one, hL]
  have h2 : (VnatVOA.L 1 ^ 2) (u : Vnat) = 0 := by rw [pow_two, Module.End.mul_apply, hL, map_zero]
  rw [h1, h2, pow_zero, Module.End.one_apply,
    show (2 * 2 - 3 - 2 - ((0 : ℕ) : ℤ) : ℤ) = -1 by norm_num, VnatVOA.smul_vacuum_neg_one,
    GriessAut.griessForm_spec VnatVOA_vacuum_ne_zero u v] at h
  simp only [PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero, zero_add] at h
  have hvac : SimpleNat.natForm VnatVOA.vacuum VnatVOA.vacuum = 1 :=
    SimpleNat.natInvForm_normalized vnat_twistedLocality
  rw [map_smul, LinearMap.smul_apply, hvac, smul_eq_mul, mul_one] at h
  rw [h, SimpleNat.natForm_symm]
  norm_num

/-- **Every automorphism of `V♮` preserves `natForm` on `V♮₂`** (`griessForm_aut` for the intrinsic
form, which is `natForm` there). -/
theorem natForm_autRestrict (h : AutVnat) (u v : VnatVOA.grading 2) :
    SimpleNat.natForm (h (u : Vnat)) (h (v : Vnat)) = SimpleNat.natForm (u : Vnat) (v : Vnat) := by
  have := GriessAut.griessForm_aut VnatVOA_vacuum_ne_zero h u v
  rw [griessForm_eq_natForm, griessForm_eq_natForm, GriessAut.autRestrict_coe,
    GriessAut.autRestrict_coe] at this
  exact this

/-- `griessConj g` preserves the intrinsic Griess form for every `bform`-isometry `g`. -/
theorem griessConj_griessForm {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : ∀ u v, bform (g u) (g v) = bform u v)
    (u v : VnatVOA.grading 2) :
    GriessAut.griessForm VnatVOA_vacuum_ne_zero (griessConj g u) (griessConj g v)
      = GriessAut.griessForm VnatVOA_vacuum_ne_zero u v := by
  rw [griessForm_eq_natForm, griessForm_eq_natForm, griessConj_natForm hg]

/-- ⭐ **Every element of `AutO` is a Griess automorphism of `V♮`** after conjugation by `griessIso`. -/
theorem griessConj_mem_griessAutVnat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) :
    griessConj g ∈ GriessAutVnat :=
  ⟨fun u v => griessConj_griessMul hg.1 u v, fun u v => griessConj_griessForm hg.2 u v⟩

/-- ⭐ **`AutO` embeds in the Griess automorphism group of `V♮`**: `g ↦ griessIso ∘ (ℂ ⊗ g) ∘ griessIso⁻¹`. -/
noncomputable def griessConjAut : AutO →* GriessAutVnat :=
  MonoidHom.codRestrict (griessConjHom.comp AutO.subtype) GriessAutVnat
    fun g => griessConj_mem_griessAutVnat g.2

@[simp] theorem griessConjAut_coe (g : AutO) :
    ((griessConjAut g : GriessAutVnat) : VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2)
      = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) := rfl

theorem griessConjAut_injective : Function.Injective griessConjAut := by
  intro g h hgh
  refine Subtype.ext (griessConjHom_injective ?_)
  have := congrArg (fun k : GriessAutVnat => (k : VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2)) hgh
  simpa using this

/-! ## Restriction of `Aut V♮` to `V♮₂` as linear automorphisms -/

/-- The restriction `AutVnat →* GL_ℂ(V♮₂)`, `h ↦ h|_{V♮₂}`. -/
noncomputable def vnatWeightTwoRestrict : AutVnat →* (VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2) :=
  GriessAutVnat.subtype.comp vnatGriessRestrict

@[simp] theorem vnatWeightTwoRestrict_apply_coe (h : AutVnat) (v : VnatVOA.grading 2) :
    ((vnatWeightTwoRestrict h v : VnatVOA.grading 2) : Vnat) = h (v : Vnat) := rfl

theorem vnatWeightTwoRestrict_eq (h : AutVnat) :
    vnatWeightTwoRestrict h = ((vnatGriessRestrict h : GriessAutVnat) : VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2) :=
  rfl

/-- **`Aut V♮` acts faithfully on `V♮₂`** (`vnatGriessRestrict_injective`). -/
theorem vnatWeightTwoRestrict_injective : Function.Injective vnatWeightTwoRestrict :=
  Subtype.coe_injective.comp vnatGriessRestrict_injective

end VOA.Moonshine.MonsterAction

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ATransformMain
import VOA.Huang.FusionUnit
import VOA.Huang.BraidingSkewJacobi

/-!
# The double contragredient and the symmetry `N^{M₃}_{M₁M₂} = N^{M₂'}_{M₁M₃'}` (FHL 5.3.1, 5.5.2)

* `doubleDualEquiv : M ≅ M''` — the evaluation map `x ↦ ⟨x, ·⟩` into the contragredient of
  the contragredient is a module isomorphism (FHL Prop. 5.3.1), for every ordinary module
  (finite-dimensional weight spaces). The module-map property is `(Y°)° = Y`
  (`dualPairing_oppB_contra`).
* `fusionRule_atrans_eq` — **FHL Prop. 5.5.2 as an equality of fusion rules**: if
  `I(M₂' / M₁ M₃')` is finite-dimensional then `N^{M₃}_{M₁M₂} = N^{M₂'}_{M₁M₃'}` (the `A`-transform
  applied twice, with `M'' ≅ M` in the second and third slots).

Together with skew-symmetry (`fusionRule_swap`) this is the `S₃`-symmetry of fusion rules.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.ATransform

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiRegular VOA.Huang.LiFusion VOA.Huang.FusionUnit
  VOA.Huang.BraidingSkew VOA.Huang.HuangODEContra
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-! ## The evaluation map `M → M''` -/

section DoubleDual

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)

/-- The `α`-piece of the evaluation map: `x ∈ M_α ↦ (ψ ∈ (M')_α ↦ ⟨x, ψ⟩)`. -/
noncomputable def evPiece (α : ℂ) :
    A.weight α →ₗ[ℂ] Module.Dual ℂ ((contragredientModule A).weight α) where
  toFun x :=
    { toFun := fun ψ => dualPairing A (x : M) (ψ : RestrictedDual A)
      map_add' := fun ψ ψ' => by simp only [Submodule.coe_add, map_add]
      map_smul' := fun c ψ => by simp only [SetLike.val_smul, map_smul, RingHom.id_apply] }
  map_add' x y := by
    ext ψ
    simp only [Submodule.coe_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    exact dualPairing_add_left A _ _ _
  map_smul' c x := by
    ext ψ
    simp only [SetLike.val_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      RingHom.id_apply]
    exact dualPairing_smul_left A _ _ _

/-- The evaluation map `M → M''`. -/
noncomputable def evDD : M →ₗ[ℂ] RestrictedDual (contragredientModule A) :=
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  (DirectSum.toModule ℂ ℂ _ (fun α => (DirectSum.lof ℂ ℂ
    (fun β => Module.Dual ℂ ((contragredientModule A).weight β)) α).comp (evPiece A α))).comp
    (DirectSum.decomposeLinearEquiv A.weight).toLinearMap

theorem evDD_homog {α : ℂ} {x : M} (hx : x ∈ A.weight α) :
    evDD A x = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ ((contragredientModule A).weight β)) α
      (evPiece A α ⟨x, hx⟩) := by
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  unfold evDD
  erw [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem A.weight hx, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
  rfl

/-- **The evaluation pairing**: `⟨ψ, ev x⟩_{M'} = ⟨x, ψ⟩_M`. -/
theorem evDD_pairing (x : M) (ψ : RestrictedDual A) :
    dualPairing (contragredientModule A) ψ (evDD A x) = dualPairing A x ψ := by
  induction x using FusionTop.induction_weight (A₁ := A) with
  | h0 => rw [map_zero, map_zero]; exact (dualPairing_zero_x A ψ).symm
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, dualPairing_add_left]
  | hhom α x hx =>
    rw [evDD_homog A hx]
    induction ψ using DirectSum.induction_on with
    | zero =>
      erw [map_zero]
      exact dualPairing_zero_x (contragredientModule A) _
    | of β g =>
      rw [← DirectSum.lof_eq_of ℂ, dualPairing_lof]
      have hmem : DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (A.weight γ)) β g
          ∈ (contragredientModule A).weight β := ⟨g, rfl⟩
      by_cases h : α = β
      · subst h
        rw [show internalProjTo (contragredientModule A).isInternal α
            (DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (A.weight γ)) α g)
            = ⟨_, hmem⟩ from internalProjTo_coe _ α ⟨_, hmem⟩]
        rfl
      · rw [internalProjTo_eq_zero_of_ne (contragredientModule A) hmem h, map_zero,
          dualPairing_lof, internalProjTo_eq_zero_of_ne A hx (Ne.symm h), map_zero]
    | add ψ ψ' hψ hψ' => erw [dualPairing_add_left, hψ, hψ', map_add]

theorem evDD_injective : Function.Injective (evDD A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_pairing A (fun ψ => ?_)
  rw [← evDD_pairing, hx]
  exact map_zero _

theorem evDD_surjective : Function.Surjective (evDD A) := by
  classical
  haveI : ∀ α, FiniteDimensional ℂ (A.weight α) := A.finrank
  -- each generator is hit
  have hgen : ∀ (α : ℂ) (Φ : Module.Dual ℂ ((contragredientModule A).weight α)),
      ∃ x, evDD A x = DirectSum.lof ℂ ℂ
        (fun β => Module.Dual ℂ ((contragredientModule A).weight β)) α Φ := by
    intro α Φ
    let L : Module.Dual ℂ (A.weight α) →ₗ[ℂ] (contragredientModule A).weight α :=
      { toFun := fun g => ⟨DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (A.weight γ)) α g, g, rfl⟩
        map_add' := fun g g' => Subtype.ext (map_add _ g g')
        map_smul' := fun c g => Subtype.ext (map_smul _ c g) }
    set x : A.weight α := (Module.evalEquiv ℂ (A.weight α)).symm (Φ.comp L) with hxdef
    refine ⟨(x : M), ?_⟩
    rw [evDD_homog A x.2]
    congr 1
    ext ψ
    obtain ⟨g, hg⟩ := ψ.2
    have hψ : ψ = L g := Subtype.ext hg.symm
    rw [hψ]
    change dualPairing A (x : M) (DirectSum.lof ℂ ℂ (fun γ => Module.Dual ℂ (A.weight γ)) α g)
      = Φ (L g)
    rw [dualPairing_lof, internalProjTo_coe]
    have h := Module.apply_evalEquiv_symm_apply ℂ (A.weight α) g (Φ.comp L)
    rw [← hxdef] at h
    exact h
  intro Ψ
  induction Ψ using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of α Φ =>
    obtain ⟨x, hx⟩ := hgen α Φ
    exact ⟨x, by rw [hx, DirectSum.lof_eq_of]⟩
  | add Ψ Ψ' hΨ hΨ' =>
    obtain ⟨x, hx⟩ := hΨ
    obtain ⟨x', hx'⟩ := hΨ'
    exact ⟨x + x', by rw [map_add, hx, hx']; rfl⟩

/-- **`M ≅ M''`** (FHL Prop. 5.3.1): the evaluation map is a module isomorphism. -/
noncomputable def doubleDualEquiv :
    ModuleEquiv W A (contragredientModule (contragredientModule A)) where
  toLinearEquiv := LinearEquiv.ofBijective (evDD A) ⟨evDD_injective A, evDD_surjective A⟩
  map_act u n x := by
    simp only [LinearEquiv.ofBijective_apply, WeakModule.act_def]
    refine restrictedDual_ext (contragredientModule A) (fun ψ => ?_)
    change dualPairing (contragredientModule A) ψ (evDD A (mode (A.YM u) n x))
      = dualPairing (contragredientModule A) ψ
          (mode ((contragredientModule (contragredientModule A)).YM u) n (evDD A x))
    rw [dualPairing_contra_mode, evDD_pairing, evDD_pairing, dualPairing_oppB_contra]

end DoubleDual

/-! ## The symmetry of fusion rules -/

section Symmetry

variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
  (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)

/-- A module isomorphism in the third slot identifies intertwiner spaces. -/
noncomputable def equivRight {M₄ : Type u} [AddCommGroup M₄] [Module ℂ M₄] {A₄ : OrdVModule W M₄}
    (e : ModuleEquiv W A₃ A₄) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₁ A₂ A₄ where
  toFun Y := ⟨fun n => ((Y : IntertwiningModes M₁ M₂ M₃) n).compr₂
      (e.toLinearEquiv : M₃ →ₗ[ℂ] M₄),
    isIntertwiningOperator_compHom Y.2 (fun u n x => e.map_act u n x)⟩
  invFun Y := ⟨fun n => ((Y : IntertwiningModes M₁ M₂ M₄) n).compr₂
      (e.symm.toLinearEquiv : M₄ →ₗ[ℂ] M₃),
    isIntertwiningOperator_compHom Y.2 (fun u n x => e.symm.map_act u n x)⟩
  map_add' Y Y' := Subtype.ext (by funext n; ext; simp)
  map_smul' c Y := Subtype.ext (by funext n; ext; simp)
  left_inv Y := Subtype.ext (by
    funext n; ext x y
    simp only [LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.toLinearEquiv.symm_apply_apply _)
  right_inv Y := Subtype.ext (by
    funext n; ext x y
    simp only [LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.toLinearEquiv.apply_symm_apply _)

/-- A module isomorphism in the second slot identifies intertwiner spaces. -/
noncomputable def equivMid {M₄ : Type u} [AddCommGroup M₄] [Module ℂ M₄] {A₄ : OrdVModule W M₄}
    (e : ModuleEquiv W A₂ A₄) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₁ A₄ A₃ :=
  (skewEquiv A₁ A₂ A₃ omegaPhase_succ omegaPhase_ne_zero).trans
    ((intertwiningEquivLeft (A₂ := A₁) (A₃ := A₃) e.symm).trans
      (skewEquiv A₄ A₁ A₃ omegaPhase_succ omegaPhase_ne_zero))

/-- **FHL Prop. 5.5.2 (fusion-rule form)**: `N^{M₃}_{M₁M₂} = N^{M₂'}_{M₁M₃'}` whenever
`I(M₂' / M₁ M₃')` is finite-dimensional (both spaces are then finite-dimensional). -/
theorem fusionRule_atrans_eq
    [FiniteDimensional ℂ (intertwiningSpace A₁ (contragredientModule A₃)
      (contragredientModule A₂))] :
    fusionRule A₁ A₂ A₃ = fusionRule A₁ (contragredientModule A₃) (contragredientModule A₂) := by
  haveI := finiteDimensional_of_atrans A₁ A₂ A₃
  -- the second `A`-transform lands in `I(M₃'' / M₁ M₂'') ≅ I(M₃ / M₁ M₂)`
  let E : intertwiningSpace A₁ (contragredientModule (contragredientModule A₂))
        (contragredientModule (contragredientModule A₃)) ≃ₗ[ℂ] intertwiningSpace A₁ A₂ A₃ :=
    (equivRight A₁ _ _ (doubleDualEquiv A₃).symm).trans
      (equivMid A₁ _ _ (doubleDualEquiv A₂).symm)
  haveI : FiniteDimensional ℂ (intertwiningSpace A₁
      (contragredientModule (contragredientModule A₂))
      (contragredientModule (contragredientModule A₃))) := LinearEquiv.finiteDimensional E.symm
  refine le_antisymm (fusionRule_le_atrans A₁ A₂ A₃) ?_
  calc fusionRule A₁ (contragredientModule A₃) (contragredientModule A₂)
      ≤ fusionRule A₁ (contragredientModule (contragredientModule A₂))
          (contragredientModule (contragredientModule A₃)) :=
        fusionRule_le_atrans A₁ (contragredientModule A₃) (contragredientModule A₂)
    _ = fusionRule A₁ A₂ A₃ := E.finrank_eq

end Symmetry

end VOA.Huang.ATransform

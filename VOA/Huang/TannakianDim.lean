/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianSymmetric
import VOA.Huang.TannakianRepG

/-!
# Braided dimensions: independence, `Rep(G)`, transport

* `toScalar_eq_of_smul` — `toScalar (c • 𝟙) = c` from `𝟙 ≠ 0` alone;
* `coev_braid_ev_indep` — `ε ∘ c_{X,Y} ∘ η` does not depend on the choice of right dual `Y`
  (mates of `𝟙_X` + naturality of the braiding);
* `symDim_fgModuleCat`, `coev_braid_ev_fdRep`, `symDim_fdRep` — in `FGModuleCat ℂ` and in
  `FDRep ℂ G` the braided dimension is `finrank` (so `FDRep ℂ G` satisfies the positivity
  hypothesis of `DeligneTannakian` on nonzero objects: the hypothesis is consistent);
* `symDim_eq_of_braided` — braided, `ℂ`-linear, fully faithful, essentially surjective functors
  preserve `symDim` (pull the target's dual back by `ExactPairing.ofFullyFaithful`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

section General

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]

/-- `toScalar f = c` as soon as `f = c • 𝟙` and `𝟙 ≠ 0` (no dimension hypothesis). -/
theorem toScalar_eq_of_smul (h1 : 𝟙 (𝟙_ C) ≠ 0) {f : 𝟙_ C ⟶ 𝟙_ C} {c : ℂ} (hf : c • 𝟙 (𝟙_ C) = f) :
    toScalar f = c := by
  have hex : ∃ c : ℂ, c • 𝟙 (𝟙_ C) = f := ⟨c, hf⟩
  rw [toScalar, dif_pos hex]
  exact smul_left_injective ℂ h1 (hex.choose_spec.trans hf.symm)

variable [BraidedCategory C]

/-- The braided trace of the identity does not depend on the choice of right dual. -/
theorem coev_braid_ev_indep {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    η_ X Y₁ ≫ (β_ X Y₁).hom ≫ ε_ X Y₁ = η_ X Y₂ ≫ (β_ X Y₂).hom ≫ ε_ X Y₂ := by
  let u : Y₁ ⟶ Y₂ := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  have hη : η_ X Y₁ ≫ X ◁ u = η_ X Y₂ := by
    have := @coevaluation_comp_rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
    simpa using this
  have hε : (u ▷ X) ≫ ε_ X Y₂ = ε_ X Y₁ := by
    have := @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
    simpa using this
  rw [← hη, ← hε, Category.assoc, BraidedCategory.braiding_naturality_right_assoc]

end General

/-! ## `symDim` in `FGModuleCat ℂ` and in `FDRep ℂ G` is the dimension -/

/-- In `FGModuleCat ℂ`, `ε ∘ c ∘ η = (dim V) • 𝟙`. -/
theorem coev_braid_ev_fgModuleCat (V : FGModuleCat ℂ) :
    η_ V Vᘁ ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ = (finrank ℂ V : ℂ) • 𝟙 (𝟙_ (FGModuleCat ℂ)) := by
  ext : 3
  change (FGModuleCat.FGModuleCatEvaluation ℂ V).hom.hom ((β_ V.obj (FGModuleCat.FGModuleCatDual ℂ V).obj).hom.hom ((FGModuleCat.FGModuleCatCoevaluation ℂ V).hom.hom (1 : ℂ))) = (finrank ℂ V : ℂ) * 1
  rw [show (FGModuleCat.FGModuleCatCoevaluation ℂ V).hom.hom (1 : ℂ) = _ from FGModuleCat.FGModuleCatCoevaluation_apply_one ℂ V]
  erw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun x _ => by
    erw [ModuleCat.MonoidalCategory.braiding_hom_apply, FGModuleCat.FGModuleCatEvaluation_apply]
    change (Basis.ofVectorSpace ℂ V).coord x ((Basis.ofVectorSpace ℂ V) x) = 1
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]]
  rw [Finset.sum_const, Finset.card_univ, ← finrank_eq_card_basis (Basis.ofVectorSpace ℂ V)]
  simp

theorem id_unit_ne_zero_fgModuleCat : 𝟙 (𝟙_ (FGModuleCat ℂ)) ≠ 0 := by
  intro h
  have := congrArg (fun f : 𝟙_ (FGModuleCat ℂ) ⟶ 𝟙_ (FGModuleCat ℂ) => f.hom.hom (1 : ℂ)) h
  simp at this
  exact one_ne_zero (α := ℂ) this

/-- `symDim V = dim V` in `FGModuleCat ℂ`. -/
theorem symDim_fgModuleCat (V : FGModuleCat ℂ) : symDim V = (finrank ℂ V : ℂ) :=
  toScalar_eq_of_smul id_unit_ne_zero_fgModuleCat (coev_braid_ev_fgModuleCat V).symm

section FDRep

variable {G : Type} [Group G]

/-- The underlying pairing of the `FDRep` duality is an exact pairing in `FGModuleCat`. -/
@[reducible] def fdRepUnderlyingPairing (X : FDRep ℂ G) : ExactPairing X.V (Xᘁ).V where
  coevaluation' := (η_ X Xᘁ).hom
  evaluation' := (ε_ X Xᘁ).hom
  coevaluation_evaluation' := by
    have := congrArg Action.Hom.hom (ExactPairing.coevaluation_evaluation X Xᘁ)
    simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.whiskerRight_hom, Action.associator_inv_hom, Action.leftUnitor_inv_hom, Action.rightUnitor_hom_hom] at this
    exact this
  evaluation_coevaluation' := by
    have := congrArg Action.Hom.hom (ExactPairing.evaluation_coevaluation X Xᘁ)
    simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.whiskerRight_hom, Action.associator_hom_hom, Action.leftUnitor_hom_hom, Action.rightUnitor_inv_hom] at this
    exact this

theorem id_unit_ne_zero_fdRep : 𝟙 (𝟙_ (FDRep ℂ G)) ≠ 0 := by
  intro h
  exact id_unit_ne_zero_fgModuleCat (congrArg Action.Hom.hom h)

/-- In `FDRep ℂ G`, `ε ∘ c ∘ η = (dim X) • 𝟙`. -/
theorem coev_braid_ev_fdRep (X : FDRep ℂ G) :
    η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (finrank ℂ X : ℂ) • 𝟙 (𝟙_ (FDRep ℂ G)) := by
  apply Action.hom_ext
  have h1 := coev_braid_ev_indep (fdRepUnderlyingPairing X) (inferInstance : ExactPairing X.V X.Vᘁ)
  rw [coev_braid_ev_fgModuleCat] at h1
  rw [Action.smul_hom, Action.comp_hom, Action.comp_hom, Action.β_hom_hom, Action.id_hom]
  exact h1

/-- **`symDim V = dim V` in `Rep(G)`**: the braided dimension of every finite-dimensional
representation is its dimension; in particular it is positive on nonzero representations, so
`FDRep ℂ G` satisfies the positivity hypothesis of `DeligneTannakian`. -/
theorem symDim_fdRep (X : FDRep ℂ G) : symDim X = (finrank ℂ X : ℂ) := by
  apply toScalar_eq_of_smul id_unit_ne_zero_fdRep
  apply Action.hom_ext
  have h1 := coev_braid_ev_indep (fdRepUnderlyingPairing X) (inferInstance : ExactPairing X.V X.Vᘁ)
  rw [coev_braid_ev_fgModuleCat] at h1
  rw [Action.smul_hom, Action.comp_hom, Action.comp_hom, Action.β_hom_hom, Action.id_hom]
  exact h1.symm

end FDRep

/-! ## Braided linear equivalences preserve `symDim` -/

section Transport

variable {D : Type*} [Category D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D] [RightRigidCategory D]
  {E : Type*} [Category E] [Preadditive E] [Linear ℂ E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E] [BraidedCategory E] [RightRigidCategory E]

/-- **Braided `ℂ`-linear equivalences preserve the braided dimension.**  If
`Φ : D ⥤ E` is braided, `ℂ`-linear, fully faithful and essentially surjective, `End 𝟙_D = ℂ`,
and `ε c η = s • 𝟙` for `Φ X` in `E`, then `symDim X = s`. -/
theorem symDim_eq_of_braided (Φ : D ⥤ E) [Φ.Braided] [Φ.Linear ℂ] [Φ.Full] [Φ.Faithful]
    [Φ.EssSurj] (hD : finrank ℂ (𝟙_ D ⟶ 𝟙_ D) = 1) (X : D) (s : ℂ)
    (hs : η_ (Φ.obj X) (Φ.obj X)ᘁ ≫ (β_ (Φ.obj X) (Φ.obj X)ᘁ).hom ≫ ε_ (Φ.obj X) (Φ.obj X)ᘁ =
      s • 𝟙 (𝟙_ E)) :
    symDim X = s := by
  -- a dual `Y` of `X` in `D` whose `Φ`-image is the chosen dual of `Φ X`
  let Y := Φ.objPreimage (Φ.obj X)ᘁ
  letI pE : ExactPairing (Φ.obj X) (Φ.obj Y) := exactPairingCongrRight (Φ.objObjPreimageIso _)
  letI pD : ExactPairing X Y := ExactPairing.ofFullyFaithful Φ X Y
  have hcoev : Φ.map (η_ X Y) = Functor.OplaxMonoidal.η Φ ≫ η_ (Φ.obj X) (Φ.obj Y) ≫
      Functor.LaxMonoidal.μ Φ X Y := by
    change Φ.map (Φ.preimage _) = _
    rw [Functor.map_preimage]
  have hev : Φ.map (ε_ X Y) = Functor.OplaxMonoidal.δ Φ Y X ≫ ε_ (Φ.obj X) (Φ.obj Y) ≫
      Functor.LaxMonoidal.ε Φ := by
    change Φ.map (Φ.preimage _) = _
    rw [Functor.map_preimage]
  -- the scalar in `E`, computed with the pairing `pE`
  have hE : η_ (Φ.obj X) (Φ.obj Y) ≫ (β_ (Φ.obj X) (Φ.obj Y)).hom ≫ ε_ (Φ.obj X) (Φ.obj Y) =
      s • 𝟙 (𝟙_ E) := by
    rw [coev_braid_ev_indep pE (inferInstance : ExactPairing (Φ.obj X) (Φ.obj X)ᘁ), hs]
  -- the scalar in `D`
  have h1D : 𝟙 (𝟙_ D) ≠ 0 := by
    intro h0
    have : ∀ g : 𝟙_ D ⟶ 𝟙_ D, g = 0 := fun g => by rw [← Category.id_comp g, h0, zero_comp]
    haveI : Subsingleton (𝟙_ D ⟶ 𝟙_ D) := ⟨fun a b => by rw [this a, this b]⟩
    rw [finrank_zero_of_subsingleton] at hD
    exact zero_ne_one hD
  set t := symDim X with ht
  have hDt : η_ X Y ≫ (β_ X Y).hom ≫ ε_ X Y = t • 𝟙 (𝟙_ D) := by
    rw [coev_braid_ev_indep pD (inferInstance : ExactPairing X Xᘁ), ht, symDim]
    exact (toScalar_smul_id hD _).symm
  -- apply `Φ`
  have hmap := congrArg Φ.map hDt
  rw [Functor.map_comp, Functor.map_comp, hcoev, hev, Functor.Linear.map_smul, Φ.map_id] at hmap
  have hbr := Functor.Braided.braided (F := Φ) X Y
  have hmid : Functor.LaxMonoidal.μ Φ X Y ≫ Φ.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ Φ Y X =
      (β_ (Φ.obj X) (Φ.obj Y)).hom := by
    rw [← Category.assoc, hbr, Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  simp only [Category.assoc] at hmap
  rw [← Category.assoc (Φ.map (β_ X Y).hom), ← Category.assoc (Functor.LaxMonoidal.μ Φ X Y),
    hmid] at hmap
  rw [← Category.assoc (β_ (Φ.obj X) (Φ.obj Y)).hom, ← Category.assoc (η_ (Φ.obj X) (Φ.obj Y)),
    ← Category.assoc (η_ (Φ.obj X) (Φ.obj Y)), Category.assoc (η_ (Φ.obj X) (Φ.obj Y)), hE,
    Linear.smul_comp, Category.id_comp, Linear.comp_smul, Functor.Monoidal.η_ε] at hmap
  -- `t • 𝟙 = s • 𝟙` on `Φ 𝟙`
  have hne : 𝟙 (Φ.obj (𝟙_ D)) ≠ 0 := by
    intro h0
    apply h1D
    apply Φ.map_injective
    rw [Φ.map_id, h0, Φ.map_zero]
  exact smul_left_injective ℂ hne hmap.symm

end Transport

end VOA.Huang.TensorCat

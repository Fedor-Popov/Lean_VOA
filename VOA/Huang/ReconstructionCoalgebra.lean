/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ReconstructionSemisimple
import VOA.Huang.ReconstructionCartier

/-!
# Tannaka reconstruction — `End(ω)` is a cocommutative bialgebra

For a monoidal, additive, `ℂ`-linear `ω : D ⥤ FGModuleCat ℂ` out of a fusion category, the algebra
`RAlg ω = ∏_i End(ω X_i)` (`ReconstructionSemisimple`) carries the comultiplication dual to the
tensor product:

* generic linear algebra: `homLin`, `endTensor` (`End V ⊗ End W ≃ End (V ⊗ W)`),
  `piEndTensorEquiv` (`(∏ End V_i) ⊗ (∏ End W_j) ≃ ∏_{(i,j)} End (V_i ⊗ W_j)`);
* `conjTensor a X Y = μ ≫ ext a (X ⊗ Y) ≫ δ`, `evPair X Y (a ⊗ b) = ext a X ⊗ ext b Y`, both
  natural (`conjTensor_natural`, `evPair_natural`); `natural2_eq` (a two-variable natural family
  is determined by its values on pairs of simples);
* `comulLin` (defined through `evS = piEndTensorEquiv` on simples), `evPair_comul`
  (`ev_{X,Y}(Δ a) = μ ≫ ext a (X ⊗ Y) ≫ δ` for **all** `X, Y`), `counitLin` with `extMor_unit`;
* `coalgebra` (coassociativity from the associativity of `μ`, counit laws from unitality),
  `bialgebra`, and, for braided `ω` out of a symmetric `D`, `isCocomm`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open CategoryTheory MonoidalCategory Limits Module TensorProduct Functor.LaxMonoidal
  Functor.OplaxMonoidal

universe v u

section Generic

/-- Morphisms of `FGModuleCat ℂ` as linear maps. -/
def homLin {V W : FGModuleCat ℂ} : (V ⟶ W) ≃ₗ[ℂ] (V →ₗ[ℂ] W) :=
  InducedCategory.homLinearEquiv.trans ModuleCat.homLinearEquiv

@[simp] theorem homLin_apply {V W : FGModuleCat ℂ} (f : V ⟶ W) : homLin f = f.hom.hom := rfl
@[simp] theorem homLin_symm_apply {V W : FGModuleCat ℂ} (f : V →ₗ[ℂ] W) :
    (homLin.symm f).hom.hom = f := rfl

/-- `End V ⊗ End W ≃ End (V ⊗ W)`. -/
def endTensor (V W : FGModuleCat ℂ) : (V ⟶ V) ⊗[ℂ] (W ⟶ W) ≃ₗ[ℂ] (V ⊗ W ⟶ V ⊗ W) :=
  (TensorProduct.congr (homLin (V := V) (W := V)) (homLin (V := W) (W := W))) ≪≫ₗ
    homTensorHomEquiv ℂ V W V W ≪≫ₗ (homLin (V := V ⊗ W) (W := V ⊗ W)).symm

@[simp] theorem endTensor_tmul {V W : FGModuleCat ℂ} (a : V ⟶ V) (b : W ⟶ W) :
    endTensor V W (a ⊗ₜ b) = (a ⊗ₘ b : V ⊗ W ⟶ V ⊗ W) := by
  apply FGModuleCat.hom_ext
  simp [endTensor]
  rfl

/-- Product-indexed currying. -/
def piProdEquiv {ι κ : Type*} (X : ι → κ → Type*) [∀ i j, AddCommGroup (X i j)]
    [∀ i j, Module ℂ (X i j)] : (∀ i j, X i j) ≃ₗ[ℂ] ∀ p : ι × κ, X p.1 p.2 where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `(∏ End V_i) ⊗ (∏ End W_j) ≃ ∏_{(i,j)} End (V_i ⊗ W_j)`. -/
def piEndTensorEquiv (V : ι → FGModuleCat ℂ) (W : κ → FGModuleCat ℂ) :
    (∀ i, V i ⟶ V i) ⊗[ℂ] (∀ j, W j ⟶ W j) ≃ₗ[ℂ] ∀ p : ι × κ, (V p.1 ⊗ W p.2 ⟶ V p.1 ⊗ W p.2) :=
  TensorProduct.piLeft ℂ (∀ j, W j ⟶ W j) (fun i => V i ⟶ V i) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i => TensorProduct.piRight ℂ ℂ (V i ⟶ V i) (fun j => W j ⟶ W j)) ≪≫ₗ
    piProdEquiv (fun i j => (V i ⟶ V i) ⊗[ℂ] (W j ⟶ W j)) ≪≫ₗ
    LinearEquiv.piCongrRight (fun p => endTensor (V p.1) (W p.2))

@[simp] theorem piEndTensorEquiv_tmul (V : ι → FGModuleCat ℂ) (W : κ → FGModuleCat ℂ)
    (a : ∀ i, V i ⟶ V i) (b : ∀ j, W j ⟶ W j) (p : ι × κ) :
    piEndTensorEquiv V W (a ⊗ₜ b) p = (a p.1 ⊗ₘ b p.2 : V p.1 ⊗ W p.2 ⟶ _) := by
  simp [piEndTensorEquiv, piProdEquiv]

/-- Endomorphisms of the unit of `FGModuleCat ℂ` are scalars. -/
theorem end_unit_eq_smul (f : 𝟙_ (FGModuleCat ℂ) ⟶ 𝟙_ (FGModuleCat ℂ)) :
    f = (show ℂ from f.hom.hom (1 : ℂ)) • 𝟙 (𝟙_ (FGModuleCat ℂ)) := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : ℂ)
  have h1 : f.hom.hom x = x • f.hom.hom (1 : ℂ) := by
    rw [← map_smul]; congr 1; exact (mul_one x).symm
  rw [h1]
  change x * (show ℂ from f.hom.hom (1 : ℂ)) = (show ℂ from f.hom.hom (1 : ℂ)) * x
  ring

theorem end_smul_tensor {V V' W W' : FGModuleCat ℂ} (t : ℂ) (f : V ⟶ V') (g : W ⟶ W') :
    (t • f) ⊗ₘ g = t • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def (C := FGModuleCat ℂ), MonoidalCategory.tensorHom_def (C := FGModuleCat ℂ),
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

theorem end_tensor_smul {V V' W W' : FGModuleCat ℂ} (t : ℂ) (f : V ⟶ V') (g : W ⟶ W') :
    f ⊗ₘ (t • g) = t • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def (C := FGModuleCat ℂ), MonoidalCategory.tensorHom_def (C := FGModuleCat ℂ),
    MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

end Generic

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

variable (ω : D ⥤ FGModuleCat ℂ) [ω.Braided] [ω.Additive] [ω.Linear ℂ]

/-- `μ ≫ ext a (X ⊗ Y) ≫ δ`. -/
def conjTensor (a : RAlg ω) (X Y : D) : ω.obj X ⊗ ω.obj Y ⟶ ω.obj X ⊗ ω.obj Y :=
  μ ω X Y ≫ extMor ω a (X ⊗ Y) ≫ δ ω X Y

theorem conjTensor_natural (a : RAlg ω) {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (ω.map f ⊗ₘ ω.map g) ≫ conjTensor ω a X' Y' = conjTensor ω a X Y ≫ (ω.map f ⊗ₘ ω.map g) := by
  unfold conjTensor
  rw [μ_natural_assoc, ← extMor_natural_assoc, ← δ_natural]
  simp only [Category.assoc]

/-- `conjTensor` as a linear map in `a`. -/
def conjLin (X Y : D) : RAlg ω →ₗ[ℂ] (ω.obj X ⊗ ω.obj Y ⟶ ω.obj X ⊗ ω.obj Y) where
  toFun a := conjTensor ω a X Y
  map_add' a b := by
    simp only [conjTensor, extMor_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' t a := by
    simp only [conjTensor, extMor_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

@[simp] theorem conjLin_apply (X Y : D) (a : RAlg ω) : conjLin ω X Y a = conjTensor ω a X Y := rfl

/-- `ev_{X,Y}(a ⊗ b) = ext a X ⊗ ext b Y`. -/
def evPair (X Y : D) : RAlg ω ⊗[ℂ] RAlg ω →ₗ[ℂ] (ω.obj X ⊗ ω.obj Y ⟶ ω.obj X ⊗ ω.obj Y) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b => extMor ω a X ⊗ₘ extMor ω b Y)
    (fun a a' b => by dsimp only; rw [extMor_add, MonoidalPreadditive.add_tensor])
    (fun t a b => by dsimp only; rw [extMor_smul, end_smul_tensor])
    (fun a b b' => by dsimp only; rw [extMor_add, MonoidalPreadditive.tensor_add])
    (fun t a b => by dsimp only; rw [extMor_smul, end_tensor_smul]))

@[simp] theorem evPair_tmul (X Y : D) (a b : RAlg ω) :
    evPair ω X Y (a ⊗ₜ b) = extMor ω a X ⊗ₘ extMor ω b Y := rfl

theorem evPair_natural (u : RAlg ω ⊗[ℂ] RAlg ω) {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (ω.map f ⊗ₘ ω.map g) ≫ evPair ω X' Y' u = evPair ω X Y u ≫ (ω.map f ⊗ₘ ω.map g) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [evPair_tmul, evPair_tmul, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      ← extMor_natural, ← extMor_natural]
  | add u v hu hv => rw [map_add, map_add, Preadditive.comp_add, Preadditive.add_comp, hu, hv]

theorem tensor_total {X Y : D} (d : Decomp X) (d' : Decomp Y) :
    ∑ k, ∑ l, (ω.map (d.π k) ⊗ₘ ω.map (d'.π l)) ≫ (ω.map (d.ι k) ⊗ₘ ω.map (d'.ι l)) = 𝟙 _ := by
  simp_rw [tensorHom_comp_tensorHom, ← tensor_sum, ← sum_tensor, map_total, id_tensorHom_id]

/-- A two-variable natural family of endomorphisms is determined by its values on pairs of
simples. -/
theorem natural2_eq {T T' : ∀ X Y : D, ω.obj X ⊗ ω.obj Y ⟶ ω.obj X ⊗ ω.obj Y}
    (hT : ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
      (ω.map f ⊗ₘ ω.map g) ≫ T X' Y' = T X Y ≫ (ω.map f ⊗ₘ ω.map g))
    (hT' : ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
      (ω.map f ⊗ₘ ω.map g) ≫ T' X' Y' = T' X Y ≫ (ω.map f ⊗ₘ ω.map g))
    (h : ∀ i j, T (F.simple i) (F.simple j) = T' (F.simple i) (F.simple j)) (X Y : D) :
    T X Y = T' X Y := by
  let d := decomp X
  let d' := decomp Y
  rw [← Category.id_comp (T X Y), ← Category.id_comp (T' X Y), ← tensor_total ω d d']
  simp only [Preadditive.sum_comp, Category.assoc, hT, hT', h]

/-- Evaluation on pairs of simples, as a linear equivalence. -/
def evS : RAlg ω ⊗[ℂ] RAlg ω ≃ₗ[ℂ]
    ∀ p : F.ι × F.ι, (ω.obj (F.simple p.1) ⊗ ω.obj (F.simple p.2) ⟶ ω.obj (F.simple p.1) ⊗ ω.obj (F.simple p.2)) :=
  piEndTensorEquiv (fun i => ω.obj (F.simple i)) (fun i => ω.obj (F.simple i))

theorem evS_tmul (a b : RAlg ω) (p : F.ι × F.ι) : evS ω (a ⊗ₜ b) p = a p.1 ⊗ₘ b p.2 :=
  piEndTensorEquiv_tmul _ _ a b p

theorem evS_apply (u : RAlg ω ⊗[ℂ] RAlg ω) (p : F.ι × F.ι) :
    evS ω u p = evPair ω (F.simple p.1) (F.simple p.2) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [evPair_tmul, extMor_simple, extMor_simple]
    exact piEndTensorEquiv_tmul _ _ a b p
  | add u v hu hv =>
    rw [map_add, map_add, Pi.add_apply, hu, hv]

/-- The comultiplication. -/
def comulLin : RAlg ω →ₗ[ℂ] RAlg ω ⊗[ℂ] RAlg ω :=
  (evS ω).symm.toLinearMap ∘ₗ LinearMap.pi (fun p : F.ι × F.ι => conjLin ω (F.simple p.1) (F.simple p.2))

theorem evS_comul (a : RAlg ω) (p : F.ι × F.ι) :
    evS ω (comulLin ω a) p = conjTensor ω a (F.simple p.1) (F.simple p.2) := by
  simp [comulLin]

/-- `ev_{X,Y}(Δ a) = μ ≫ ext a (X ⊗ Y) ≫ δ` for all `X, Y`. -/
theorem evPair_comul (a : RAlg ω) (X Y : D) : evPair ω X Y (comulLin ω a) = conjTensor ω a X Y :=
  natural2_eq ω (T := fun X Y => evPair ω X Y (comulLin ω a)) (T' := fun X Y => conjTensor ω a X Y)
    (fun f g => evPair_natural ω _ f g) (fun f g => conjTensor_natural ω a f g)
    (fun i j => by dsimp only; rw [← evS_apply ω _ (i, j), evS_comul]) X Y

/-- The counit, as the scalar by which `ext a` acts on `ω 𝟙`. -/
def counitLin : RAlg ω →ₗ[ℂ] ℂ where
  toFun a := (ε ω ≫ extMor ω a (𝟙_ D) ≫ η ω).hom.hom (1 : ℂ)
  map_add' a b := by
    simp only [extMor_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' t a := by
    simp only [extMor_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]
    rfl

theorem extMor_unit (a : RAlg ω) : extMor ω a (𝟙_ D) = counitLin ω a • 𝟙 _ := by
  have h := end_unit_eq_smul (ε ω ≫ extMor ω a (𝟙_ D) ≫ η ω)
  have : extMor ω a (𝟙_ D) = η ω ≫ (ε ω ≫ extMor ω a (𝟙_ D) ≫ η ω) ≫ ε ω := by
    simp only [Category.assoc, Functor.Monoidal.η_ε, Category.comp_id, Functor.Monoidal.η_ε_assoc]
  rw [this, h, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Functor.Monoidal.η_ε]
  rfl

theorem counitLin_eq {a : RAlg ω} {c : ℂ} (h : extMor ω a (𝟙_ D) = c • 𝟙 _) : counitLin ω a = c := by
  rw [extMor_unit] at h
  exact smul_left_injective ℂ (id_obj_unit_ne_zero ω) h

/-! ### Coassociativity -/

/-- Evaluation on triples of simples. -/
def evS3 : RAlg ω ⊗[ℂ] (RAlg ω ⊗[ℂ] RAlg ω) ≃ₗ[ℂ]
    ∀ p : F.ι × (F.ι × F.ι), (ω.obj (F.simple p.1) ⊗
      (ω.obj (F.simple p.2.1) ⊗ ω.obj (F.simple p.2.2)) ⟶ ω.obj (F.simple p.1) ⊗
      (ω.obj (F.simple p.2.1) ⊗ ω.obj (F.simple p.2.2))) :=
  TensorProduct.congr (LinearEquiv.refl ℂ (RAlg ω)) (evS ω) ≪≫ₗ
    piEndTensorEquiv (fun i => ω.obj (F.simple i))
      (fun p : F.ι × F.ι => ω.obj (F.simple p.1) ⊗ ω.obj (F.simple p.2))

theorem evS3_tmul (a : RAlg ω) (t : RAlg ω ⊗[ℂ] RAlg ω) (p : F.ι × (F.ι × F.ι)) :
    evS3 ω (a ⊗ₜ t) p = (a p.1 ⊗ₘ evS ω t p.2 : _ ⟶ _) := by
  rw [evS3, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  exact piEndTensorEquiv_tmul _ _ a _ p

theorem evS3_lTensor_comul (u : RAlg ω ⊗[ℂ] RAlg ω) (i j k : F.ι) :
    evS3 ω (comulLin ω |>.lTensor (RAlg ω) u) (i, (j, k)) =
      (ω.obj (F.simple i) ◁ μ ω (F.simple j) (F.simple k)) ≫
        evPair ω (F.simple i) (F.simple j ⊗ F.simple k) u ≫
          (ω.obj (F.simple i) ◁ δ ω (F.simple j) (F.simple k)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, evS3_tmul, evS_comul, evPair_tmul, extMor_simple]
    simp only [conjTensor, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
  | add u v hu hv =>
    rw [map_add, map_add, Pi.add_apply, hu, hv, map_add, Preadditive.add_comp,
      Preadditive.comp_add]

theorem evS3_assoc_tmul (t : RAlg ω ⊗[ℂ] RAlg ω) (c : RAlg ω) (i j k : F.ι) :
    evS3 ω (TensorProduct.assoc ℂ _ _ _ (t ⊗ₜ c)) (i, (j, k)) =
      (α_ _ _ _).inv ≫ (evS ω t (i, j) ⊗ₘ c k) ≫ (α_ _ _ _).hom := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.assoc_tmul, evS3_tmul, evS_tmul, evS_tmul]
    dsimp only
    rw [← associator_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  | add t s ht hs =>
    rw [TensorProduct.add_tmul, map_add, map_add, Pi.add_apply, ht, hs, map_add, Pi.add_apply,
      MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]

theorem evS3_assoc_rTensor_comul (u : RAlg ω ⊗[ℂ] RAlg ω) (i j k : F.ι) :
    evS3 ω (TensorProduct.assoc ℂ _ _ _ (comulLin ω |>.rTensor (RAlg ω) u)) (i, (j, k)) =
      (α_ _ _ _).inv ≫ (μ ω (F.simple i) (F.simple j) ▷ ω.obj (F.simple k)) ≫
        evPair ω (F.simple i ⊗ F.simple j) (F.simple k) u ≫
          (δ ω (F.simple i) (F.simple j) ▷ ω.obj (F.simple k)) ≫ (α_ _ _ _).hom := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, evS3_assoc_tmul, evS_comul, evPair_tmul, extMor_simple]
    simp only [conjTensor, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Category.comp_id, Category.assoc]
  | add u v hu hv =>
    rw [map_add, map_add, map_add, Pi.add_apply, hu, hv, map_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add]

theorem extMor_assoc (a : RAlg ω) (X Y Z : D) :
    extMor ω a ((X ⊗ Y) ⊗ Z) = ω.map (α_ X Y Z).hom ≫ extMor ω a (X ⊗ (Y ⊗ Z)) ≫ ω.map (α_ X Y Z).inv := by
  rw [← extMor_natural_assoc, ← ω.map_comp, Iso.hom_inv_id, ω.map_id, Category.comp_id]

theorem coassoc_simple (a : RAlg ω) (X Y Z : D) :
    (α_ _ _ _).inv ≫ (μ ω X Y ▷ ω.obj Z) ≫ conjTensor ω a (X ⊗ Y) Z ≫ (δ ω X Y ▷ ω.obj Z) ≫
      (α_ _ _ _).hom = (ω.obj X ◁ μ ω Y Z) ≫ conjTensor ω a X (Y ⊗ Z) ≫ (ω.obj X ◁ δ ω Y Z) := by
  unfold conjTensor
  rw [extMor_assoc]
  have h1 : μ ω X Y ▷ ω.obj Z ≫ μ ω (X ⊗ Y) Z ≫ ω.map (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫ ω.obj X ◁ μ ω Y Z ≫ μ ω X (Y ⊗ Z) := Functor.LaxMonoidal.associativity ω X Y Z
  have h2 : ω.map (α_ X Y Z).inv ≫ δ ω (X ⊗ Y) Z ≫ δ ω X Y ▷ ω.obj Z ≫ (α_ _ _ _).hom =
      δ ω X (Y ⊗ Z) ≫ ω.obj X ◁ δ ω Y Z := by
    rw [Functor.OplaxMonoidal.associativity, ← ω.map_comp_assoc, Iso.inv_hom_id, ω.map_id,
      Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem comul_coassoc :
    TensorProduct.assoc ℂ (RAlg ω) (RAlg ω) (RAlg ω) ∘ₗ (comulLin ω).rTensor (RAlg ω) ∘ₗ comulLin ω =
      (comulLin ω).lTensor (RAlg ω) ∘ₗ comulLin ω := by
  apply LinearMap.ext
  intro a
  apply (evS3 ω).injective
  funext ⟨i, j, k⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [evS3_assoc_rTensor_comul, evS3_lTensor_comul, evPair_comul, evPair_comul, coassoc_simple]

/-! ### Counit laws -/

theorem evPair_unit_left (u : RAlg ω ⊗[ℂ] RAlg ω) (Y : D) :
    evPair ω (𝟙_ D) Y u = ω.obj (𝟙_ D) ◁
      extMor ω (TensorProduct.lid ℂ (RAlg ω) ((counitLin ω).rTensor (RAlg ω) u)) Y := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [evPair_tmul, extMor_unit, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, extMor_smul,
      end_smul_tensor, id_tensorHom, MonoidalLinear.whiskerLeft_smul]
  | add u v hu hv => rw [map_add, hu, hv, map_add, map_add, extMor_add, MonoidalPreadditive.whiskerLeft_add]

theorem evPair_unit_right (u : RAlg ω ⊗[ℂ] RAlg ω) (X : D) :
    evPair ω X (𝟙_ D) u =
      extMor ω (TensorProduct.rid ℂ (RAlg ω) ((counitLin ω).lTensor (RAlg ω) u)) X ▷ ω.obj (𝟙_ D) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [evPair_tmul, extMor_unit, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, extMor_smul,
      end_tensor_smul, tensorHom_id, MonoidalLinear.smul_whiskerRight]
  | add u v hu hv => rw [map_add, hu, hv, map_add, map_add, extMor_add, MonoidalPreadditive.add_whiskerRight]

theorem comul_rTensor_counit :
    (counitLin ω).rTensor (RAlg ω) ∘ₗ comulLin ω = TensorProduct.mk ℂ ℂ (RAlg ω) 1 := by
  apply LinearMap.ext
  intro a
  apply (TensorProduct.lid ℂ (RAlg ω)).injective
  rw [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lid_tmul, one_smul]
  set a' := TensorProduct.lid ℂ (RAlg ω) ((counitLin ω).rTensor (RAlg ω) (comulLin ω a))
  apply eq_of_extMor_simple
  intro i
  have h : ω.obj (𝟙_ D) ◁ extMor ω a' (F.simple i) =
      μ ω (𝟙_ D) (F.simple i) ≫ extMor ω a (𝟙_ D ⊗ F.simple i) ≫ δ ω (𝟙_ D) (F.simple i) := by
    rw [← evPair_unit_left, evPair_comul]; rfl
  have hn : extMor ω a (F.simple i) = ω.map (λ_ (F.simple i)).inv ≫
      extMor ω a (𝟙_ D ⊗ F.simple i) ≫ ω.map (λ_ (F.simple i)).hom := by
    rw [extMor_natural, ← ω.map_comp_assoc, Iso.inv_hom_id, ω.map_id, Category.id_comp]
  rw [hn, Functor.Monoidal.map_leftUnitor_inv, Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc]
  rw [reassoc_of% (show μ ω (𝟙_ D) (F.simple i) ≫ extMor ω a (𝟙_ D ⊗ F.simple i) ≫
      δ ω (𝟙_ D) (F.simple i) = ω.obj (𝟙_ D) ◁ extMor ω a' (F.simple i) from h.symm)]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, Functor.Monoidal.ε_η, id_whiskerRight,
    Category.id_comp, id_whiskerLeft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem comul_lTensor_counit :
    (counitLin ω).lTensor (RAlg ω) ∘ₗ comulLin ω = (TensorProduct.mk ℂ (RAlg ω) ℂ).flip 1 := by
  apply LinearMap.ext
  intro a
  apply (TensorProduct.rid ℂ (RAlg ω)).injective
  rw [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.rid_tmul,
    one_smul]
  set a' := TensorProduct.rid ℂ (RAlg ω) ((counitLin ω).lTensor (RAlg ω) (comulLin ω a))
  apply eq_of_extMor_simple
  intro i
  have h : extMor ω a' (F.simple i) ▷ ω.obj (𝟙_ D) =
      μ ω (F.simple i) (𝟙_ D) ≫ extMor ω a (F.simple i ⊗ 𝟙_ D) ≫ δ ω (F.simple i) (𝟙_ D) := by
    rw [← evPair_unit_right, evPair_comul]; rfl
  have hn : extMor ω a (F.simple i) = ω.map (ρ_ (F.simple i)).inv ≫
      extMor ω a (F.simple i ⊗ 𝟙_ D) ≫ ω.map (ρ_ (F.simple i)).hom := by
    rw [extMor_natural, ← ω.map_comp_assoc, Iso.inv_hom_id, ω.map_id, Category.id_comp]
  rw [hn, Functor.Monoidal.map_rightUnitor_inv, Functor.Monoidal.map_rightUnitor]
  simp only [Category.assoc]
  rw [reassoc_of% (show μ ω (F.simple i) (𝟙_ D) ≫ extMor ω a (F.simple i ⊗ 𝟙_ D) ≫
      δ ω (F.simple i) (𝟙_ D) = extMor ω a' (F.simple i) ▷ ω.obj (𝟙_ D) from h.symm)]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, Functor.Monoidal.ε_η, whiskerLeft_id,
    Category.id_comp, whiskerRight_id]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

instance coalgebraStruct : CoalgebraStruct ℂ (RAlg ω) where
  comul := comulLin ω
  counit := counitLin ω

/-- `End(ω)` is a coalgebra. -/
instance coalgebra : Coalgebra ℂ (RAlg ω) where
  coassoc := comul_coassoc ω
  rTensor_counit_comp_comul := comul_rTensor_counit ω
  lTensor_counit_comp_comul := comul_lTensor_counit ω

@[simp] theorem comul_eq : (CoalgebraStruct.comul (R := ℂ) (A := RAlg ω)) = comulLin ω := rfl
@[simp] theorem counit_eq : (CoalgebraStruct.counit (R := ℂ) (A := RAlg ω)) = counitLin ω := rfl

/-! ### Bialgebra -/

theorem evS_mul (u v : RAlg ω ⊗[ℂ] RAlg ω) (p : F.ι × F.ι) :
    evS ω (u * v) p = evS ω v p ≫ evS ω u p := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, evS_tmul, evS_tmul, evS_tmul, RAlg.mul_apply,
        RAlg.mul_apply, tensorHom_comp_tensorHom]
    | add v w hv hw => rw [mul_add, map_add, Pi.add_apply, hv, hw, map_add, Pi.add_apply,
        Preadditive.add_comp]
  | add u w hu hw => rw [add_mul, map_add, Pi.add_apply, hu, hw, map_add, Pi.add_apply,
      Preadditive.comp_add]

theorem counit_one' : counitLin ω 1 = 1 := counitLin_eq ω (by rw [extMor_one, one_smul])

theorem counit_mul' (a b : RAlg ω) : counitLin ω (a * b) = counitLin ω a * counitLin ω b := by
  apply counitLin_eq
  rw [extMor_mul, extMor_unit, extMor_unit, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul, mul_comm]

theorem comul_one' : comulLin ω 1 = 1 := by
  apply (evS ω).injective
  funext p
  rw [evS_comul, Algebra.TensorProduct.one_def, evS_tmul]
  simp only [RAlg.one_apply, conjTensor, extMor_one, Category.id_comp, Functor.Monoidal.μ_δ,
    id_tensorHom_id]

theorem comul_mul' (a b : RAlg ω) : comulLin ω (a * b) = comulLin ω a * comulLin ω b := by
  apply (evS ω).injective
  funext p
  rw [evS_mul, evS_comul, evS_comul, evS_comul]
  simp only [conjTensor, extMor_mul, Category.assoc, Functor.Monoidal.δ_μ_assoc]

/-- `End(ω)` is a bialgebra. -/
instance bialgebra : Bialgebra ℂ (RAlg ω) :=
  Bialgebra.mk' ℂ (RAlg ω) (counit_one' ω) (fun {a b} => counit_mul' ω a b) (comul_one' ω)
    (fun {a b} => comul_mul' ω a b)

/-! ### Cocommutativity -/

section Symmetric

theorem evS_comm (u : RAlg ω ⊗[ℂ] RAlg ω) (i j : F.ι) :
    evS ω (TensorProduct.comm ℂ _ _ u) (i, j) =
      (β_ _ _).hom ≫ evS ω u (j, i) ≫ (β_ _ _).hom := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.comm_tmul, evS_tmul, evS_tmul]
    dsimp only
    rw [← BraidedCategory.braiding_naturality_assoc, SymmetricCategory.symmetry, Category.comp_id]
  | add u v hu hv =>
    rw [map_add, map_add, Pi.add_apply, hu, hv, map_add, Pi.add_apply, Preadditive.add_comp,
      Preadditive.comp_add]

theorem conjTensor_braid (a : RAlg ω) (X Y : D) :
    (β_ _ _).hom ≫ conjTensor ω a Y X ≫ (β_ _ _).hom = conjTensor ω a X Y := by
  unfold conjTensor
  have h1 : (β_ (ω.obj X) (ω.obj Y)).hom ≫ μ ω Y X = μ ω X Y ≫ ω.map (β_ X Y).hom :=
    (Functor.LaxBraided.braided X Y).symm
  have h2 : δ ω Y X ≫ (β_ (ω.obj Y) (ω.obj X)).hom = ω.map (β_ Y X).hom ≫ δ ω X Y := by
    calc δ ω Y X ≫ (β_ (ω.obj Y) (ω.obj X)).hom
        = δ ω Y X ≫ (β_ (ω.obj Y) (ω.obj X)).hom ≫ μ ω X Y ≫ δ ω X Y := by
          rw [Functor.Monoidal.μ_δ, Category.comp_id]
      _ = δ ω Y X ≫ μ ω Y X ≫ ω.map (β_ Y X).hom ≫ δ ω X Y := by
          rw [reassoc_of% (Functor.LaxBraided.braided (F := ω) Y X)]
      _ = ω.map (β_ Y X).hom ≫ δ ω X Y := by rw [Functor.Monoidal.δ_μ_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2, extMor_natural_assoc, ← ω.map_comp_assoc, SymmetricCategory.symmetry,
    ω.map_id, Category.id_comp]

/-- `End(ω)` is cocommutative (the braiding is symmetric). -/
instance isCocomm : Coalgebra.IsCocomm ℂ (RAlg ω) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro a
    apply (evS ω).injective
    funext ⟨i, j⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, evS_comm, comul_eq, evS_comul, evS_comul,
      conjTensor_braid]

end Symmetric

end VOA.Huang.TensorCat.Reconstruction

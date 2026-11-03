/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneReduction

/-!
# Tannaka reconstruction — fiber functors preserve duality and are additive

For a braided, `ℂ`-linear monoidal functor `ω : D ⥤ FGModuleCat ℂ` out of a symmetric fusion
category:

* `exactPairingMap` — a monoidal functor carries an exact pairing `(X, Y)` to an exact pairing
  `(F X, F Y)` (coevaluation `ε ≫ F η ≫ δ`, evaluation `μ ≫ F ε ≫ η`); not in Mathlib;
* `finrank_obj_eq_symDim` — `dim ω(X) = symDim X`;
* `additive_of_braided` — `ω` is **additive**.  Mathlib's `Functor.Linear` only asks
  `F.map (r • f) = r • F.map f`; additivity is *derived*: `dim ω(Y ⊞ Z) = dim ω Y + dim ω Z` (by
  the previous item and additivity of `symDim`), so the orthogonal idempotents `ω(fst ≫ inl)` and
  `ω(snd ≫ inr)`, of ranks `dim ω Y`, `dim ω Z`, sum to the identity.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

section Pairing

variable {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]

/-- A monoidal functor carries exact pairings to exact pairings. -/
@[reducible] def exactPairingMap (F : C ⥤ E) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    have h := congrArg F.map (ExactPairing.coevaluation_evaluation X Y)
    have h2 := (F.obj Y ◁ ε F ≫ μ F Y (𝟙_ C)) ≫= h =≫ (δ F (𝟙_ C) Y ≫ η F ▷ F.obj Y)
    simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_rightUnitor, Functor.Monoidal.map_leftUnitor_inv,
      Category.assoc, Functor.Monoidal.μ_δ_assoc, Category.comp_id, Functor.Monoidal.whiskerLeft_ε_η_assoc,
      Functor.Monoidal.whiskerRight_ε_η] at h2
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← h2]
  evaluation_coevaluation' := by
    have h := congrArg F.map (ExactPairing.evaluation_coevaluation X Y)
    have h2 := (ε F ▷ F.obj X ≫ μ F (𝟙_ C) X) ≫= h =≫ (δ F X (𝟙_ C) ≫ F.obj X ◁ η F)
    simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator, Functor.Monoidal.map_rightUnitor_inv, Functor.Monoidal.map_leftUnitor,
      Category.assoc, Functor.Monoidal.μ_δ_assoc, Category.comp_id,
      Functor.Monoidal.whiskerRight_ε_η_assoc, Functor.Monoidal.whiskerLeft_ε_η] at h2
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← h2]

end Pairing

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- `symDim` is additive on binary biproducts. -/
theorem symDim_biprod (Y Z : D) : symDim (Y ⊞ Z) = symDim Y + symDim Z := by
  apply symDim_eq_of_trMor
  rw [← biprod.total, trMor_add, trMor_comp_comm, trMor_comp_comm biprod.snd, biprod.inl_fst,
    biprod.inr_snd, trMor_id_eq_smul, trMor_id_eq_smul, add_smul]

/-- The identity of `ω 𝟙` is nonzero. -/
theorem id_obj_unit_ne_zero (ω : D ⥤ FGModuleCat ℂ) [ω.Monoidal] : 𝟙 (ω.obj (𝟙_ D)) ≠ 0 := by
  intro h
  apply id_unit_ne_zero_fgModuleCat
  rw [← Functor.Monoidal.ε_η (F := ω), ← Category.id_comp (η ω), h, zero_comp, comp_zero]

/-- **`dim ω(X) = symDim X`** for a braided `ℂ`-linear `ω`. -/
theorem finrank_obj_eq_symDim (ω : D ⥤ FGModuleCat ℂ) [ω.Braided] [ω.Linear ℂ] (X : D) :
    (finrank ℂ (ω.obj X) : ℂ) = symDim X := by
  letI pE : ExactPairing (ω.obj X) (ω.obj Xᘁ) := exactPairingMap ω X Xᘁ
  have hE : η_ (ω.obj X) (ω.obj Xᘁ) ≫ (β_ (ω.obj X) (ω.obj Xᘁ)).hom ≫ ε_ (ω.obj X) (ω.obj Xᘁ) =
      (finrank ℂ (ω.obj X) : ℂ) • 𝟙 _ := by
    rw [coev_braid_ev_indep pE (inferInstance : ExactPairing (ω.obj X) (ω.obj X)ᘁ),
      coev_braid_ev_fgModuleCat]
  have hD : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = symDim X • 𝟙 (𝟙_ D) :=
    (toScalar_smul_id FusionCategory.finrank_end_unit _).symm
  have hmap := congrArg ω.map hD
  rw [Functor.Linear.map_smul, ω.map_id] at hmap
  have hbr : ω.map (β_ X Xᘁ).hom = δ ω X Xᘁ ≫ (β_ (ω.obj X) (ω.obj Xᘁ)).hom ≫ μ ω Xᘁ X := by
    rw [← Functor.LaxBraided.braided, Functor.Monoidal.δ_μ_assoc]
  have key : ω.map (η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ) =
      η ω ≫ (η_ (ω.obj X) (ω.obj Xᘁ) ≫ (β_ (ω.obj X) (ω.obj Xᘁ)).hom ≫
        ε_ (ω.obj X) (ω.obj Xᘁ)) ≫ ε ω := by
    change _ = η ω ≫ ((ε ω ≫ ω.map (η_ X Xᘁ) ≫ δ ω X Xᘁ) ≫ (β_ (ω.obj X) (ω.obj Xᘁ)).hom ≫
        (μ ω Xᘁ X ≫ ω.map (ε_ X Xᘁ) ≫ η ω)) ≫ ε ω
    rw [Functor.map_comp, Functor.map_comp, hbr]
    simp only [Category.assoc, Functor.Monoidal.η_ε_assoc, Functor.Monoidal.η_ε, Category.comp_id]
  rw [key, hE, Linear.smul_comp, Category.id_comp, Linear.comp_smul, Functor.Monoidal.η_ε] at hmap
  exact smul_left_injective ℂ (id_obj_unit_ne_zero ω) hmap

section Additive

variable (ω : D ⥤ FGModuleCat ℂ) [ω.Linear ℂ]

theorem map_zero' {X Y : D} : ω.map (0 : X ⟶ Y) = 0 := by
  rw [← zero_smul ℂ (0 : X ⟶ Y), Functor.Linear.map_smul, zero_smul]

/-- Two orthogonal idempotents of complementary ranks sum to the identity. -/
theorem linear_idem_sum {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (P Q : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P) (hQ : Q ∘ₗ Q = Q) (hPQ : P ∘ₗ Q = 0) (hQP : Q ∘ₗ P = 0)
    (hrk : finrank ℂ (LinearMap.range P) + finrank ℂ (LinearMap.range Q) = finrank ℂ V) :
    P + Q = LinearMap.id := by
  have hinf : LinearMap.range P ⊓ LinearMap.range Q = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h1 : P (P a) = P a := LinearMap.congr_fun hP a
    rw [← hb] at h1 ⊢
    have h2 : P (Q b) = 0 := LinearMap.congr_fun hPQ b
    rw [h2] at h1
    exact h1.symm
  have hsup : LinearMap.range P ⊔ LinearMap.range Q = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P) (LinearMap.range Q)
    rw [hinf, finrank_bot, add_zero] at this
    rw [this, hrk]
  ext v
  have hv : v ∈ LinearMap.range P ⊔ LinearMap.range Q := hsup ▸ Submodule.mem_top
  obtain ⟨y, ⟨a, rfl⟩, z, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 : P (P a) = P a := LinearMap.congr_fun hP a
  have e2 : Q (Q b) = Q b := LinearMap.congr_fun hQ b
  have e3 : P (Q b) = 0 := LinearMap.congr_fun hPQ b
  have e4 : Q (P a) = 0 := LinearMap.congr_fun hQP a
  simp only [LinearMap.add_apply, map_add, e1, e2, e3, e4, LinearMap.id_apply]
  abel

/-- The rank of a retract. -/
theorem finrank_range_retract {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (r : V →ₗ[ℂ] W) (s : W →ₗ[ℂ] V)
    (h : r ∘ₗ s = LinearMap.id) : finrank ℂ (LinearMap.range (s ∘ₗ r)) = finrank ℂ W := by
  have hr : Function.Surjective r := fun w => ⟨s w, LinearMap.congr_fun h w⟩
  have hs : Function.Injective s := fun a b hab => by
    have := congrArg r hab
    simpa [← LinearMap.comp_apply, h] using this
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hr, Submodule.map_top,
    LinearMap.finrank_range_of_inj hs]

variable [ω.Braided]

/-- The biproduct idempotents of `ω (Y ⊞ Z)` sum to the identity. -/
theorem map_biprod_total (Y Z : D) :
    ω.map (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ _) + ω.map (biprod.snd ≫ biprod.inr) = 𝟙 _ := by
  have key := linear_idem_sum (ω.map (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ _)).hom.hom
    (ω.map (biprod.snd ≫ biprod.inr : Y ⊞ Z ⟶ _)).hom.hom
    (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp)
    (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp)
    (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp [map_zero' ω])
    (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp [map_zero' ω])
    (by
      rw [ω.map_comp, FGModuleCat.hom_hom_comp, ω.map_comp, FGModuleCat.hom_hom_comp,
        finrank_range_retract _ _ (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp),
        finrank_range_retract _ _ (by rw [← FGModuleCat.hom_hom_comp, ← ω.map_comp]; simp)]
      exact_mod_cast (show ((finrank ℂ (ω.obj Y) + finrank ℂ (ω.obj Z) : ℕ) : ℂ) =
          finrank ℂ (ω.obj (Y ⊞ Z)) by
        push_cast
        rw [finrank_obj_eq_symDim, finrank_obj_eq_symDim, finrank_obj_eq_symDim, symDim_biprod]))
  ext1
  exact key

/-- **A braided `ℂ`-linear functor `D ⥤ FGModuleCat ℂ` is additive.** -/
theorem additive_of_braided : ω.Additive where
  map_add {X W f g} := by
    have h : f + g = biprod.lift f g ≫ biprod.desc (𝟙 W) (𝟙 W) := by simp
    have htot := map_biprod_total ω W W
    rw [h, ω.map_comp, ← Category.id_comp (ω.map (biprod.desc _ _)), ← Category.assoc,
      ← htot]
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, ← ω.map_comp]
    simp

end Additive

end VOA.Huang.TensorCat.Reconstruction

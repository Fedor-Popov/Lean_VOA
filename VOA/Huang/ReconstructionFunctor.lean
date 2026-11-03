/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ReconstructionGroup
import VOA.Huang.DeligneIntegral

/-!
# Tannaka reconstruction — essential surjectivity and the theorem

* `exists_retraction` — Maschke for `FDRep ℂ G` (`G` finite): an injective morphism of
  representations has an equivariant left inverse (average a linear one over `G`);
* `regObj` (`⨁_i X_i`) with `extMor_regObj_injective` (`End(ω)` acts faithfully on `ω(⨁ X_i)`);
* `exists_injective_to_fiber` — every `W : FDRep ℂ G` embeds equivariantly into
  `ω(⨁_{K} ⨁_i X_i)`: the maps `w ↦ ext(c_φ(w)) (b_j)`, `c_φ(w) = Σ_g φ(g⁻¹w) g`, are equivariant
  and jointly injective (linear independence of group-likes);
* `fiberRep_essSurj` — the reconstruction functor is essentially surjective (lift the
  equivariant idempotent `r ≫ ι` by fullness, split it in `D`);
* `fiberFunctorReconstruction : FiberFunctorReconstruction` — **Tannaka reconstruction**
  (Deligne–Milne Thm 2.11 / EGNO §5, finite semisimple symmetric case), at all universe levels.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open CategoryTheory MonoidalCategory Limits Module TensorProduct

universe v u

section Maschke

variable {G : Type} [Group G]

theorem rho_comp (N : FDRep ℂ G) (a b : G) : Action.ρ N a ≫ Action.ρ N b = Action.ρ N (b * a) := by
  rw [map_mul, End.mul_def]

/-- **Maschke** for `FDRep ℂ G`: an injective morphism has an equivariant retraction. -/
theorem exists_retraction [Finite G] {M N : FDRep ℂ G} (ι : M ⟶ N)
    (hι : Function.Injective ι.hom.hom.hom) : ∃ r : N ⟶ M, ι ≫ r = 𝟙 M := by
  haveI := Fintype.ofFinite G
  obtain ⟨r0l, hr0l⟩ :=
    LinearMap.exists_leftInverse_of_injective ι.hom.hom.hom (LinearMap.ker_eq_bot.mpr hι)
  let r0 : N.V ⟶ M.V := (homLin (V := N.V) (W := M.V)).symm r0l
  have h0 : ι.hom ≫ r0 = 𝟙 _ := by
    apply FGModuleCat.hom_ext
    exact hr0l
  let rr : N.V ⟶ M.V := (Fintype.card G : ℂ)⁻¹ • ∑ u : G, Action.ρ N u⁻¹ ≫ r0 ≫ Action.ρ M u
  refine ⟨⟨rr, fun g => ?_⟩, ?_⟩
  · simp only [rr, Linear.comp_smul, Linear.smul_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← Category.assoc, rho_comp, rho_comp, ← rho_comp M v g]
    congr 2
    group
  · apply Action.Hom.ext
    change ι.hom ≫ rr = 𝟙 _
    simp only [rr, Linear.comp_smul, Preadditive.comp_sum]
    have : ∀ u : G, ι.hom ≫ Action.ρ N u⁻¹ ≫ r0 ≫ Action.ρ M u = 𝟙 _ := fun u => by
      rw [← Category.assoc, ← ι.comm, Category.assoc, reassoc_of% h0, rho_comp, mul_inv_cancel,
        map_one]
      rfl
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero), one_smul]

end Maschke

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

variable (ω : D ⥤ FGModuleCat ℂ) [ω.Braided] [ω.Additive] [ω.Linear ℂ]

/-- The regular object `⨁_i X_i`. -/
def regObj : D := ⨁ fun i : F.ι => F.simple i

theorem extMor_regObj_injective {a : RAlg ω} (h : extMor ω a (regObj (D := D)) = 0) : a = 0 := by
  apply RAlg.ext ω
  intro i
  have hn := extMor_natural ω a (biproduct.ι (fun i : F.ι => F.simple i) i)
  rw [extMor_simple] at hn
  change _ = ω.map _ ≫ extMor ω a regObj at hn
  rw [h, comp_zero] at hn
  have : a i = a i ≫ ω.map (biproduct.ι (fun i : F.ι => F.simple i) i) ≫
      ω.map (biproduct.π (fun i : F.ι => F.simple i) i) := by
    rw [← ω.map_comp, biproduct.ι_π_self, ω.map_id, Category.comp_id]
  rw [this, reassoc_of% hn]
  exact Limits.zero_comp

instance : Fintype (AutG ω) := Fintype.ofFinite _

theorem linearIndependent_AutG : LinearIndependent ℂ (AutG.val ω) := by
  have hli := linearIndepOn_isGroupLikeElem (R := ℂ) (A := RAlg ω)
  have := LinearIndependent.comp hli (fun u : AutG ω => (⟨AutG.val ω u, AutG.isGroupLike ω u⟩ :
    {a : RAlg ω | IsGroupLikeElem ℂ a})) fun u v h => AutG.val_injective ω (congrArg Subtype.val h)
  exact this

/-- `c_φ(w) = Σ_g φ(g⁻¹ w) g`. -/
def coeffMap (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V) : W.V →ₗ[ℂ] RAlg ω :=
  ∑ u : AutG ω, LinearMap.smulRight (φ ∘ₗ W.ρ u⁻¹) (AutG.val ω u)

theorem coeffMap_apply (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V) (w : W.V) :
    coeffMap ω W φ w = ∑ u : AutG ω, φ (W.ρ u⁻¹ w) • AutG.val ω u := by
  simp [coeffMap]

theorem rho_apply_mul (W : FDRep ℂ (AutG ω)) (a b : AutG ω) (w : W.V) :
    W.ρ (a * b) w = W.ρ a (W.ρ b w) := by
  rw [map_mul, Module.End.mul_apply]

theorem coeffMap_equivariant (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V) (g : AutG ω) (w : W.V) :
    coeffMap ω W φ (W.ρ g w) = AutG.val ω g * coeffMap ω W φ w := by
  rw [coeffMap_apply, coeffMap_apply, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Equiv.coe_mulLeft, AutG.val_mul, mul_smul_comm]
  congr 2
  rw [← rho_apply_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- The component maps `W → ω(⨁ X_i)`. -/
def compMap (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V) (b : ω.obj (regObj (D := D))) :
    W.V →ₗ[ℂ] ω.obj (regObj (D := D)) :=
  LinearMap.applyₗ b ∘ₗ (homLin (V := ω.obj regObj) (W := ω.obj regObj)).toLinearMap ∘ₗ
    extLin ω regObj ∘ₗ coeffMap ω W φ

theorem compMap_apply (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V) (b : ω.obj (regObj (D := D)))
    (w : W.V) : compMap ω W φ b w = (extMor ω (coeffMap ω W φ w) regObj).hom.hom b := rfl

theorem compMap_equivariant (W : FDRep ℂ (AutG ω)) (φ : Module.Dual ℂ W.V)
    (b : ω.obj (regObj (D := D))) (g : AutG ω) (w : W.V) :
    compMap ω W φ b (W.ρ g w) = (extMor ω (AutG.val ω g) regObj).hom.hom (compMap ω W φ b w) := by
  rw [compMap_apply, compMap_apply, coeffMap_equivariant, extMor_mul]
  rfl

theorem compMap_jointly_injective (W : FDRep ℂ (AutG ω)) (w : W.V)
    (h : ∀ (φ : Module.Dual ℂ W.V) (b : ω.obj (regObj (D := D))), compMap ω W φ b w = 0) : w = 0 := by
  have hc : ∀ φ : Module.Dual ℂ W.V, coeffMap ω W φ w = 0 := fun φ => by
    apply extMor_regObj_injective ω
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact h φ b
  have hφ : ∀ φ : Module.Dual ℂ W.V, φ w = 0 := fun φ => by
    have h1 := hc φ
    rw [coeffMap_apply] at h1
    have := Fintype.linearIndependent_iff.mp (linearIndependent_AutG ω) _ h1 1
    simpa using this
  exact (Module.forall_dual_apply_eq_zero_iff ℂ w).mp hφ

theorem compMap_basis_injective (W : FDRep ℂ (AutG ω)) (w : W.V)
    (h : ∀ (p : Fin (finrank ℂ W.V)) (j : Fin (finrank ℂ (ω.obj (regObj (D := D))))),
      compMap ω W ((Module.finBasis ℂ W.V).coord p) (Module.finBasis ℂ (ω.obj regObj) j) w = 0) :
    w = 0 := by
  have hc : ∀ p, coeffMap ω W ((Module.finBasis ℂ W.V).coord p) w = 0 := fun p => by
    apply extMor_regObj_injective ω
    apply FGModuleCat.hom_ext
    exact (Module.finBasis ℂ (ω.obj regObj)).ext fun j => h p j
  have hφ : ∀ p, (Module.finBasis ℂ W.V).coord p w = 0 := fun p => by
    have h1 := hc p
    rw [coeffMap_apply] at h1
    have := Fintype.linearIndependent_iff.mp (linearIndependent_AutG ω) _ h1 1
    simpa using this
  exact (Module.finBasis ℂ W.V).forall_coord_eq_zero_iff.mp hφ

/-- The index set of the embedding. -/
abbrev EmbIdx (W : FDRep ℂ (AutG ω)) := Fin (finrank ℂ W.V) × Fin (finrank ℂ (ω.obj (regObj (D := D))))

/-- The target object `⨁_K ⨁_i X_i`. -/
def embObj (W : FDRep ℂ (AutG ω)) : D := ⨁ fun _ : EmbIdx ω W => (regObj (D := D))

/-- The `k`-th component map. -/
def embComp (W : FDRep ℂ (AutG ω)) (k : EmbIdx ω W) : W.V ⟶ ω.obj (regObj (D := D)) :=
  (homLin (V := W.V) (W := ω.obj regObj)).symm
    (compMap ω W ((Module.finBasis ℂ W.V).coord k.1) (Module.finBasis ℂ (ω.obj regObj) k.2))

theorem embComp_comm (W : FDRep ℂ (AutG ω)) (k : EmbIdx ω W) (g : AutG ω) :
    Action.ρ W g ≫ embComp ω W k = embComp ω W k ≫ extMor ω (AutG.val ω g) regObj := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rw [FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact compMap_equivariant ω W _ _ g w

/-- The equivariant embedding `W ⟶ ω(⨁_K ⨁_i X_i)`. -/
def embMor (W : FDRep ℂ (AutG ω)) : W.V ⟶ ω.obj (embObj ω W) :=
  ∑ k, embComp ω W k ≫ ω.map (biproduct.ι (fun _ : EmbIdx ω W => (regObj (D := D))) k)

theorem embMor_comm (W : FDRep ℂ (AutG ω)) (g : AutG ω) :
    Action.ρ W g ≫ embMor ω W = embMor ω W ≫ extMor ω (AutG.val ω g) (embObj ω W) := by
  simp only [embMor, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [reassoc_of% (embComp_comm ω W k g), Category.assoc, extMor_natural]

/-- The embedding as a morphism of representations. -/
def embHom (W : FDRep ℂ (AutG ω)) : W ⟶ (fiberRep ω).obj (embObj ω W) :=
  ⟨embMor ω W, embMor_comm ω W⟩

theorem embMor_comp_π (W : FDRep ℂ (AutG ω)) (k : EmbIdx ω W) :
    embMor ω W ≫ ω.map (biproduct.π (fun _ : EmbIdx ω W => (regObj (D := D))) k) = embComp ω W k := by
  simp only [embMor, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single k]
  · erw [← ω.map_comp, biproduct.ι_π, dif_pos rfl, eqToHom_refl, ω.map_id, Category.comp_id]
  · intro l _ hl
    erw [← ω.map_comp, biproduct.ι_π, dif_neg hl, Functor.map_zero, comp_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem embHom_injective (W : FDRep ℂ (AutG ω)) : Function.Injective (embHom ω W).hom.hom.hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  apply compMap_basis_injective ω W w
  intro p j
  have h1 := congrArg (fun m : W.V ⟶ ω.obj regObj => m.hom.hom w)
    (embMor_comp_π ω W (p, j))
  simp only at h1
  change (embComp ω W (p, j)).hom.hom w = 0
  rw [← h1, FGModuleCat.hom_hom_comp, LinearMap.comp_apply]
  have hw' : (embMor ω W).hom.hom w = 0 := hw
  rw [hw', map_zero]

/-- The reconstruction functor is **essentially surjective**. -/
theorem fiberRep_essImage [ω.Faithful] (W : FDRep ℂ (AutG ω)) : (fiberRep ω).essImage W := by
  obtain ⟨r, hr⟩ := exists_retraction (embHom ω W) (embHom_injective ω W)
  set ι := embHom ω W
  set e := r ≫ ι with he
  obtain ⟨f, hf⟩ := (fiberRep ω).map_surjective e
  have hee : e ≫ e = e := by rw [he, Category.assoc, reassoc_of% hr]
  have hff : f ≫ f = f := (fiberRep ω).map_injective (by rw [Functor.map_comp, hf, hee])
  obtain ⟨Y, i, p, hip, hpi⟩ := IsIdempotentComplete.idempotents_split _ f hff
  refine ⟨Y, ⟨Iso.mk ((fiberRep ω).map i ≫ r) (ι ≫ (fiberRep ω).map p) ?_ ?_⟩⟩
  · have : (fiberRep ω).map i ≫ e ≫ (fiberRep ω).map p = 𝟙 _ := by
      rw [← hf, ← Functor.map_comp, ← Functor.map_comp, ← hpi]
      simp only [Category.assoc]
      rw [reassoc_of% hip, hip, CategoryTheory.Functor.map_id]
    rw [← this, he]
    simp only [Category.assoc]
  · have : ι ≫ (fiberRep ω).map p ≫ (fiberRep ω).map i ≫ r = ι ≫ e ≫ r := by
      rw [← Functor.map_comp_assoc, hpi, hf]
    rw [Category.assoc, this, he]
    simp only [Category.assoc]
    rw [reassoc_of% hr, hr]

instance [ω.Faithful] : (fiberRep ω).EssSurj := ⟨fiberRep_essImage ω⟩

/-- The reconstruction functor is an **equivalence**. -/
instance fiberRep_isEquivalence [ω.Faithful] : (fiberRep ω).IsEquivalence where

end VOA.Huang.TensorCat.Reconstruction

namespace VOA.Huang.TensorCat

open CategoryTheory Reconstruction

/-- **Tannaka reconstruction** (finite semisimple symmetric case; Saavedra Rivano,
Deligne–Milne Thm 2.11, EGNO §5.2–5.4): a symmetric fusion category over `ℂ` with a braided,
`ℂ`-linear, faithful functor to `FGModuleCat ℂ` is braided-equivalent, by a `ℂ`-linear functor, to
`FDRep ℂ G` for the finite group `G = Aut⊗(ω)`. -/
theorem fiberFunctorReconstruction : FiberFunctorReconstruction.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ _ ω ⟨hbr⟩ hlin hfaith
  letI := hbr
  haveI := additive_of_braided ω
  exact ⟨AutG ω, inferInstance, inferInstance, fiberRep ω, ⟨inferInstance⟩, inferInstance,
    inferInstance⟩

end VOA.Huang.TensorCat

namespace VOA.Huang.TensorCat

/-- With reconstruction proved, **Deligne's theorem reduces to the existence of a fiber
functor**. -/
theorem deligneTannakian_of_symmetricFiberFunctorExists
    (hF : SymmetricFiberFunctorExists.{v, u}) : DeligneTannakian.{v, u} :=
  deligneTannakian_of_fiberFunctor hF fiberFunctorReconstruction

/-- `DeligneTannakian ↔ SymmetricFiberFunctorExists` (at every universe level). -/
theorem deligneTannakian_iff_symmetricFiberFunctorExists :
    DeligneTannakian.{v, u} ↔ SymmetricFiberFunctorExists.{v, u} :=
  ⟨symmetricFiberFunctorExists_of_deligneTannakian, deligneTannakian_of_symmetricFiberFunctorExists⟩

end VOA.Huang.TensorCat

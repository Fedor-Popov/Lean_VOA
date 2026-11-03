import VOA.Huang.HuangRigidOrdinary
import VOA.Huang.HuangRigidPivotal

/-!
# `θ_{X'} = (θ_X)'`: the twist commutes with duality (`RibbonDualInput`)

* Abstract: the right adjoint mate is additive and `ℂ`-linear; a natural twist that is a scalar
  `t_j` on the summands `S_j` of a split presentation of `X` and the SAME scalar on their duals
  satisfies `θ_{Xᘁ} = (θ_X)ᘁ` (`twist_dual_of_split`).
* Ordinary modules: every irreducible `T` has a right dual all of whose weights are weights of
  `T` (it is the contragredient: `(M')_α = (M_α)*`), so the twist of the dual is the same scalar
  `e^{2πih}` (`exists_dual_weights`).
* `ribbonDualInput_holds` — for every structural model and EVERY choice of right duals,
  `(modelTwist Xᘁ).hom = ((modelTwist X).hom)ᘁ`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangRigid

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe v u

section Scalar

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear ℂ 𝒞]

/-- A natural automorphism that is a scalar on `B` is the same scalar on any `A ≅ B`. -/
theorem nat_scalar_of_iso (θ : ∀ X : 𝒞, X ≅ X)
    (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
    {A B : 𝒞} (e : A ≅ B) (c : ℂ) (hB : (θ B).hom = c • 𝟙 B) : (θ A).hom = c • 𝟙 A := by
  have h := hθ e.hom
  rw [hB, Linear.comp_smul, Category.comp_id] at h
  have : (θ A).hom = (θ A).hom ≫ e.hom ≫ e.inv := by simp
  rw [this, ← Category.assoc, ← h, Linear.smul_comp, e.hom_inv_id]

end Scalar

section Mate

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear ℂ 𝒞] [MonoidalCategory 𝒞]
  [MonoidalPreadditive 𝒞] [MonoidalLinear ℂ 𝒞] [RightRigidCategory 𝒞]

theorem rightAdjointMate_add {X Y : 𝒞} (f g : X ⟶ Y) : (f + g)ᘁ = fᘁ + gᘁ := by
  simp only [rightAdjointMate, MonoidalPreadditive.add_whiskerRight,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

theorem rightAdjointMate_zero {X Y : 𝒞} : (0 : X ⟶ Y)ᘁ = 0 := by
  simp only [rightAdjointMate, MonoidalPreadditive.zero_whiskerRight,
    MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]

theorem rightAdjointMate_smul {X Y : 𝒞} (c : ℂ) (f : X ⟶ Y) : (c • f)ᘁ = c • fᘁ := by
  simp only [rightAdjointMate, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

theorem rightAdjointMate_sum {X Y : 𝒞} {J : Type*} (s : Finset J) (f : J → (X ⟶ Y)) :
    (∑ j ∈ s, f j)ᘁ = ∑ j ∈ s, (f j)ᘁ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rightAdjointMate_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, rightAdjointMate_add, ih]

/-- **Twist and duality, through a split presentation.** -/
theorem twist_dual_of_split (θ : ∀ X : 𝒞, X ≅ X)
    (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
    (X : 𝒞) {n : ℕ} (S : Fin n → 𝒞) (p : ∀ j, X ⟶ S j) (i : ∀ j, S j ⟶ X)
    (htot : ∑ j, p j ≫ i j = 𝟙 X) (t : Fin n → ℂ)
    (hS : ∀ j, (θ (S j)).hom = t j • 𝟙 (S j)) (hSd : ∀ j, (θ ((S j)ᘁ)).hom = t j • 𝟙 ((S j)ᘁ)) :
    (θ (Xᘁ)).hom = ((θ X).hom)ᘁ := by
  have hX : (θ X).hom = ∑ j, t j • (p j ≫ i j) := by
    calc (θ X).hom = (∑ j, p j ≫ i j) ≫ (θ X).hom := by rw [htot, Category.id_comp]
      _ = ∑ j, t j • (p j ≫ i j) := by
        rw [Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Category.assoc, hθ (i j), hS j, Linear.smul_comp, Category.id_comp,
          Linear.comp_smul]
  have hdual : 𝟙 (Xᘁ) = ∑ j, (i j)ᘁ ≫ (p j)ᘁ := by
    rw [← rightAdjointMate_id, ← htot, rightAdjointMate_sum]
    exact Finset.sum_congr rfl fun j _ => comp_rightAdjointMate
  calc (θ (Xᘁ)).hom = (∑ j, (i j)ᘁ ≫ (p j)ᘁ) ≫ (θ (Xᘁ)).hom := by
        rw [← hdual, Category.id_comp]
    _ = ∑ j, t j • ((i j)ᘁ ≫ (p j)ᘁ) := by
        rw [Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Category.assoc, hθ ((p j)ᘁ), hSd j, Linear.smul_comp, Category.id_comp,
          Linear.comp_smul]
    _ = ((θ X).hom)ᘁ := by
        rw [hX, rightAdjointMate_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [rightAdjointMate_smul, comp_rightAdjointMate]

end Mate

section Ordinary

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeTransport VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A nonzero weight space of the contragredient comes from a nonzero weight space. -/
theorem weight_ne_bot_of_contragredient {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {α : ℂ} (h : (contragredientModule N).weight α ≠ ⊥) :
    N.weight α ≠ ⊥ := by
  intro hN
  apply h
  change RestrictedDual.weight N α = ⊥
  rw [RestrictedDual.weight, LinearMap.range_eq_bot]
  haveI : Subsingleton (N.weight α) := by
    rw [hN]; infer_instance
  ext f
  have : f = 0 := Subsingleton.elim _ _
  simp [this]

open VOA.VHat VOA.VHat.DLM3 VOA.Huang.ZhuFiniteIrr VOA.Huang.ZhuSemisimple in
/-- The canonical Zhu family of a nice VOA: complete, irredundant, with a vacuum label. -/
theorem exists_zhuFamily (hNice : Nice W) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (_ : DecidableEq ι) (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D ∧ Irredundant D.Mfam ∧ Complete D.Mfam ∧
        ∃ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) := by
  classical
  have hSR : StronglyRational W := hNice.1
  let Pr := voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))
  have hss := isSemisimpleRing_A_of_admissiblyRational Pr hSR.rational
  haveI : Finite (Φ W) := finite_Φ_of_C2Cofinite Pr hSR.c2Cofinite hss
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  obtain ⟨D, hM, -, hZ⟩ := zhuModularity_canonical_of_Pr (W := W) Pr hSR.c2Cofinite hss
  have hic := canonicalIrrFamily_irredundant_complete (W := W)
  let c0 : Φ W := (adjointIrr W hSR.simple).toΦ
  refine ⟨Φ W, inferInstance, inferInstance, D, hZ, by rw [hM]; exact hic.1,
    by rw [hM]; exact hic.2, c0, ?_⟩
  rw [hM]; exact Quotient.exact (canonicalIrrModule_toΦ c0)

/-- **Every irreducible ordinary module has a right dual with no new weights** (the
contragredient). -/
theorem exists_dual_weights (F : FusionChoice W) (hNice : Nice W) (T : Ordinary W)
    (hT : T.isMod.IsIrreducible) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    ∃ Y : Ordinary W, Nonempty (ExactPairing T Y) ∧
      ∀ α, Y.isMod.weight α ≠ ⊥ → T.isMod.weight α ≠ ⊥ := by
  letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
  obtain ⟨ι, _, _, D, hZ, hirr, hcomp, v0, hv0⟩ := exists_zhuFamily hNice
  obtain ⟨b, ⟨g⟩⟩ := hcomp ⟨T.carrier, T.isMod, hT⟩
  obtain ⟨a, ⟨g'⟩, ⟨p⟩⟩ := exactPairing_famObj F hNice D hZ hirr hcomp v0 hv0 b
  let i : T ≅ famObj D b := Ordinary.isoOfModuleEquiv g
  refine ⟨famObj D a, ⟨exactPairingCongrLeft i⟩, fun α hα => ?_⟩
  exact g.symm.weight_ne_bot (weight_ne_bot_of_contragredient _ (g'.symm.weight_ne_bot hα))

end Ordinary

section Model

open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The model twist is a scalar on any object whose image is isomorphic to a module on which
the actual twist is that scalar. -/
theorem modelTwist_eq_smul_of_iso (M : StructuralModel W) (Z : M.C) {T : Ordinary W}
    (e : M.E.functor.obj Z ≅ T) (c : ℂ) (hT : (twistIso T).hom = c • 𝟙 T) :
    (modelTwist M.E Z).hom = c • 𝟙 Z := by
  have h1 : (twistIso (M.E.functor.obj Z)).hom = c • 𝟙 _ :=
    nat_scalar_of_iso (fun X => twistIso X) (fun f => twist_naturality f) e c hT
  apply M.E.functor.map_injective
  rw [map_modelTwist, Functor.map_smul, CategoryTheory.Functor.map_id]
  exact h1

/-- Any right dual in the model is the pull-back of any right dual of the image. -/
theorem nonempty_dual_iso (M : StructuralModel W) [RightRigidCategory M.C] (Z : M.C)
    (Y : Ordinary W) :
    letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
    ExactPairing (M.E.functor.obj Z) Y → Nonempty (Zᘁ ≅ M.E.inverse.obj Y) := by
  letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
  letI := M.monoidalFunctor
  intro pE
  letI hE : HasRightDual (M.E.functor.obj Z) := { rightDual := Y, exact := pE }
  exact ⟨rightDualIso (HasRightDual.exact (X := Z))
    (hasRightDualOfEquivalence M.E.toAdjunction Z).exact⟩

/-- **`θ_{X'} = (θ_X)'`** for every structural model of a nice VOA and EVERY choice of
right duals. -/
theorem ribbonDualInput_of_nice (hW : Nice W) (M : StructuralModel W)
    (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    [RightRigidCategory M.C] : M.RibbonDualInput := by
  intro X
  letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
  letI := M.monoidalFunctor
  obtain ⟨n, lab, ⟨e⟩⟩ := semisimple_of_modularData D hD M.stronglyRational (M.E.functor.obj X)
  let T : Fin n → Ordinary W := fun j => Ordinary.of (D.module (lab j))
  let S : Fin n → M.C := fun j => modelSimple M.E D (lab j)
  let p : ∀ j, X ⟶ S j := fun j => M.E.functor.preimage
    (e.hom ≫ biproduct.π T j ≫ (modelSimpleIso M.E D (lab j)).inv)
  let i : ∀ j, S j ⟶ X := fun j => M.E.functor.preimage
    ((modelSimpleIso M.E D (lab j)).hom ≫ biproduct.ι T j ≫ e.inv)
  have htot : ∑ j, p j ≫ i j = 𝟙 X := by
    apply M.E.functor.map_injective
    rw [Functor.map_sum, CategoryTheory.Functor.map_id]
    simp only [p, i, Functor.map_comp, Functor.map_preimage, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_sum]
    simp_rw [← Category.assoc (biproduct.π T _)]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]
  let t : Fin n → ℂ := fun j => Complex.exp (2 * Real.pi * Complex.I * (D.h (lab j) : ℂ))
  have hS : ∀ j, (modelTwist M.E (S j)).hom = t j • 𝟙 (S j) := fun j =>
    modelTwist_simple M.E D hD (lab j)
  have hSd : ∀ j, (modelTwist M.E ((S j)ᘁ)).hom = t j • 𝟙 ((S j)ᘁ) := by
    intro j
    obtain ⟨Y, ⟨pY⟩, hY⟩ := exists_dual_weights M.F hW (T j) (hD.irred (lab j))
    have hYt : (twistIso Y).hom = t j • 𝟙 Y :=
      twistIso_eq_smul_of_weights Y _ (fun α hα => hD.weight_support (lab j) α (hY α hα))
    obtain ⟨iso1⟩ := nonempty_dual_iso M (S j) Y
      (exactPairingCongrLeft (modelSimpleIso M.E D (lab j)))
    exact modelTwist_eq_smul_of_iso M ((S j)ᘁ) (M.E.functor.mapIso iso1 ≪≫ M.E.counitIso.app Y)
      (t j) hYt
  exact twist_dual_of_split (fun Z => modelTwist M.E Z) (fun f => modelTwist_naturality M.E f)
    X S p i htot t hS hSd

end Model

end VOA.Huang.HuangRigid

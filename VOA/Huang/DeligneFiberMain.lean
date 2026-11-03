/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberStep
import VOA.Huang.ReconstructionFunctor

/-!
# Deligne's fiber functor — assembly: `SymmetricFiberFunctorExists` at `v = 0`

* the base lax braided functor `homG = Hom(𝟙, -)` (the unit algebra `𝟙` of `Ind(D)`; hom-spaces
  are finite-dimensional, so they are shrunk to `Type` by `Shrink`), with `ε 1 = 𝟙 ≠ 0` and
  finite-dimensional values;
* `exists_orthonormal_family` — `n` Gram–Schmidt steps (`gram_schmidt_step`) starting from
  the empty family over `homG`;
* `frameFunctorExists_holds : FrameFunctorExists.{v, u}`, hence
  **`symmetricFiberFunctorExists_holds : SymmetricFiberFunctorExists.{v, u}`** (Deligne's
  existence theorem, fusion case, all universes), and
  **`deligneTannakian_holds : DeligneTannakian.{v, u}`** (with `fiberFunctorReconstruction`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Cardinal
open scoped TensorProduct

universe v u

section HomMul

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [SymmetricCategory D]

theorem tensorHom_smul_left'' {P Q R S : D} (c : ℂ) (f : P ⟶ Q) (g : R ⟶ S) : (c • f) ⊗ₘ g = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

theorem tensorHom_smul_right'' {P Q R S : D} (f : P ⟶ Q) (c : ℂ) (g : R ⟶ S) : f ⊗ₘ (c • g) = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

/-- The product `a · b = λ⁻¹ ≫ (a ⊗ b)` on `Hom(𝟙, -)`. -/
def homMul (Y Z : D) : (𝟙_ D ⟶ Y) →ₗ[ℂ] (𝟙_ D ⟶ Z) →ₗ[ℂ] (𝟙_ D ⟶ Y ⊗ Z) :=
  LinearMap.mk₂ ℂ (fun a b => (λ_ (𝟙_ D)).inv ≫ (a ⊗ₘ b))
    (fun a a' b => by simp [MonoidalPreadditive.add_tensor])
    (fun c a b => by
      show (λ_ (𝟙_ D)).inv ≫ ((c • a) ⊗ₘ b) = c • ((λ_ (𝟙_ D)).inv ≫ (a ⊗ₘ b))
      rw [tensorHom_smul_left'', Linear.comp_smul])
    (fun a b b' => by simp [MonoidalPreadditive.tensor_add])
    (fun c a b => by
      show (λ_ (𝟙_ D)).inv ≫ (a ⊗ₘ (c • b)) = c • ((λ_ (𝟙_ D)).inv ≫ (a ⊗ₘ b))
      rw [tensorHom_smul_right'', Linear.comp_smul])

theorem homMul_apply (Y Z : D) (a : 𝟙_ D ⟶ Y) (b : 𝟙_ D ⟶ Z) : homMul Y Z a b = (λ_ (𝟙_ D)).inv ≫ (a ⊗ₘ b) := rfl

theorem homMul_natural_left {Y Y' : D} (f : Y ⟶ Y') (Z : D) (a : 𝟙_ D ⟶ Y) (b : 𝟙_ D ⟶ Z) :
    homMul Y' Z (a ≫ f) b = homMul Y Z a b ≫ (f ▷ Z) := by
  simp only [homMul_apply, Category.assoc, tensorHom_comp_whiskerRight]

theorem homMul_natural_right (Y : D) {Z Z' : D} (f : Z ⟶ Z') (a : 𝟙_ D ⟶ Y) (b : 𝟙_ D ⟶ Z) :
    homMul Y Z' a (b ≫ f) = homMul Y Z a b ≫ (Y ◁ f) := by
  simp only [homMul_apply, Category.assoc, tensorHom_comp_whiskerLeft]

theorem homMul_assoc (X Y Z : D) (a : 𝟙_ D ⟶ X) (b : 𝟙_ D ⟶ Y) (c : 𝟙_ D ⟶ Z) :
    homMul (X ⊗ Y) Z (homMul X Y a b) c ≫ (α_ X Y Z).hom = homMul X (Y ⊗ Z) a (homMul Y Z b c) := by
  simp only [homMul_apply, tensorHom_def]
  monoidal

theorem homMul_unit_left (Y : D) (c : ℂ) (a : 𝟙_ D ⟶ Y) : c • a = homMul (𝟙_ D) Y (c • 𝟙 _) a ≫ (λ_ Y).hom := by
  rw [homMul_apply, tensorHom_smul_left'', Linear.comp_smul, Linear.smul_comp, id_tensorHom, Category.assoc,
    leftUnitor_naturality, Iso.inv_hom_id_assoc]

theorem homMul_unit_right (Y : D) (c : ℂ) (a : 𝟙_ D ⟶ Y) : c • a = homMul Y (𝟙_ D) a (c • 𝟙 _) ≫ (ρ_ Y).hom := by
  rw [homMul_apply, tensorHom_smul_right'', Linear.comp_smul, Linear.smul_comp, tensorHom_id, Category.assoc,
    rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc]

theorem homMul_braid (Y Z : D) (a : 𝟙_ D ⟶ Y) (b : 𝟙_ D ⟶ Z) : homMul Y Z a b ≫ (β_ Y Z).hom = homMul Z Y b a := by
  simp only [homMul_apply, Category.assoc, BraidedCategory.braiding_naturality, braiding_tensorUnit_left]
  simp [unitors_equal]

end HomMul

section HomG

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [SymmetricCategory D] [hs : ∀ Y : D, Small.{0} (𝟙_ D ⟶ Y)]

/-- `Hom(𝟙, Y)`, shrunk to `Type`. -/
abbrev hS (Y : D) : Type := Shrink.{0} (𝟙_ D ⟶ Y)

/-- The identification `Shrink (𝟙 ⟶ Y) ≃ₗ (𝟙 ⟶ Y)`. -/
abbrev hL (Y : D) : hS Y ≃ₗ[ℂ] (𝟙_ D ⟶ Y) := Shrink.linearEquiv ℂ (𝟙_ D ⟶ Y)

/-- The base functor `Y ↦ Hom(𝟙, Y)` (the unit algebra of `Ind(D)`), with values in `Type`. -/
def homG : D ⥤ ModuleCat.{0} ℂ where
  obj Y := ModuleCat.of ℂ (hS Y)
  map f := ModuleCat.ofHom ((hL _).symm.toLinearMap ∘ₗ Linear.rightComp ℂ (𝟙_ D) f ∘ₗ (hL _).toLinearMap)
  map_id Y := by
    ext g
    simp [Linear.rightComp]
  map_comp f g := by
    ext h
    simp [Linear.rightComp]

theorem homG_map_apply {Y Y' : D} (f : Y ⟶ Y') (g : hS Y) :
    ((homG (D := D)).map f).hom g = (hL Y').symm ((hL Y) g ≫ f) := rfl

/-- The transported product. -/
def homMulS (Y Z : D) : hS Y →ₗ[ℂ] hS Z →ₗ[ℂ] hS (Y ⊗ Z) :=
  (((homMul Y Z).compr₂ (hL (Y ⊗ Z)).symm.toLinearMap).compl₁₂ (hL Y).toLinearMap (hL Z).toLinearMap)

theorem homMulS_apply (Y Z : D) (a : hS Y) (b : hS Z) :
    homMulS Y Z a b = (hL (Y ⊗ Z)).symm (homMul Y Z (hL Y a) (hL Z b)) := rfl

instance : (homG (D := D)).LaxMonoidal where
  ε := ModuleCat.ofHom ((hL (𝟙_ D)).symm.toLinearMap ∘ₗ LinearMap.toSpanSingleton ℂ (𝟙_ D ⟶ 𝟙_ D) (𝟙 _))
  μ Y Z := ModuleCat.ofHom (TensorProduct.lift (homMulS Y Z))
  μ_natural_left f Z := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    change homMulS _ Z ((hL _).symm ((hL _) a ≫ f)) b = (hL _).symm ((hL _) (homMulS _ Z a b) ≫ (f ▷ Z))
    simp only [homMulS_apply, LinearEquiv.apply_symm_apply, homMul_natural_left]
  μ_natural_right Y f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    change homMulS Y _ a ((hL _).symm ((hL _) b ≫ f)) = (hL _).symm ((hL _) (homMulS Y _ a b) ≫ (Y ◁ f))
    simp only [homMulS_apply, LinearEquiv.apply_symm_apply, homMul_natural_right]
  associativity X Y Z := by
    apply ModuleCat.MonoidalCategory.tensor_ext₃'
    intro a b c
    change (hL _).symm ((hL _) (homMulS (X ⊗ Y) Z (homMulS X Y a b) c) ≫ (α_ X Y Z).hom) =
      homMulS X (Y ⊗ Z) a (homMulS Y Z b c)
    simp only [homMulS_apply, LinearEquiv.apply_symm_apply, homMul_assoc]
  left_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c a
    change c • a = (hL _).symm ((hL _) (homMulS (𝟙_ D) Y ((hL _).symm (c • 𝟙 _)) a) ≫ (λ_ Y).hom)
    rw [homMulS_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← homMul_unit_left, map_smul,
      LinearEquiv.symm_apply_apply]
    rfl
  right_unitality Y := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a c
    change c • a = (hL _).symm ((hL _) (homMulS Y (𝟙_ D) a ((hL _).symm (c • 𝟙 _))) ≫ (ρ_ Y).hom)
    rw [homMulS_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← homMul_unit_right, map_smul,
      LinearEquiv.symm_apply_apply]
    rfl

theorem homG_ε_apply (c : ℂ) : (ε (homG (D := D))).hom c = (hL (𝟙_ D)).symm (c • 𝟙 (𝟙_ D)) := rfl

instance : (homG (D := D)).LaxBraided where
  braided Y Z := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    change (hL _).symm ((hL _) (homMulS Y Z a b) ≫ (β_ Y Z).hom) = homMulS Z Y b a
    simp only [homMulS_apply, LinearEquiv.apply_symm_apply, homMul_braid]

instance : (homG (D := D)).Additive where
  map_add {Y Y' f g} := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro h
    simp only [ModuleCat.hom_add, LinearMap.add_apply, homG_map_apply, Preadditive.comp_add, map_add]
    rfl

instance : (homG (D := D)).Linear ℂ where
  map_smul {Y Y'} f c := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro h
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply, homG_map_apply, Linear.comp_smul, map_smul]
    rfl

end HomG

section Assembly

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

/-- Hom-spaces of a fusion category are finite-dimensional, hence `Type`-small. -/
theorem small_hom (Y Z : D) : Small.{0} (Y ⟶ Z) := by
  haveI := F.finiteDimensional Y Z
  exact Module.Finite.small ℂ (Y ⟶ Z)

variable [∀ Y : D, Small.{0} (𝟙_ D ⟶ Y)]

theorem homG_ε_ne_zero : (ε (homG (D := D))).hom 1 ≠ 0 := by
  rw [homG_ε_apply, one_smul]
  intro h0
  have h1 : 𝟙 (𝟙_ D) = 0 := by
    have := congrArg (hL (𝟙_ D)) h0
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this]
    exact map_zero (hL (𝟙_ D))
  have hsub : ∀ g : 𝟙_ D ⟶ 𝟙_ D, g = 0 := fun g => by
    rw [← Category.comp_id g, h1]
    erw [Limits.comp_zero]
  have hfr := FusionCategory.finrank_end_unit (C := D)
  haveI : Subsingleton (𝟙_ D ⟶ 𝟙_ D) := ⟨fun a b => by rw [hsub a, hsub b]⟩
  rw [Module.finrank_zero_of_subsingleton] at hfr
  exact zero_ne_one hfr

theorem homG_rank_le (Y : D) : Module.rank ℂ ((homG (D := D)).obj Y) ≤ ℵ₀ := by
  haveI := F.finiteDimensional (𝟙_ D) Y
  haveI : Module.Finite ℂ (hS Y) := Module.Finite.equiv (hL Y).symm
  exact (Module.rank_lt_aleph0 ℂ (hS Y)).le

/-- **Orthonormal families of every length `m ≤ n`** (`n` Gram–Schmidt steps from `Hom(𝟙, -)`). -/
theorem exists_orthonormal_family (X : D) {n : ℕ}
    (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ D)) : ∀ m, m ≤ n →
    ∃ (G : D ⥤ ModuleCat.{0} ℂ) (_ : G.LaxBraided) (_ : G.Additive) (_ : G.Linear ℂ)
      (e : Fin m → G.obj X) (f : Fin m → G.obj Xᘁ),
      (ε G).hom 1 ≠ 0 ∧ (∀ Y, Module.rank ℂ (G.obj Y) ≤ ℵ₀) ∧
      ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0
  | 0, _ => ⟨homG, inferInstance, inferInstance, inferInstance, Fin.elim0, Fin.elim0,
      homG_ε_ne_zero, homG_rank_le, fun i => i.elim0⟩
  | m + 1, hm => by
    haveI : HasBinaryBiproducts D := hasBinaryBiproducts_of_finite_biproducts D
    obtain ⟨G, h1, h2, h3, e, f, hne, hrank, horth⟩ := exists_orthonormal_family X htr m (by omega)
    letI := h1
    haveI := h2
    haveI := h3
    exact gram_schmidt_step G X htr (by omega) hne hrank e f horth

end Assembly

/-- **Frame functors exist**. -/
theorem frameFunctorExists_holds : FrameFunctorExists.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ F hpos
  haveI : ∀ Y : D, Small.{0} (𝟙_ D ⟶ Y) := fun Y => small_hom (𝟙_ D) Y
  let X : D := ⨁ (fun i => F.simple i)
  obtain ⟨n, hn⟩ := symDim_eq_nat hpos X
  have htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ D) := by
    rw [← trMor_id, trMor_id_eq_smul, hn]
  obtain ⟨G, h1, h2, h3, e, f, hne, hrank, horth⟩ := exists_orthonormal_family X htr n le_rfl
  letI := h1
  haveI := h2
  haveI := h3
  refine ⟨G, h1, h2, h3, X, n, e, fun i => ⟨biproduct.ι _ i, biproduct.π _ i, biproduct.ι_π_self _ i⟩,
    hne, hrank _, frameMap_bijective_of_orthonormal G e f (antisym_eq_zero_of_symDim hpos X hn) horth⟩

/-- **Deligne's existence theorem** (fusion case): every symmetric fusion category over `ℂ`
with positive dimensions has a symmetric (braided), `ℂ`-linear, faithful fiber functor. -/
theorem symmetricFiberFunctorExists_holds : SymmetricFiberFunctorExists.{v, u} :=
  symmetricFiberFunctorExists_of_frameFunctorExists frameFunctorExists_holds

/-- **Deligne's theorem** (fusion case): a symmetric fusion category over `ℂ` with positive
dimensions is braided-equivalent to `FDRep ℂ G` for a finite group `G`. -/
theorem deligneTannakian_holds : DeligneTannakian.{v, u} :=
  deligneTannakian_of_symmetricFiberFunctorExists symmetricFiberFunctorExists_holds

end VOA.Huang.TensorCat.DeligneFiber

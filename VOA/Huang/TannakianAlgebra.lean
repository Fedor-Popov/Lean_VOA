/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianMain
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# The regular algebra of `Rep(V)_{h∈ℤ}`

* `Equivalence.inverseBraided` — the inverse of a braided equivalence is braided (Mathlib has only
  `Equivalence.inverseMonoidal`);
* `regularAlgebra_of_factorized` — under the hypotheses of `tannakian_dims_of_factorized`, the
  trivial-twist part `C_{θ=1}` contains a **commutative, haploid algebra object** `A`
  (`dim Hom(𝟙, A) = 1`), with `dim Hom(A, X_i) = d_i` for every simple of trivial twist: the
  object `A ≅ ⊕_{h_a ∈ ℤ} d_a X_a` that Huang–Kirillov–Lepowsky turn into the extension `W ⊇ V`
  (GR Prop. 2.13). It has trivial twist by construction.

Conditional only on `DeligneTannakian` and the stated categorical data.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

section InverseBraided

variable {C₁ : Type*} [Category C₁] [MonoidalCategory C₁] [BraidedCategory C₁]
  {D₁ : Type*} [Category D₁] [MonoidalCategory D₁] [BraidedCategory D₁]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of a braided equivalence is braided. -/
@[reducible] def Equivalence.inverseBraided (e : C₁ ≌ D₁) [e.functor.Braided] :
    e.inverse.Braided :=
  letI := e.inverseMonoidal
  { braided := fun X Y => by
      apply e.functor.map_injective
      apply (Iso.cancel_iso_hom_right _ _ (e.counitIso.app (Y ⊗ X))).mp
      have hn := e.counit.naturality (β_ X Y).hom
      simp only [Functor.comp_map, Functor.id_map] at hn
      simp only [Functor.map_comp, Iso.app_hom]
      change (_ ≫ _) ≫ e.counit.app (Y ⊗ X) = (_ ≫ _) ≫ e.counit.app (Y ⊗ X)
      simp only [Category.assoc]
      erw [hn]
      have h1 := CategoryTheory.Equivalence.functor_map_μ_inverse_comp_counit_app_tensor e X Y
      have h2 := CategoryTheory.Equivalence.functor_map_μ_inverse_comp_counit_app_tensor e Y X
      erw [reassoc_of% h1, h2]
      rw [Functor.map_braiding]
      simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
      rw [BraidedCategory.braiding_naturality] }

end InverseBraided

section Regular

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C] {R : RibbonStructure C}

/-- `Hom` spaces across a `ℂ`-linear fully faithful functor. -/
def homLinearEquivOfFullyFaithful {D₁ E₁ : Type*} [Category D₁] [Preadditive D₁] [Linear ℂ D₁]
    [Category E₁] [Preadditive E₁] [Linear ℂ E₁] (Φ : D₁ ⥤ E₁) [Φ.Additive] [Φ.Linear ℂ]
    [Φ.Full] [Φ.Faithful] (X Y : D₁) : (X ⟶ Y) ≃ₗ[ℂ] (Φ.obj X ⟶ Φ.obj Y) :=
  LinearEquiv.ofBijective (Φ.mapLinearMap ℂ) ⟨Φ.map_injective, Φ.map_surjective⟩

/-- **The regular algebra of `Rep(V)_{h∈ℤ}`, conditional on Deligne.**  Under the hypotheses
of `tannakian_dims_of_factorized`, the trivial-twist part contains a commutative haploid algebra
object `A` with `dim Hom(A, X_i) = d_i` for every simple of trivial twist. -/
theorem regularAlgebra_of_factorized (hDel : DeligneTannakian.{v, u}) (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ))
    (hsym : R.SymDimAgrees) :
    letI := isMonoidal_trivialTwist_of_factorized U hS
    letI := symmetricTrivialTwist_of_factorized U hS
    ∃ (A : TT R) (_ : MonObj A), IsCommMonObj A ∧ finrank ℂ (𝟙_ (TT R) ⟶ A) = 1 ∧
      ∀ (i : F.ι) (hi : R.T i = 1), (finrank ℂ (A ⟶ ttSimple R ⟨i, hi⟩) : ℂ) = U.d i := by
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  obtain ⟨G, hG, hGf, Φ, ⟨hbr⟩, hlin, heq, hdim⟩ := tannakian_dims_of_factorized hDel U hS hsym
  letI := hbr
  let e := Φ.asEquivalence
  letI : e.functor.Braided := hbr
  letI : e.inverse.Braided := Equivalence.inverseBraided e
  let Fun : FDRep ℂ G := TannakaDuality.FiniteGroup.rightFDRep
  letI : MonObj (e.inverse.obj Fun) := Functor.monObjObj Fun
  haveI : IsCommMonObj (e.inverse.obj Fun) := Functor.isCommMonObj_obj
  haveI : HasBinaryBiproducts (TT R) := hasBinaryBiproducts_of_finite_biproducts _
  haveI : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  refine ⟨e.inverse.obj Fun, inferInstance, inferInstance, ?_, ?_⟩
  · rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
    exact (Linear.homCongr ℂ (Functor.Monoidal.εIso Φ).symm (e.counitIso.app Fun)).finrank_eq.trans
      VOA.Huang.Tannakian.finrank_hom_unit_fun
  · intro i hi
    rw [(homLinearEquivOfFullyFaithful Φ _ _).finrank_eq]
    have h := (Linear.homCongr ℂ (e.counitIso.app Fun)
      (Iso.refl (Φ.obj (ttSimple R ⟨i, hi⟩)))).finrank_eq
    change _ = finrank ℂ (Fun ⟶ Φ.obj (ttSimple R ⟨i, hi⟩)) at h
    rw [VOA.Huang.Tannakian.finrank_hom_rightFDRep] at h
    change (finrank ℂ ((e.inverse ⋙ e.functor).obj Fun ⟶ Φ.obj (ttSimple R ⟨i, hi⟩)) : ℂ) = _
    rw [h, (hdim i hi).1]

end Regular

end VOA.Huang.TensorCat

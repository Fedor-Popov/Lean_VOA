/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLNiceSimple
import VOA.Huang.BuhlSpanningMain
import VOA.Modules.C2Cofinite

/-!
# HKL niceness, part 2: the extension is `C₂`-cofinite

`extVOA_c2Cofinite`: for strongly rational `V`, the extension `W = extVOA F μ η …` is
`C₂`-cofinite.  Two steps:

* `moduleC2Cofinite_ordinary` — every ordinary `V`-module `X` is `C₂`-cofinite as a module: `X` is a
  finite direct sum of irreducible lowest-weight modules (`semisimple_lw_pbw`), each `C₂`-cofinite
  (Buhl, `moduleC2Input_holds`), and `X/C₂(X)` is the image of `Π_j Y_j/C₂(Y_j)`;
* `C₂(A as V-module) ⊆ C₂(W)` since `(η a)₍₋₂₎ = a₍₋₂₎` on `A`, so `W/C₂(W)` is a quotient of
  `A/C₂(A)`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLNice

open CategoryTheory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.FusionC2

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- Module maps send `C₂(X)` into `C₂(Y)`. -/
theorem C2M_le_comap {X Y : Ordinary V} (φ : X ⟶ Y) :
    C2M X.isMod.toWeakModule ≤ (C2M Y.isMod.toWeakModule).comap φ.val := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, rfl⟩
  change φ.val (mode (X.isMod.YM a) (-2) x) ∈ C2M Y.isMod.toWeakModule
  rw [φ.property a (-2) x]
  exact Submodule.subset_span ⟨a, φ.val x, rfl⟩

/-- A module that is a retract-sum of finitely many `C₂`-cofinite modules is `C₂`-cofinite. -/
theorem moduleC2Cofinite_of_decomp {X : Ordinary V} {n : ℕ} (Y : Fin n → Ordinary V)
    (π : ∀ j, X ⟶ Y j) (ι : ∀ j, Y j ⟶ X) (htot : ∑ j, π j ≫ ι j = 𝟙 X)
    (hY : ∀ j, ModuleC2Cofinite (Y j).isMod.toWeakModule) :
    ModuleC2Cofinite X.isMod.toWeakModule := by
  classical
  haveI : ∀ j, FiniteDimensional ℂ ((Y j).carrier ⧸ C2M (Y j).isMod.toWeakModule) := hY
  let L : (∀ j, (Y j).carrier ⧸ C2M (Y j).isMod.toWeakModule) →ₗ[ℂ]
      X.carrier ⧸ C2M X.isMod.toWeakModule :=
    ∑ j, (Submodule.mapQ _ _ (ι j).val (C2M_le_comap (ι j))).comp (LinearMap.proj j)
  have hsurj : Function.Surjective L := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    refine ⟨fun j => Submodule.mkQ _ ((π j).val x), ?_⟩
    simp only [L, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
    change ∑ j, (C2M X.isMod.toWeakModule).mkQ ((ι j).val ((π j).val x)) =
      (C2M X.isMod.toWeakModule).mkQ x
    rw [← map_sum]
    congr 1
    have h := congrArg (fun φ : X ⟶ X => φ.val x) htot
    simp only [Ordinary.sum_val, Ordinary.comp_apply, Ordinary.id_apply] at h
    exact h
  exact Module.Finite.of_surjective L hsurj

/-- **Every ordinary module of a strongly rational VOA is `C₂`-cofinite.** -/
theorem moduleC2Cofinite_ordinary (hV : StronglyRational V) (X : Ordinary V) :
    ModuleC2Cofinite X.isMod.toWeakModule := by
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hV X
  let g : Fin n → Ordinary V := fun j => Ordinary.of (R j).isMod
  refine moduleC2Cofinite_of_decomp g (fun j => e.hom ≫ biproduct.π g j)
    (fun j => biproduct.ι g j ≫ e.inv) ?_
    (fun j => VOA.Huang.BuhlSpanning.moduleC2Input_holds 𝒱 V hV (R j) (hR j))
  have h1 : ∑ j, (e.hom ≫ biproduct.π g j) ≫ biproduct.ι g j ≫ e.inv =
      e.hom ≫ (∑ j, biproduct.π g j ≫ biproduct.ι g j) ≫ e.inv := by
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Category.assoc]
  rw [h1, biproduct.total, Category.id_comp, e.hom_inv_id]

variable {F : FusionChoice V} {A : Ordinary V} {m : tensorObj F A A ⟶ A}
  {η : vacuumObject ⟶ A}
  {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

/-- **The extension is `C₂`-cofinite.** -/
theorem extVOA_c2Cofinite (hV : StronglyRational V) :
    C2Cofinite (extVOA F m η hl hr htw hloc hvac hpos) := by
  set W := extVOA F m η hl hr htw hloc hvac hpos with hW
  have hle : C2M A.isMod.toWeakModule ≤ O₂ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, rfl⟩
    refine Submodule.subset_span ⟨η.val a, x, ?_⟩
    rw [extVOA_smul, ext_unit_left_int F m η hl]
  haveI : FiniteDimensional ℂ (A.carrier ⧸ C2M A.isMod.toWeakModule) :=
    moduleC2Cofinite_ordinary hV A
  change FiniteDimensional ℂ (A.carrier ⧸ O₂ W)
  exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

end VOA.Huang.HKLNice

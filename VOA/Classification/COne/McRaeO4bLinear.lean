/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2LogMonoidal
import VOA.Classification.COne.McRaeM2TensorGeneration
import VOA.Classification.COne.McRaeO4bAbstract

/-! # O4b: the logarithmic monoidal category is `ℂ`-linear monoidal

This file shows that the logarithmic tensor product of `C = LogModuleCat W` is additive and
`ℂ`-linear in each variable. In Mathlib terms, `logarithmicMonoidalCategory hC2` is
`MonoidalPreadditive` (`logarithmic_monoidalPreadditive`) and `MonoidalLinear ℂ`
(`logarithmic_monoidalLinear`).

The proof uses that a map out of a tensor object is determined by its values on the canonical
zero-log tensor modes (`tensor_linearMap_ext`). The tensor of two maps acts on those modes by
`tensorMap_intertwiner`, pointwise: `tensorMorphism_apply`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory MonoidalCategory VOA.Classification.COne VOA.C2Rigid.LocalInjective
  VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The canonical logarithmic tensor operator of two objects of `C`. -/
abbrev canonical (N P : LogModuleCat W) :=
  tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration

/-- The tensor of two maps on a canonical tensor mode. -/
theorem tensorMorphism_apply {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) (g : N₂ ⟶ P₂)
    (n : ℂ) (k : ℕ) (x : N₁) (y : N₂) :
    (tensorMorphism hC2 f g).1 ((canonical hC2 N₁ N₂).1 n k x y) =
      (canonical hC2 P₁ P₂).1 n k (f.1 x) (g.1 y) :=
  congrArg (fun Y : LogIntertwiningOperator N₁.act.toWeakModule N₂.act.toWeakModule
      (tensorModule hC2 P₁.act P₂.act P₁.finiteGeneration P₂.finiteGeneration).toWeakModule =>
      Y.1 n k x y)
    (tensorMap_intertwiner hC2 N₁.act N₂.act N₁.finiteGeneration N₂.finiteGeneration
      P₁.act P₂.act P₁.finiteGeneration P₂.finiteGeneration (toWeakHom f) (toWeakHom g))

/-- Maps out of a tensor object are determined on canonical zero-log modes. -/
theorem tensorObject_hom_ext {N₁ N₂ P : LogModuleCat W} {F F' : tensorObject hC2 N₁ N₂ ⟶ P}
    (h : ∀ (n : ℂ) (x : N₁) (y : N₂), F.1 ((canonical hC2 N₁ N₂).1 n 0 x y) =
      F'.1 ((canonical hC2 N₁ N₂).1 n 0 x y)) : F = F' := by
  apply hom_ext
  intro q
  exact congrArg (fun φ => φ q) (tensor_linearMap_ext hC2 N₁.act N₂.act N₁.finiteGeneration
    N₂.finiteGeneration (f := F.1) (g := F'.1) h)

/-- Evaluation of morphisms at a point is additive. -/
def evalAddHom {N P : LogModuleCat W} (x : N) : (N ⟶ P) →+ P where
  toFun f := f.1 x
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_apply {N P : LogModuleCat W} {ι : Type*} (s : Finset ι) (f : ι → (N ⟶ P)) (x : N) :
    (∑ i ∈ s, f i).1 x = ∑ i ∈ s, (f i).1 x :=
  map_sum (evalAddHom x) f s

theorem tensorMorphism_add_left {N₁ N₂ P₁ P₂ : LogModuleCat W} (f f' : N₁ ⟶ P₁) (g : N₂ ⟶ P₂) :
    tensorMorphism hC2 (f + f') g = tensorMorphism hC2 f g + tensorMorphism hC2 f' g := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 (f + f') g).1 _ =
    (tensorMorphism hC2 f g).1 _ + (tensorMorphism hC2 f' g).1 _
  rw [tensorMorphism_apply, tensorMorphism_apply, tensorMorphism_apply]
  exact LinearMap.map_add₂ ((canonical hC2 P₁ P₂).1 n 0) (f.1 x) (f'.1 x) (g.1 y)

theorem tensorMorphism_add_right {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) (g g' : N₂ ⟶ P₂) :
    tensorMorphism hC2 f (g + g') = tensorMorphism hC2 f g + tensorMorphism hC2 f g' := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 f (g + g')).1 _ =
    (tensorMorphism hC2 f g).1 _ + (tensorMorphism hC2 f g').1 _
  rw [tensorMorphism_apply, tensorMorphism_apply, tensorMorphism_apply]
  exact map_add _ _ _

theorem tensorMorphism_zero_left {N₁ N₂ P₁ P₂ : LogModuleCat W} (g : N₂ ⟶ P₂) :
    tensorMorphism hC2 (0 : N₁ ⟶ P₁) g = 0 := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 (0 : N₁ ⟶ P₁) g).1 _ = 0
  rw [tensorMorphism_apply]
  change (canonical hC2 P₁ P₂).1 n 0 0 (g.1 y) = 0
  rw [map_zero, LinearMap.zero_apply]

theorem tensorMorphism_zero_right {N₁ N₂ P₁ P₂ : LogModuleCat W} (f : N₁ ⟶ P₁) :
    tensorMorphism hC2 f (0 : N₂ ⟶ P₂) = 0 := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 f (0 : N₂ ⟶ P₂)).1 _ = 0
  rw [tensorMorphism_apply]
  exact map_zero _

theorem tensorMorphism_smul_left {N₁ N₂ P₁ P₂ : LogModuleCat W} (c : ℂ) (f : N₁ ⟶ P₁)
    (g : N₂ ⟶ P₂) : tensorMorphism hC2 (c • f) g = c • tensorMorphism hC2 f g := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 (c • f) g).1 _ = c • (tensorMorphism hC2 f g).1 _
  rw [tensorMorphism_apply, tensorMorphism_apply]
  exact LinearMap.map_smul₂ ((canonical hC2 P₁ P₂).1 n 0) c (f.1 x) (g.1 y)

theorem tensorMorphism_smul_right {N₁ N₂ P₁ P₂ : LogModuleCat W} (c : ℂ) (f : N₁ ⟶ P₁)
    (g : N₂ ⟶ P₂) : tensorMorphism hC2 f (c • g) = c • tensorMorphism hC2 f g := by
  apply tensorObject_hom_ext hC2
  intro n x y
  change (tensorMorphism hC2 f (c • g)).1 _ = c • (tensorMorphism hC2 f g).1 _
  rw [tensorMorphism_apply, tensorMorphism_apply]
  exact map_smul _ _ _

/-- **The logarithmic tensor product is additive in each variable.** -/
theorem logarithmic_monoidalPreadditive :
    letI := logarithmicMonoidalCategory hC2
    MonoidalPreadditive (LogModuleCat W) := by
  letI := logarithmicMonoidalCategory hC2
  exact
    { whiskerLeft_zero := tensorMorphism_zero_right hC2 _
      zero_whiskerRight := tensorMorphism_zero_left hC2 _
      whiskerLeft_add := fun f g => tensorMorphism_add_right hC2 _ f g
      add_whiskerRight := fun f g => tensorMorphism_add_left hC2 f g _ }

/-- **The logarithmic tensor product is `ℂ`-linear in each variable.** -/
theorem logarithmic_monoidalLinear :
    letI := logarithmicMonoidalCategory hC2
    haveI := logarithmic_monoidalPreadditive hC2
    MonoidalLinear ℂ (LogModuleCat W) := by
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  exact
    { whiskerLeft_smul := fun _ _ _ c f => tensorMorphism_smul_right hC2 c _ f
      smul_whiskerRight := fun c _ _ f _ => tensorMorphism_smul_left hC2 c f _ }

end VOA.LogTensor.LogModuleCat

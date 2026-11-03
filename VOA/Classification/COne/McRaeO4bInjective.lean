/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO4bLinear

/-! # O4b: joint injectivity of twisted products, element form

This file is generic: it works for any object `A` of `C = LogModuleCat W`. Suppose we have:
- maps `m : A ⊠ A ⟶ A`, `u : 𝟙 ⟶ A`, `ψ_g : A ⊠ A ⟶ A` with `ψ_1 = m`;
- the identity `GaloisData.unit_cancel` (as `hU`);
- an identity of the shape of `GaloisData.sum_theta`, whose right side factors through
  `(A ⊠ A) ◁ ψ_{y⁻¹}` (as `hT`);
- a vector `w'` with `ψ_g(w') = δ_{g,1} u(𝟙)`.

Then the `ψ_g` are jointly injective on elements: `injective_of_theta`.

The proof evaluates `hT` on the canonical tensor mode `w' ⊠₋₁ w`. Stating it for a generic `A`
keeps the element-level defeq checks cheap.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.Classification.COne VOA.C2Rigid.LocalInjective VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The left unit inverse on an element is the vacuum tensor mode. -/
theorem leftUnitIso_inv_apply (N : LogModuleCat W) (x : N) :
    (leftUnitIso hC2 N).inv.1 x = (canonical hC2 unitObject N).1 (-1) 0 W.vacuum x := rfl

/-- **Joint injectivity from the Θ identity** (element form, generic `A`). -/
theorem injective_of_theta {A : LogModuleCat W} (m : tensorObject hC2 A A ⟶ A)
    (u : (unitObject : LogModuleCat W) ⟶ A) {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (ψ : G → (tensorObject hC2 A A ⟶ A))
    (H : G → (tensorObject hC2 (tensorObject hC2 A A) A ⟶ tensorObject hC2 A A))
    (hU : (leftUnitIso hC2 (tensorObject hC2 A A)).inv ≫
      tensorMorphism hC2 u (𝟙 (tensorObject hC2 A A)) ≫ (associatorIso hC2 A A A).inv ≫
      tensorMorphism hC2 m (𝟙 A) = 𝟙 _)
    (hT : ∑ h, tensorMorphism hC2 (ψ h) (𝟙 (tensorObject hC2 A A)) ≫
        (associatorIso hC2 A A A).inv ≫ tensorMorphism hC2 (ψ h) (𝟙 A) =
      ∑ y, tensorMorphism hC2 (𝟙 (tensorObject hC2 A A)) (ψ y⁻¹) ≫ H y)
    (hψ1 : ψ 1 = m) (w' : tensorObject hC2 A A)
    (hw' : ∀ g, (ψ g).1 w' = if g = 1 then u.1 W.vacuum else 0)
    (w : tensorObject hC2 A A) (h : ∀ g, (ψ g).1 w = 0) : w = 0 := by
  have hU' := congrArg (fun F => F.1 w) hU
  change (tensorMorphism hC2 m (𝟙 A)).1 ((associatorIso hC2 A A A).inv.1
    ((tensorMorphism hC2 u (𝟙 _)).1 ((leftUnitIso hC2 (tensorObject hC2 A A)).inv.1 w))) = w
    at hU'
  rw [leftUnitIso_inv_apply, tensorMorphism_apply] at hU'
  let z := (canonical hC2 (tensorObject hC2 A A) (tensorObject hC2 A A)).1 (-1) 0 w' w
  have hT' := congrArg (fun F => F.1 z) hT
  simp only [sum_apply] at hT'
  have hL : ∀ g : G, (tensorMorphism hC2 (ψ g) (𝟙 (tensorObject hC2 A A)) ≫
      (associatorIso hC2 A A A).inv ≫ tensorMorphism hC2 (ψ g) (𝟙 A)).1 z =
      if g = 1 then w else 0 := by
    intro g
    change (tensorMorphism hC2 (ψ g) (𝟙 A)).1 ((associatorIso hC2 A A A).inv.1
      ((tensorMorphism hC2 (ψ g) (𝟙 (tensorObject hC2 A A))).1 z)) = _
    rw [tensorMorphism_apply]
    by_cases hg : g = 1
    · have hv : (ψ g).1 w' = u.1 W.vacuum := by rw [hw' g, if_pos hg]
      rw [hv, if_pos hg, hg, hψ1]
      exact hU'
    · have hv : (ψ g).1 w' = 0 := by rw [hw' g, if_neg hg]
      rw [hv, if_neg hg, map_zero, LinearMap.zero_apply]
      erw [map_zero, map_zero]
  have hR : ∀ y : G, (tensorMorphism hC2 (𝟙 (tensorObject hC2 A A)) (ψ y⁻¹) ≫ H y).1 z = 0 := by
    intro y
    change (H y).1 ((tensorMorphism hC2 (𝟙 (tensorObject hC2 A A)) (ψ y⁻¹)).1 z) = 0
    have e : (tensorMorphism hC2 (𝟙 (tensorObject hC2 A A)) (ψ y⁻¹)).1 z = 0 := by
      refine (tensorMorphism_apply hC2 _ _ (-1) 0 w' w).trans ?_
      have h0 : (ψ y⁻¹).1 w = 0 := h _
      exact (congrArg ((canonical hC2 (tensorObject hC2 A A) A).1 (-1) 0 w') h0).trans
        (map_zero _)
    exact (congrArg (H y).1 e).trans (map_zero _)
  simp only [hL, hR, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero] at hT'
  exact hT'

end VOA.LogTensor.LogModuleCat

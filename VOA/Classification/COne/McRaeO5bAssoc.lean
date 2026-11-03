/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5Main
import VOA.Classification.COne.McRaeO3Assoc
import VOA.Classification.COne.McRaeM2LogBraidedCurves

/-! # O5b, step 1: the module axiom as analytic associativity of the action operator

For a left module `(X, a)` of the O3 algebra `V = vObj G hfg` in `C = LogModuleCat (W^G)`, the
module axiom `μ ▷ X ≫ a = α ≫ V ◁ a ≫ a` (`IsLeftModule.mul_smul`), tested on completed canonical
iterates, says (`actY_completed_assoc`):

  completed product `⟨f, 𝒴_a(u, 1 + e^t) 𝒴_a(v, 1) x⟩`
    = completed iterate `⟨f, 𝒴_a(Y_W(u, e^t) v, 1) x⟩`

on the overlap domain, where `𝒴_a = actY a = a ∘ 𝒴_⊠`. The left path is the iterate of `actY a`
with `Y_W` (`μ ∘ 𝒴_⊠ = Y_W`, `mulWeakHom_intertwiner`); the right path is the product of
`actY a` with itself (`tensorAssociatorHom_completed_shift`). This is the converse direction of
O3's `mulHom_assoc`.

No `sorry`, no new axioms.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open CategoryTheory MonoidalCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open VOA.Huang.AssocExpansion VOA.Classification.COne.McRaeO3 VOA.Classification.COne.McRaeO5
open VOA.Classification.COne.McRaeO4c VOA.Huang.LogBraided

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

section Assoc
variable {X : LogModuleCat (orbifoldVOA G)} (a : tensorObject hC2 (vObj G hfg) X ⟶ X)

/-- The left path `(μ ⊠ 1) ≫ a` on a completed canonical iterate is the completed iterate of
`actY a` with `Y_W`. -/
theorem left_path_iterate {c β : ℂ} {x : X} (hx : x ∈ X.act.weight c) (f : X →ₗ[ℂ] ℂ)
    (u v : V) (ℓ₀ ℓ₂ : ℂ) :
    completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act
        (tensorObject hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X).act
        (tensorObject hC2 (vObj G hfg) (vObj G hfg)).act
        (canY hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X)
        (canY hC2 (vObj G hfg) (vObj G hfg)) ℓ₀ ℓ₂ c β
        (f ∘ₗ (tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 X) ≫ a).1) u v ⟨x, hx⟩ =
      completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
        (actY hC2 a) (vertexIntertwiner G) ℓ₀ ℓ₂ c β f u v ⟨x, hx⟩ := by
  have h1 := completedLogIterate_postcompose (vObj G hfg).act (vObj G hfg).act X.act
    (tensorObject hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X).act
    (tensorObject hC2 (vObj G hfg) (vObj G hfg)).act X.act
    (toWeakHom (tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 X) ≫ a))
    (canY hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X)
    (canY hC2 (vObj G hfg) (vObj G hfg)) ℓ₀ ℓ₂ c β f u v ⟨x, hx⟩
  refine h1.symm.trans ?_
  have h2 := post_tensorMorphism_comp hC2 (mulHom G hfg hC2) (𝟙 X) a
  rw [h2]
  have h3 := completedLogIterate_precompose_left (vObj G hfg).act (vObj G hfg).act X.act X.act
    (tensorObject hC2 (vObj G hfg) (vObj G hfg)).act (vObj G hfg).act
    (toWeakHom (mulHom G hfg hC2)) (actY hC2 a) (canY hC2 (vObj G hfg) (vObj G hfg))
    ℓ₀ ℓ₂ c β f u v ⟨x, hx⟩
  refine h3.trans ?_
  have h4 : postcompose (toWeakHom (mulHom G hfg hC2)) (canY hC2 (vObj G hfg) (vObj G hfg)) =
      vertexIntertwiner G := mulWeakHom_intertwiner G hfg hC2
  rw [h4]

/-- The right path `α ≫ (1 ⊠ a) ≫ a` on a completed canonical iterate is the completed product
of `actY a` with itself. -/
theorem right_path_product {α c β : ℂ} {u : V} {x : X} (hu : u ∈ (vObj G hfg).act.weight α)
    {v : V} {b : ℂ} (hv : v ∈ (vObj G hfg).act.weight b)
    (hx : x ∈ X.act.weight c) (f : X →ₗ[ℂ] ℂ) {t : ℂ} (ht : t ∈ overlapDomain) :
    completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act
        (tensorObject hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X).act
        (tensorObject hC2 (vObj G hfg) (vObj G hfg)).act
        (canY hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X)
        (canY hC2 (vObj G hfg) (vObj G hfg)) t 0 c β
        (f ∘ₗ ((associatorIso hC2 (vObj G hfg) (vObj G hfg) X).hom ≫
          tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1) u v ⟨x, hx⟩ =
      completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) (Complex.log (1 + Complex.exp t)) 0 α β f ⟨u, hu⟩ v x := by
  have hA := tensorAssociatorHom_completed_shift (β := β) hC2 (vObj G hfg).act (vObj G hfg).act
    X.act (vObj G hfg).finiteGeneration (vObj G hfg).finiteGeneration X.finiteGeneration hu hv hx
    (f ∘ₗ (tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1) ht 0
  simp only [add_zero] at hA
  refine hA.symm.trans ?_
  have h1 := completedLogProduct_postcompose (vObj G hfg).act (vObj G hfg).act X.act
    (tensorObject hC2 (vObj G hfg) (tensorObject hC2 (vObj G hfg) X)).act
    (tensorObject hC2 (vObj G hfg) X).act X.act
    (toWeakHom (tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a))
    (canY hC2 (vObj G hfg) (tensorObject hC2 (vObj G hfg) X))
    (canY hC2 (vObj G hfg) X) (Complex.log (1 + Complex.exp t)) 0 α β f ⟨u, hu⟩ v x
  refine h1.symm.trans ?_
  have h2 := post_tensorMorphism_comp hC2 (𝟙 (vObj G hfg)) a a
  rw [h2]
  exact completedLogProduct_precompose_right (vObj G hfg).act (vObj G hfg).act X.act X.act
    (tensorObject hC2 (vObj G hfg) X).act X.act (toWeakHom a) (actY hC2 a)
    (canY hC2 (vObj G hfg) X) (Complex.log (1 + Complex.exp t)) 0 α β f ⟨u, hu⟩ v x

/-- **Analytic associativity of the action operator** from the module axiom. -/
theorem actY_completed_assoc (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    {α b c β : ℂ} {u v : V} {x : X} (hu : u ∈ (vObj G hfg).act.weight α)
    (hv : v ∈ (vObj G hfg).act.weight b) (hx : x ∈ X.act.weight c) (f : X →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t ∈ overlapDomain) :
    completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) (Complex.log (1 + Complex.exp t)) 0 α β f ⟨u, hu⟩ v x =
      completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
        (actY hC2 a) (vertexIntertwiner G) t 0 c β f u v ⟨x, hx⟩ := by
  letI := logarithmicMonoidalCategory hC2
  have hm := hX.mul_smul
  have hm' : (tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 X) ≫ a).1 =
      ((associatorIso hC2 (vObj G hfg) (vObj G hfg) X).hom ≫
        tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1 := congrArg (fun F => F.1) hm
  rw [← right_path_product G hfg hC2 a hu hv hx f ht, ← left_path_iterate G hfg hC2 a hx f u v t 0,
    hm']

/-- The right path at a shifted scale `e^s`. -/
theorem right_path_product_shift {α c β : ℂ} {u : V} {x : X}
    (hu : u ∈ (vObj G hfg).act.weight α) {v : V} {b : ℂ} (hv : v ∈ (vObj G hfg).act.weight b)
    (hx : x ∈ X.act.weight c) (f : X →ₗ[ℂ] ℂ) {t : ℂ} (ht : t ∈ overlapDomain) (s : ℂ) :
    completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act
        (tensorObject hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X).act
        (tensorObject hC2 (vObj G hfg) (vObj G hfg)).act
        (canY hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg)) X)
        (canY hC2 (vObj G hfg) (vObj G hfg)) (t + s) s c β
        (f ∘ₗ ((associatorIso hC2 (vObj G hfg) (vObj G hfg) X).hom ≫
          tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1) u v ⟨x, hx⟩ =
      completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) (Complex.log (1 + Complex.exp t) + s) s α β f ⟨u, hu⟩ v x := by
  have hA := tensorAssociatorHom_completed_shift (β := β) hC2 (vObj G hfg).act (vObj G hfg).act
    X.act (vObj G hfg).finiteGeneration (vObj G hfg).finiteGeneration X.finiteGeneration hu hv hx
    (f ∘ₗ (tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1) ht s
  refine hA.symm.trans ?_
  have h1 := completedLogProduct_postcompose (vObj G hfg).act (vObj G hfg).act X.act
    (tensorObject hC2 (vObj G hfg) (tensorObject hC2 (vObj G hfg) X)).act
    (tensorObject hC2 (vObj G hfg) X).act X.act
    (toWeakHom (tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a))
    (canY hC2 (vObj G hfg) (tensorObject hC2 (vObj G hfg) X))
    (canY hC2 (vObj G hfg) X) (Complex.log (1 + Complex.exp t) + s) s α β f ⟨u, hu⟩ v x
  refine h1.symm.trans ?_
  have h2 := post_tensorMorphism_comp hC2 (𝟙 (vObj G hfg)) a a
  rw [h2]
  exact completedLogProduct_precompose_right (vObj G hfg).act (vObj G hfg).act X.act X.act
    (tensorObject hC2 (vObj G hfg) X).act X.act (toWeakHom a) (actY hC2 a)
    (canY hC2 (vObj G hfg) X) (Complex.log (1 + Complex.exp t) + s) s α β f ⟨u, hu⟩ v x

/-- **Analytic associativity of the action operator at every scale.** -/
theorem actY_completed_assoc_shift (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    {α b c β : ℂ} {u v : V} {x : X} (hu : u ∈ (vObj G hfg).act.weight α)
    (hv : v ∈ (vObj G hfg).act.weight b) (hx : x ∈ X.act.weight c) (f : X →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t ∈ overlapDomain) (s : ℂ) :
    completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) (Complex.log (1 + Complex.exp t) + s) s α β f ⟨u, hu⟩ v x =
      completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
        (actY hC2 a) (vertexIntertwiner G) (t + s) s c β f u v ⟨x, hx⟩ := by
  letI := logarithmicMonoidalCategory hC2
  have hm := hX.mul_smul
  have hm' : (tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 X) ≫ a).1 =
      ((associatorIso hC2 (vObj G hfg) (vObj G hfg) X).hom ≫
        tensorMorphism hC2 (𝟙 (vObj G hfg)) a ≫ a).1 := congrArg (fun F => F.1) hm
  rw [← right_path_product_shift G hfg hC2 a hu hv hx f ht s,
    ← left_path_iterate G hfg hC2 a hx f u v (t + s) s, hm']

end Assoc

end VOA.Classification.COne.McRaeO5b

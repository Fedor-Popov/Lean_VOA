/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO6Quotient
import VOA.Classification.COne.McRaeO3RightExact

/-! # O6: McRae Lemma 4.21 (surjections in `C` split), conditional on the analytic bridge

`W` simple, `G ≤ Aut W` finite, `hC2 : C2Cofinite W^G`, `C = LogModuleCat W^G`, `V = vObj` the
O3 algebra with unit `ι` and counit `ε` (`ι ≫ ε = 𝟙`).

* `section_of_whisker` (any monoidal category): if `ι : 𝟙 ⟶ A`, `ε : A ⟶ 𝟙` with `ι ≫ ε = 𝟙`,
  and `s ≫ (A ◁ f) = 𝟙`, then `σ := λ⁻¹ ≫ (ι ▷ Y₂) ≫ s ≫ (ε ▷ Y₁) ≫ λ` has `σ ≫ f = 𝟙`.
* `lemma_4_21`: if every `W^{⟨g⟩}` is admissibly rational, every surjective `C`-morphism
  `f : Y₁ ⟶ Y₂` has a `C`-section. Proof (McRae Lemma 4.21): `V ◁ f` is an epimorphism
  (`tensorMorphism_epi`), hence surjective (`surjective_of_epi`), and a map of induced
  `V`-modules (`isLeftModule_induced`, `isModuleHom_induced`); O5 (`exists_section_of_twisted`)
  splits it; `section_of_whisker` descends the splitting.
* `V2m_lemma_4_21`: the case `W = V₂`, where the rationality of the cyclic orbifolds is
  `V2m_cyclic_admissiblyRational`.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO6
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.Classification.COne.McRaeO4c VOA.Classification.COne.McRaeO3
open VOA.Classification.COne.McRaeO5

/-- **Descent of sections along a split unit.** In any monoidal category, if `ι ≫ ε = 𝟙` and
`s ≫ (A ◁ f) = 𝟙`, then `λ⁻¹ ≫ (ι ▷ Y₂) ≫ s ≫ (ε ▷ Y₁) ≫ λ` is a section of `f`. -/
theorem section_of_whisker {C : Type*} [Category C] [MonoidalCategory C] {A : C}
    (ι : 𝟙_ C ⟶ A) (ε : A ⟶ 𝟙_ C) (hιε : ι ≫ ε = 𝟙 _) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)
    (s : A ⊗ Y₂ ⟶ A ⊗ Y₁) (hs : s ≫ A ◁ f = 𝟙 _) :
    ((λ_ Y₂).inv ≫ ι ▷ Y₂ ≫ s ≫ ε ▷ Y₁ ≫ (λ_ Y₁).hom) ≫ f = 𝟙 Y₂ := by
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, reassoc_of% hs,
    ← comp_whiskerRight_assoc, hιε, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

/-- **McRae Lemma 4.21 for `V` over `V^G`, conditional on the bridge.** If every cyclic
orbifold `W^{⟨g⟩}` is admissibly rational, every surjective morphism of `C = LogModuleCat W^G`
has a section in `C`. -/
theorem lemma_4_21 [Fintype G] [DecidableEq G] (hW : W.IsSimple)
    (hB : TwistedJacobiBridge G hfg hC2)
    (hrat : ∀ g : G, AdmissiblyRational (orbifoldVOA (Subgroup.zpowers (g : Aut W)))) :
    ∀ {Y₁ Y₂ : LogModuleCat (orbifoldVOA G)} (f : Y₁ ⟶ Y₂), Function.Surjective f.1 →
      ∃ σ : Y₂ ⟶ Y₁, σ ≫ f = 𝟙 Y₂ := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  intro Y₁ Y₂ f hf
  haveI hepi : Epi (vObj G hfg ◁ f) := tensorMorphism_epi hC2 f hf
  have hsurj : Function.Surjective (vObj G hfg ◁ f).1 := surjective_of_epi hC2 _
  obtain ⟨s, hs⟩ := exists_section_of_twisted G hfg hC2 hW hB hrat _ _ _ _
    (isLeftModule_induced (mulHom_one_mul G hfg hC2) (mulHom_assoc G hfg hC2) Y₁)
    (isLeftModule_induced (mulHom_one_mul G hfg hC2) (mulHom_assoc G hfg hC2) Y₂)
    (vObj G hfg ◁ f) (isModuleHom_induced f) hsurj
  exact ⟨_, section_of_whisker (unitHom G hfg) (counitHom G hfg) (unitHom_counitHom G hfg) f s hs⟩

/-- **O6 for `V₂`, conditional on the bridge.** For finite `G ≤ Aut V₂` with `C₂`-cofinite
`V₂^G`, every surjective morphism of `LogModuleCat V₂^G` has a section. -/
theorem V2m_lemma_4_21 (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G] [DecidableEq G]
    (hC2 : C2Cofinite (orbifoldVOA G))
    (hB : TwistedJacobiBridge G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2) :
    ∀ {Y₁ Y₂ : LogModuleCat (orbifoldVOA G)} (f : Y₁ ⟶ Y₂), Function.Surjective f.1 →
      ∃ σ : Y₂ ⟶ Y₁, σ ≫ f = 𝟙 Y₂ :=
  lemma_4_21 G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2 (V2m_isSimple 1 le_rfl) hB
    (fun g => V2m_cyclic_admissiblyRational _ (G.subtype.isOfFinOrder (isOfFinOrder_of_finite g)))

end VOA.Classification.COne.McRaeO6

/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO4cAbstract
import VOA.Classification.COne.McRaeO4bRigid

/-! # O4c, instance: McRae's Theorem 3.3 for `V` over `V^G`

`W` is a simple VOA and `G ≤ Aut W` is finite, with `hC2 : C2Cofinite (orbifoldVOA G)` and
`hfg : FinGen (orbifold G).adjointRestrict`. Let `V = vObj G hfg` be the O3 algebra in the
logarithmic braided category `C` of `W^G`-modules, and let `ĩ = coevHom` be the O4b
coevaluation.

* `mcraeData`: `(V, μ, ι, ε, G, ĩ)` satisfies `McRaeData` (McRae's Assumption 3.1 in Galois
  form). Every field comes from O3/O4b; the only new input is `autHom_comp_mul`.
* `theorem_3_3_orbifold`: every left `V`-module `(X, a)` in `C` has a complete family of
  orthogonal idempotent module endomorphisms `π_g` with `g`-twisted images.
* `twisted_hom_eq_zero_orbifold`: no nonzero module maps between `g₁`- and `g₂`-twisted
  modules for `g₁ ≠ g₂`.
* `V2m_theorem_3_3`: the case `W = V₂`, where `hfg` and simplicity are discharged.

Every proof here is a single `exact` of the abstract result (see the O4b pitfalls: no rewriting
on concrete tensor objects).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO4c
open CategoryTheory MonoidalCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO3
open VOA.Classification.COne.McRaeO4b

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

/-- The action is a group homomorphism: `autHom (g * h) = autHom h ≫ autHom g`. -/
theorem autHom_comp_mul (g h : G) :
    autHom G hfg (g * h) = autHom G hfg h ≫ autHom G hfg g := by
  apply hom_ext
  intro x
  rfl

/-- **McRae's Assumption 3.1** (Galois form) for `V` over `V^G`. -/
theorem mcraeData [Fintype G] [DecidableEq G] (hW : W.IsSimple) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    haveI := logarithmic_monoidalPreadditive hC2
    haveI := logarithmic_monoidalLinear hC2
    McRaeData (vObj G hfg) (mulHom G hfg hC2) (unitHom G hfg) (counitHom G hfg) G
      (autHom G hfg) (coevHom G hfg hC2 hW) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  exact
    { toGaloisData := galoisData G hfg hC2
      mul_comm := mulHom_comm G hfg hC2
      act_comp := autHom_comp_mul G hfg
      coev_psi := coevHom_psi G hfg hC2 hW }

/-- **McRae, Theorem 3.3, for `V` over `V^G`.** Every left `V`-module `(X, a)` in the
logarithmic braided category of `V^G`-modules has module endomorphisms `π_g` (`g ∈ G`) with
`π_g ≫ π_h = δ_{g,h} π_g` and `Σ_g π_g = 𝟙`, and the image of each `π_g` is `g`-twisted:
`(1 ⊠ π_g) ≫ M_{V,X} ≫ (g ⊠ 1) ≫ a = (1 ⊠ π_g) ≫ a`. -/
theorem theorem_3_3_orbifold [Fintype G] [DecidableEq G] (hW : W.IsSimple) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ (X : LogModuleCat (orbifoldVOA G)) (a : vObj G hfg ⊗ X ⟶ X),
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a →
      ∃ π : G → (X ⟶ X),
        (∀ g, a ≫ π g = vObj G hfg ◁ π g ≫ a) ∧
        (∀ g, vObj G hfg ◁ π g ≫ monodromy (vObj G hfg) X ≫ autHom G hfg g ▷ X ≫ a =
          vObj G hfg ◁ π g ≫ a) ∧
        (∀ g h, π g ≫ π h = if g = h then π g else 0) ∧
        ∑ g, π g = 𝟙 X := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  intro X a hX
  exact (mcraeData G hfg hC2 hW).theorem_3_3 hX

/-- **Hom-vanishing** (McRae, proof of Corollary 3.4): there are no nonzero `V`-module maps from
a `g₁`-twisted to a `g₂`-twisted `V`-module when `g₁ ≠ g₂`. -/
theorem twisted_hom_eq_zero_orbifold [Finite G] (hW : W.IsSimple) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ {X Y : LogModuleCat (orbifoldVOA G)} {a : vObj G hfg ⊗ X ⟶ X}
      {b : vObj G hfg ⊗ Y ⟶ Y} {g₁ g₂ : G},
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a →
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) b →
      IsTwisted a (autHom G hfg g₁) → IsTwisted b (autHom G hfg g₂) → g₁ ≠ g₂ →
      ∀ f : X ⟶ Y, IsModuleHom a b f → f = 0 := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  intro X Y a b g₁ g₂ hX hY h₁ h₂ hne f hf
  classical
  haveI := Fintype.ofFinite G
  exact (mcraeData G hfg hC2 hW).hom_eq_zero_of_twisted hY hX h₁ h₂ hne f hf

/-- **The case `V₂`**: McRae's Theorem 3.3 for `V₂` over `V₂^G`, for every finite
`G ≤ Aut V₂` with `C₂`-cofinite `V₂^G`. -/
theorem V2m_theorem_3_3 (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G] [DecidableEq G]
    (hC2 : C2Cofinite (orbifoldVOA G)) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ (X : LogModuleCat (orbifoldVOA G)) (a : V2mObj G ⊗ X ⟶ X),
      IsLeftModule (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2)
        (unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) a →
      ∃ π : G → (X ⟶ X),
        (∀ g, a ≫ π g = V2mObj G ◁ π g ≫ a) ∧
        (∀ g, V2mObj G ◁ π g ≫ monodromy (V2mObj G) X ≫
            autHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) g ▷ X ≫ a =
          V2mObj G ◁ π g ≫ a) ∧
        (∀ g h, π g ≫ π h = if g = h then π g else 0) ∧
        ∑ g, π g = 𝟙 X := by
  exact theorem_3_3_orbifold G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
    (V2m_isSimple 1 le_rfl)

end VOA.Classification.COne.McRaeO4c

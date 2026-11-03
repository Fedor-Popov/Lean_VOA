/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5Split

/-! # O5: surjections between twisted summands split (conditional on the analytic bridge)

`W` simple, `G ≤ Aut W` finite, `hC2 : C2Cofinite W^G`, `C = LogModuleCat W^G`, `V = vObj` the O3
algebra, `π_g = (mcraeData …).proj a g` McRae's O4c projections.

* `TwistedJacobiBridge G hfg hC2` (**Prop, open**): on the image of a module endomorphism `p` whose
  image is `g`-twisted, the integral log-free modes of the action operator `actY a` satisfy the
  Jacobi identity for `g`-fixed vectors. This is the one analytic input of O5 (step (b)).
* `twistData_of`: the categorical hypotheses plus the bridge give `TwistData` (steps (a) proved:
  `twisted_modes`, `unit_modes`, `modHom_modes`).
* `exists_twisted_section`: if `V^{⟨g⟩}` is admissibly rational, every surjective `V`-module
  map `f : X₁ ⟶ X₂` in `C` has a `C`-morphism `s_g : X₂ ⟶ X₁` with `s_g ≫ f = π_g`,
  `π_g ≫ s_g = s_g`, `s_g ≫ π_g = s_g`.
* `V2m_exists_twisted_section` (`W = V₂`, rationality of `V₂^{⟨g⟩}` discharged by
  `V2m_cyclic_admissiblyRational`) and `V2m_exists_section`: `s := Σ_g s_g` satisfies
  `s ≫ f = 𝟙` (the input of O6).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO4c VOA.Classification.COne.McRaeO3

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

/-- **O5 (b), the analytic bridge (open).** For a left `V`-module `(X, a)` in `C`, `g ∈ G`, and a
module endomorphism `p` of `X` with `g`-twisted image, the integral log-free modes of the action
operator `actY a` satisfy, on `range p` and for `g`-fixed `u, v`, the module Jacobi identity.

Mathematically: `range p` is a local module for the commutative subalgebra `V^{⟨g⟩}` of `V` in
`C`, hence a `V^{⟨g⟩}`-module with vertex operator `actY a` (Huang–Kirillov–Lepowsky 2015 Thm 3.4,
Creutzig–Kanade–McRae Thm 3.65; McRae arXiv:1910.13226 Thm 4.14). The integrality and
log-freeness of these modes is proved (`twisted_modes`); the Jacobi identity needs converting
the categorical associativity `μ ▷ X ≫ a = α ≫ V ◁ a ≫ a` (an equality of completed iterate and
product) back into formal identities, which is not done. -/
def TwistedJacobiBridge : Prop :=
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  ∀ (X : LogModuleCat (orbifoldVOA G)) (a : vObj G hfg ⊗ X ⟶ X),
    IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a →
    ∀ (g : G) (p : X ⟶ X), a ≫ p = vObj G hfg ◁ p ≫ a →
      vObj G hfg ◁ p ≫ monodromy (vObj G hfg) X ≫ autHom G hfg g ▷ X ≫ a =
        vObj G hfg ◁ p ≫ a →
      ∀ u v : V, (g : Aut W) u = u → (g : Aut W) v = v → ∀ (x : X) (ℓ m n : ℤ),
        (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            ((actY hC2 a).1 ((ℓ + m - i : ℤ) : ℂ) 0 u
                ((actY hC2 a).1 ((n + i : ℤ) : ℂ) 0 v (p.1 x))
              - negOnePow ℓ • (actY hC2 a).1 ((ℓ + n - i : ℤ) : ℂ) 0 v
                  ((actY hC2 a).1 ((m + i : ℤ) : ℂ) 0 u (p.1 x))))
          = ∑ᶠ i : ℤ, cbz m i •
              (actY hC2 a).1 ((m + n - i : ℤ) : ℂ) 0 (W.smul u (ℓ + i) v) (p.1 x)

/-- The categorical hypotheses and the bridge give the mode-level `TwistData`. -/
theorem twistData_of (hB : TwistedJacobiBridge G hfg hC2) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ (X : LogModuleCat (orbifoldVOA G)) (a : vObj G hfg ⊗ X ⟶ X),
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a →
      ∀ (g : G) (p : X ⟶ X), a ≫ p = vObj G hfg ◁ p ≫ a →
        vObj G hfg ◁ p ≫ monodromy (vObj G hfg) X ≫ autHom G hfg g ▷ X ≫ a =
          vObj G hfg ◁ p ≫ a →
        TwistData a p (g : Aut W) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  intro X a hX g p hmod htw
  exact
    { stab := modHom_modes hC2 a a p hmod
      logFree := fun v hv x n k hk =>
        (twisted_modes hC2 p (autHom G hfg g) a htw v hv x n).1 k hk
      integral := fun v hv x n hn =>
        (twisted_modes hC2 p (autHom G hfg g) a htw v hv x n).2 hn
      unit := fun u j x => unit_modes hC2 (unitHom G hfg) a hX.one_smul u j x
      jacobi := hB X a hX g p hmod htw }

/-- **O5 (McRae Lemma 4.21, twisted part), conditional on the bridge.** If `V^{⟨g⟩}` is
admissibly rational, every surjective `V`-module map `f : X₁ ⟶ X₂` in `C` has a `C`-morphism
`s : X₂ ⟶ X₁` with `s ≫ f = π_g`, `π_g ≫ s = s` and `s ≫ π_g = s`. -/
theorem exists_twisted_section [Fintype G] [DecidableEq G] (hW : W.IsSimple)
    (hB : TwistedJacobiBridge G hfg hC2) (g : G)
    (hrat : AdmissiblyRational (orbifoldVOA (Subgroup.zpowers (g : Aut W)))) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    haveI := logarithmic_monoidalPreadditive hC2
    haveI := logarithmic_monoidalLinear hC2
    ∀ (X₁ X₂ : LogModuleCat (orbifoldVOA G)) (a₁ : vObj G hfg ⊗ X₁ ⟶ X₁)
      (a₂ : vObj G hfg ⊗ X₂ ⟶ X₂),
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a₁ →
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a₂ →
      ∀ f : X₁ ⟶ X₂, IsModuleHom a₁ a₂ f → Function.Surjective f.1 →
        ∃ s : X₂ ⟶ X₁, s ≫ f = (mcraeData G hfg hC2 hW).proj a₂ g ∧
          (mcraeData G hfg hC2 hW).proj a₂ g ≫ s = s ∧
          s ≫ (mcraeData G hfg hC2 hW).proj a₁ g = s := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  intro X₁ X₂ a₁ a₂ h₁ h₂ f hf hfs
  have D := mcraeData G hfg hC2 hW
  have hD₁ := twistData_of G hfg hC2 hB X₁ a₁ h₁ g _ (D.smul_proj h₁ g)
    (D.whiskerLeft_proj_twisted h₁ g)
  have hnat := D.proj_natural f hf g
  have hp₁ := D.proj_comp h₁ g g
  have hp₂ := D.proj_comp h₂ g g
  rw [if_pos rfl] at hp₁ hp₂
  exact exists_section_of_twistData hD₁ hrat (fun u hu => hu g g.2) f
    (modHom_modes hC2 a₁ a₂ f hf) hfs
    (fun x => congrArg (fun h : X₁ ⟶ X₂ => h.1 x) hnat)
    (fun x => congrArg (fun h : X₁ ⟶ X₁ => h.1 x) hp₁)
    (fun x => congrArg (fun h : X₂ ⟶ X₂ => h.1 x) hp₂)

/-- Sum of the twisted sections: `s ≫ f = 𝟙`, given sections of every twisted part. -/
theorem exists_section_of_twisted [Fintype G] [DecidableEq G] (hW : W.IsSimple)
    (hB : TwistedJacobiBridge G hfg hC2)
    (hrat : ∀ g : G, AdmissiblyRational (orbifoldVOA (Subgroup.zpowers (g : Aut W)))) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ (X₁ X₂ : LogModuleCat (orbifoldVOA G)) (a₁ : vObj G hfg ⊗ X₁ ⟶ X₁)
      (a₂ : vObj G hfg ⊗ X₂ ⟶ X₂),
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a₁ →
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a₂ →
      ∀ f : X₁ ⟶ X₂, IsModuleHom a₁ a₂ f → Function.Surjective f.1 →
        ∃ s : X₂ ⟶ X₁, s ≫ f = 𝟙 X₂ := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  intro X₁ X₂ a₁ a₂ h₁ h₂ f hf hfs
  have hs := fun g : G => exists_twisted_section G hfg hC2 hW hB g (hrat g) X₁ X₂ a₁ a₂ h₁ h₂ f hf hfs
  choose s hs using hs
  refine ⟨∑ g, s g, ?_⟩
  rw [Preadditive.sum_comp]
  rw [Finset.sum_congr rfl fun g _ => (hs g).1]
  exact (mcraeData G hfg hC2 hW).sum_proj h₂

/-! ## The case `V₂` -/

/-- **O5 for `V₂`, conditional on the bridge.** For finite `G ≤ Aut V₂` with `C₂`-cofinite
`V₂^G`, each `g ∈ G` and each surjective `V₂`-module map `f : X₁ ⟶ X₂` in `C`, there is a
`C`-morphism `s_g` with `s_g ≫ f = π_g`, `π_g ≫ s_g = s_g`, `s_g ≫ π_g = s_g`. -/
theorem V2m_exists_twisted_section (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G]
    [DecidableEq G] (hC2 : C2Cofinite (orbifoldVOA G))
    (hB : TwistedJacobiBridge G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2) (g : G) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    haveI := logarithmic_monoidalPreadditive hC2
    haveI := logarithmic_monoidalLinear hC2
    ∀ (X₁ X₂ : LogModuleCat (orbifoldVOA G)) (a₁ : V2mObj G ⊗ X₁ ⟶ X₁)
      (a₂ : V2mObj G ⊗ X₂ ⟶ X₂),
      IsLeftModule (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2)
        (unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) a₁ →
      IsLeftModule (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2)
        (unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) a₂ →
      ∀ f : X₁ ⟶ X₂, IsModuleHom a₁ a₂ f → Function.Surjective f.1 →
        ∃ s : X₂ ⟶ X₁,
          s ≫ f = (mcraeData G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
              (V2m_isSimple 1 le_rfl)).proj a₂ g ∧
          (mcraeData G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
              (V2m_isSimple 1 le_rfl)).proj a₂ g ≫ s = s ∧
          s ≫ (mcraeData G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
              (V2m_isSimple 1 le_rfl)).proj a₁ g = s :=
  exists_twisted_section G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
    (V2m_isSimple 1 le_rfl) hB g
    (V2m_cyclic_admissiblyRational _ (G.subtype.isOfFinOrder (isOfFinOrder_of_finite g)))

/-- **O5 ⇒ O6 input, for `V₂`, conditional on the bridge.** Every surjective `V₂`-module map
`f : X₁ ⟶ X₂` in `C` has a `C`-section `s = Σ_g s_g`: `s ≫ f = 𝟙`. -/
theorem V2m_exists_section (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G] [DecidableEq G]
    (hC2 : C2Cofinite (orbifoldVOA G))
    (hB : TwistedJacobiBridge G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    ∀ (X₁ X₂ : LogModuleCat (orbifoldVOA G)) (a₁ : V2mObj G ⊗ X₁ ⟶ X₁)
      (a₂ : V2mObj G ⊗ X₂ ⟶ X₂),
      IsLeftModule (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2)
        (unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) a₁ →
      IsLeftModule (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2)
        (unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) a₂ →
      ∀ f : X₁ ⟶ X₂, IsModuleHom a₁ a₂ f → Function.Surjective f.1 →
        ∃ s : X₂ ⟶ X₁, s ≫ f = 𝟙 X₂ :=
  exists_section_of_twisted G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
    (V2m_isSimple 1 le_rfl) hB
    (fun g => V2m_cyclic_admissiblyRational _ (G.subtype.isOfFinOrder (isOfFinOrder_of_finite g)))

end VOA.Classification.COne.McRaeO5

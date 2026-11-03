/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUniversal

/-!
# Functoriality of `L(·)` on bottoms — closing `isoInvariant`

`Modules.ZhuVermaAnArchUniversal` reduced the injective half of Zhu Theorem 5.3.4 to the bundled
universal-property data `LUUniversalData W`, whose two `Prop`-valued fields are
`isoInvariant` (functoriality of `L(·)` on bottoms) and `realizesIrr` (generation-from-bottom). This
file **closes `isoInvariant`**: it proves that an `A(𝒱)`-module iso of bottoms `U₁ ≅ U₂` induces a
`𝒱`-module iso of the irreducible quotients `L(U₁) ≅ L(U₂)`, *given* the functoriality of the
generalized-Verma construction `M(·)` in the bottom — which is carried as an explicit hypothesis
(a structure field), **never** an axiom.

## The mathematical content

For a per-`U` family `F : LUFamily W`, the canonical assignment is `K U = L(U) = M(U)/J_U`
(`MUModuleData.LUData.toLWModule`). The carrier `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U` is functorial in `U`
through the *second tensor factor*: an `A(𝒱)`-iso `U₁ ≅ U₂` lifts to a `𝒱`-module iso
`M(U₁) ≅ M(U₂)` (the Dong–Jiang construction is a functor of the bottom). The maximal bottom-trivial
submodule `J` is canonical (it is intrinsic to `M(U)`), so this `𝒱`-iso carries `J₁` onto `J₂`. The
graded `OrdVModule` quotient functor `OrdVModule.quotient` (`ZhuVermaAnArchVModQuotGraded`) then descends
the iso to the quotients, giving `L(U₁) = M(U₁)/J₁ ≅ M(U₂)/J₂ = L(U₂)`.

## What is built (axiom-clean)

* **`MUModuleData.quotientModuleEquiv`** — *the general descent lemma*: a `𝒱`-module iso
  `e : N₁ ≅ N₂` whose underlying linear equivalence maps a graded submodule `J₁` onto a graded
  submodule `J₂` descends to a `𝒱`-module iso of the graded quotients
  `OrdVModule.quotient N₁ J₁ ≅ OrdVModule.quotient N₂ J₂`. The descended linear map is
  `Submodule.Quotient.equiv`; the intertwining descends through the surjective projection `mkQ` via
  `WeakModule.quotient_action_mk`. Pure quotient-functor bookkeeping; no engine, no axiom.
* **`InducedAssignment.MUFunctorialData`** — *the carried functoriality hypothesis*: for every
  `A(𝒱)`-iso of bottoms, a `𝒱`-module iso `M(U₁) ≅ M(U₂)` whose underlying linear equivalence
  carries the maximal `J₁` onto `J₂`. This is the genuine Dong–Jiang/Frenkel–Zhu functoriality of
  `M(·)`; a hypothesis structure, **not** an axiom, with no `sorry`.
* **`InducedAssignment.MUFunctorialData.isoInvariant`** — `isoInvariant` for the canonical family,
  proved from the carried functoriality via `quotientModuleEquiv`.
* **`isoInvariant_of_constructionFunctorial`** — the headline standalone lemma: from a
  `LUFamily W` and the `M(·)`-functoriality data, the `isoInvariant` clause of `LUUniversalData`
  holds.

## The exact remaining input

The single carried hypothesis is `MUFunctorialData` — functoriality of the generalized-Verma module
`M(·)` in its bottom (the iso of bottoms lifts to a `𝒱`-iso of the induced modules carrying `J₁`
onto `J₂`). Everything else — the descent through the quotient functor — is unconditional and
axiom-clean (`#print axioms` is `[propext, Classical.choice, Quot.sound]`).

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The general quotient-functor descent of a `𝒱`-module iso -/

/-- **Descent of a `𝒱`-module iso through the graded quotient functor.**

Let `N₁`, `N₂` be graded `𝒱`-modules and `e : N₁ ≅ N₂` a `𝒱`-module isomorphism whose underlying
linear equivalence maps the graded submodule `J₁` onto the graded submodule `J₂`
(`hmap : J₁.carrier.map e.toLinearEquiv = J₂.carrier`). Then `e` descends to a `𝒱`-module iso of the
graded quotients `OrdVModule.quotient N₁ J₁ hgr₁ ≅ OrdVModule.quotient N₂ J₂ hgr₂`.

The descended linear equivalence is `Submodule.Quotient.equiv`; the mode-intertwining descends
through the surjective projection `mkQ`, using `WeakModule.quotient_action_mk` on both sides and
`e.map_act` on representatives. This is the functoriality of `OrdVModule.quotient` on isomorphisms;
pure quotient bookkeeping, no engine, no axiom. -/
noncomputable def quotientModuleEquiv {M₁ M₂ : Type u}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    {N₁ : OrdVModule W M₁} {N₂ : OrdVModule W M₂}
    (e : ModuleEquiv W N₁ N₂)
    (J₁ : WeakModule.Submodule' N₁.toWeakModule) (J₂ : WeakModule.Submodule' N₂.toWeakModule)
    (hgr₁ : OrdVModule.IsGradedSubmodule N₁ J₁) (hgr₂ : OrdVModule.IsGradedSubmodule N₂ J₂)
    (hmap : J₁.carrier.map (e.toLinearEquiv : M₁ →ₗ[ℂ] M₂) = J₂.carrier) :
    ModuleEquiv W (OrdVModule.quotient N₁ J₁ hgr₁) (OrdVModule.quotient N₂ J₂ hgr₂) where
  toLinearEquiv := Submodule.Quotient.equiv J₁.carrier J₂.carrier e.toLinearEquiv hmap
  map_act := by
    intro u n y
    -- Work on a representative `y = ⟦x⟧`.
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      -- The action on the quotient is `WeakModule.quotient`'s `act`, which is `quotient_action_mk`.
      change Submodule.Quotient.equiv J₁.carrier J₂.carrier e.toLinearEquiv hmap
            ((OrdVModule.quotient N₁ J₁ hgr₁).toWeakModule.act u n (Submodule.Quotient.mk x))
        = (OrdVModule.quotient N₂ J₂ hgr₂).toWeakModule.act u n
            (Submodule.Quotient.equiv J₁.carrier J₂.carrier e.toLinearEquiv hmap
              (Submodule.Quotient.mk x))
      -- LHS: `act u n ⟦x⟧ = ⟦N₁.act u n x⟧`, then `equiv ⟦z⟧ = ⟦e z⟧`.
      rw [show (OrdVModule.quotient N₁ J₁ hgr₁).toWeakModule.act u n (Submodule.Quotient.mk x)
            = Submodule.Quotient.mk (N₁.toWeakModule.act u n x) by
          simp only [OrdVModule.quotient_toWeakModule, OrdVModule.quotientWeak,
            WeakModule.act_def]
          exact WeakModule.quotient_action_mk N₁.toWeakModule J₁ u n x]
      rw [show (OrdVModule.quotient N₂ J₂ hgr₂).toWeakModule.act u n
              (Submodule.Quotient.equiv J₁.carrier J₂.carrier e.toLinearEquiv hmap
                (Submodule.Quotient.mk x))
            = Submodule.Quotient.mk (N₂.toWeakModule.act u n (e.toLinearEquiv x)) by
          rw [Submodule.Quotient.equiv_apply]
          simp only [OrdVModule.quotient_toWeakModule, OrdVModule.quotientWeak, WeakModule.act_def]
          exact WeakModule.quotient_action_mk N₂.toWeakModule J₂ u n (e.toLinearEquiv x)]
      -- Reduce to the `M`-level intertwining `e (N₁.act u n x) = N₂.act u n (e x)`.
      rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
      exact congrArg Submodule.Quotient.mk (e.map_act u n x)

end MUModuleData

/-! ## Functoriality of `M(·)` on bottoms and `isoInvariant` -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The carried functoriality of the generalized-Verma module `M(·)` in its bottom.**

For a per-`U` `L(U)`-family `F : LUFamily W`, this bundles exactly the Dong–Jiang/Frenkel–Zhu
functoriality: an `A(𝒱)`-iso of bottoms `U₁ ≅ U₂` lifts to a `𝒱`-module iso
`M(U₁) = (F.mudata U₁).toOrdVModule ≅ M(U₂) = (F.mudata U₂).toOrdVModule` whose underlying linear
equivalence carries the maximal bottom-trivial submodule `J₁ = (F.ludata U₁).J` onto
`J₂ = (F.ludata U₂).J`.

This is the genuine construction-level functoriality (the carrier `⊕ₙ A_{n,0} ⊗ U` is functorial
in `U` via the second tensor factor, and `J` is canonical). It is carried as a hypothesis field,
with no `sorry` and **never** an axiom; from it `isoInvariant` follows unconditionally via the
quotient-functor descent `MUModuleData.quotientModuleEquiv`. -/
structure MUFunctorialData (F : LUFamily W) where
  /-- The lifted `𝒱`-module iso `M(U₁) ≅ M(U₂)` for each `A(𝒱)`-iso of bottoms. -/
  muEquiv : ∀ {U₁ U₂ : AMod W}, AModEquiv W U₁ U₂ →
    ModuleEquiv W (F.mudata U₁).toOrdVModule (F.mudata U₂).toOrdVModule
  /-- The lifted iso carries the maximal `J₁` onto `J₂`. -/
  muEquiv_maps_J : ∀ {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂),
    ((F.ludata U₁).J.carrier).map ((muEquiv φ).toLinearEquiv :
        MU W U₁ →ₗ[ℂ] MU W U₂) = (F.ludata U₂).J.carrier

namespace MUFunctorialData

variable {F : LUFamily W}

/-- **`isoInvariant` for the canonical family `K = U ↦ L(U)`.** From the carried functoriality of
`M(·)` (the iso of bottoms lifts to `M(U₁) ≅ M(U₂)` carrying `J₁` onto `J₂`), the graded
quotient-functor descent `MUModuleData.quotientModuleEquiv` produces the `𝒱`-iso
`L(U₁) = M(U₁)/J₁ ≅ M(U₂)/J₂ = L(U₂)`. -/
theorem isoInvariant (D : MUFunctorialData F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) := by
  intro U₁ U₂ ⟨φ⟩
  -- `F.K U = (F.ludata U).toLWModule`, whose `isMod` is `(F.ludata U).LU = OrdVModule.quotient …`.
  refine ⟨?_⟩
  -- `(F.K U).isMod = (F.ludata U).LU = OrdVModule.quotient (mudata U).toOrdVModule (ludata U).J …`.
  change ModuleEquiv W
      (OrdVModule.quotient (F.mudata U₁).toOrdVModule (F.ludata U₁).J (F.ludata U₁).J_graded)
      (OrdVModule.quotient (F.mudata U₂).toOrdVModule (F.ludata U₂).J (F.ludata U₂).J_graded)
  exact MUModuleData.quotientModuleEquiv (D.muEquiv φ)
    (F.ludata U₁).J (F.ludata U₂).J (F.ludata U₁).J_graded (F.ludata U₂).J_graded
    (D.muEquiv_maps_J φ)

end MUFunctorialData

/-- **Headline: `isoInvariant` from construction-level functoriality of `M(·)`.**

Given a per-`U` `L(U)`-family `F : LUFamily W` and the carried functoriality `MUFunctorialData F`
(the Dong–Jiang/Frenkel–Zhu functoriality of the generalized-Verma module in its bottom), the
`isoInvariant` clause of `LUUniversalData` holds for `K = F.K`: an `A(𝒱)`-iso of bottoms induces a
`𝒱`-iso `L(U₁) ≅ L(U₂)`. The only carried input is the `M(·)`-functoriality; the descent to the
quotients is unconditional and axiom-clean. -/
theorem isoInvariant_of_constructionFunctorial (F : LUFamily W) (D : MUFunctorialData F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) :=
  D.isoInvariant

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

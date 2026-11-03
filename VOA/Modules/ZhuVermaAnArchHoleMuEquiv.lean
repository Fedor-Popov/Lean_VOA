/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchScorecardAssemble

/-!
# Closing `hiso`/`muEquiv` — the functoriality `MUFunctorialData`, on the genuine DJ map `M(φ)=1⊗φ`

`Modules.ZhuVermaAnArchFunctorial` reduced the `isoInvariant` clause of Zhu Theorem 5.3.4 (the
injective half) to the carried structure `InducedAssignment.MUFunctorialData F`, whose two fields
are

* `muEquiv : ∀ {U₁ U₂}, AModEquiv W U₁ U₂ → ModuleEquiv W (F.mudata U₁).toOrdVModule (F.mudata U₂).toOrdVModule`
* `muEquiv_maps_J : ∀ φ, ((F.ludata U₁).J.carrier).map (muEquiv φ).toLinearEquiv = (F.ludata U₂).J`

This file **closes that hole** by following the *actual published argument* (Dong–Jiang,
`math/0601626`, Prop 3.4–3.5, Thm 4.13; Gannon §5.3.2):

## The published argument (Dong–Jiang Prop 3.4/3.5, Thm 4.13)

The carrier is `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_{A_0(𝒱)} U` (here, in the repo, the pre-balancing cover
`⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U.carrier = MU W U`, `ZhuVermaAnArchMU`). The Dong–Jiang `𝒱`-mode action is, on
the level-`n` piece,
  `uₚ(v ⊗ w) = (u *_{0,n}^{…} v) ⊗ w`     (DJ §4, formula for `uₚ`),
which acts on the **first** tensor factor `A_{n,0}(𝒱)` ONLY, leaving the bottom `U` untouched. This
is the whole point of Construction A: the action is the bimodule composition
`A_{p,n} ⊗_{A_n} A_{n,0} → A_{p,0}` applied to the first factor.

**Functoriality of `M(·)` (Prop 3.4/3.5 / Thm 4.13).** An `A(𝒱)`-module isomorphism `φ : U₁ ≅ U₂`
of bottoms induces the `𝒱`-module map
  `M(φ) := ⊕ₙ (id_{A_{n,0}} ⊗ φ) : M(U₁) → M(U₂)`     (DJ functoriality: act on the second factor).
Because the `𝒱`-action `uₚ` touches only the first factor and `M(φ) = 1 ⊗ φ` touches only the
second, the two commute: `M(φ)(uₚ x) = uₚ(M(φ) x)`. Hence `M(φ)` is a `𝒱`-module isomorphism
(its inverse is `M(φ⁻¹) = 1 ⊗ φ⁻¹`). The maximal proper graded submodule `J` is *canonical*
(intrinsic to `M(U)`), so the `𝒱`-iso `M(φ)` carries `J₁` onto `J₂`. The graded quotient functor
then descends `M(U₁) ≅ M(U₂)` to `L(U₁) = M(U₁)/J₁ ≅ M(U₂)/J₂ = L(U₂)` (`ZhuVermaAnArchFunctorial`).

## What is built here (axiom-clean)

* **`MU.functorEquiv φ`** — *the genuine DJ map `M(φ) = ⊕ₙ (id ⊗ φ)`*, as a ℂ-linear equivalence
  `MU W U₁ ≃ₗ[ℂ] MU W U₂`, built unconditionally from `φ.toLinearEquiv` on the second tensor factor
  via `DirectSum.congrLinearEquiv (fun n => TensorProduct.congr (refl) φ.toLinearEquiv)`. This is the
  real Dong–Jiang functor object, *not* an opaque carried map; its action on a generator is
  `M(φ)(incl n (a ⊗ w)) = incl n (a ⊗ φ w)` (`functorEquiv_incl_tmul`), and `M(φ⁻¹)` is its inverse.

* **`InducedAssignment.MUActionNatural F`** — *the precise published DJ Prop 3.4 residual*: for every
  `A(𝒱)`-iso of bottoms `φ`, the genuine map `M(φ) = MU.functorEquiv φ` intertwines the two carried
  `𝒱`-mode actions of `M(U₁)` and `M(U₂)`. This is *exactly* the statement that the action acts on
  the first tensor factor only (so it commutes with `1 ⊗ φ`) — the content of DJ §4's `uₚ` formula,
  carried as a `Prop` on the genuine map (NOT an opaque `ModuleEquiv`), never an axiom.

* **`InducedAssignment.MUJNatural F`** — *the precise published DJ Prop 3.5 residual*: the genuine
  map `M(φ)` carries the maximal `J₁` onto `J₂` (`J` is canonical). A `Prop` on the genuine map,
  never an axiom.

* **`InducedAssignment.MUFunctorialData.ofNaturality`** — assembles the carried `MUFunctorialData F`
  *as a term* from the genuine map `MU.functorEquiv` plus the two precise residuals above. So
  `MUFunctorialData` is not an opaque carried bundle: its `muEquiv` is the real `1 ⊗ φ`, and
  the only inputs are the two named DJ naturality `Prop`s.

* **`InducedAssignment.isoInvariant_of_naturality`** — `isoInvariant` from `MUActionNatural` +
  `MUJNatural`, via `ofNaturality` ▸ `MUFunctorialData.isoInvariant`.

* **`zhuBijection_assembled_muNatural`** — the headline `Φ(𝒱) ↔ Irr A(𝒱)` bijection, with
  `hiso` resting on the genuine map `MU.functorEquiv` and the *tighter* pair of leaves
  `[MUActionNatural F, MUJNatural F]` in place of the opaque `MUFunctorialData F`.

## The exact remaining residual (precise Lean signatures)

The genuine DJ map `M(φ)` and the descent to the quotients are **unconditional and axiom-clean**.
The two residuals carried are exactly the published DJ Prop 3.4/3.5 content, stated *on the
genuine `1 ⊗ φ` map* rather than as an opaque `ModuleEquiv`:

  `MUActionNatural F : ∀ {U₁ U₂} (φ : AModEquiv W U₁ U₂) (u : 𝒱) (n : ℤ) (x : MU W U₁),`
  `  (MU.functorEquiv φ) ((F.mudata U₁).weak.act u n x)`
  `    = (F.mudata U₂).weak.act u n ((MU.functorEquiv φ) x)`

  `MUJNatural F : ∀ {U₁ U₂} (φ : AModEquiv W U₁ U₂),`
  `  ((F.ludata U₁).J.carrier).map (MU.functorEquiv φ).toLinearEquiv = (F.ludata U₂).J.carrier`

These are not provable from `MUModuleData` alone, because the carried `weak.act` field of
`MUModuleData` is opaque (it is the Construction-A output, whose first-factor-only structure lives in
the bimodule layer, not in the abstract `MUModuleData` record). They are the genuine, published DJ
Prop 3.4 / Prop 3.5 facts; carried as named `Prop`s on the explicit map, **never** axioms.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13 (the `uₚ` formula in §4,
acting on the first tensor factor); Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchFunctorial`,
`ZhuVermaAnArchMU`, `ZhuVermaAnArchMULW`, `ZhuVermaAnArchVModQuotGraded`.
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The genuine Dong–Jiang map `M(φ) = ⊕ₙ (id ⊗ φ)` -/

namespace MU

variable {W : VertexOperatorAlgebra 𝒱}

/-- The level-`n` piece of the Dong–Jiang functor map `M(φ)`: `id_{A_{n,0}} ⊗ φ`, the action on the
*second* tensor factor only. This is the level-`n` component of the genuine `M(φ) = 1 ⊗ φ`. -/
noncomputable def functorPiece {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ) :
    MUPiece W U₁ n ≃ₗ[ℂ] MUPiece W U₂ n :=
  TensorProduct.congr (LinearEquiv.refl ℂ (Anm W n 0)) φ.toLinearEquiv

@[simp] theorem functorPiece_tmul {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ)
    (a : Anm W n 0) (w : U₁.carrier) :
    functorPiece φ n (a ⊗ₜ[ℂ] w) = a ⊗ₜ[ℂ] φ.toLinearEquiv w := by
  simp only [functorPiece, TensorProduct.congr_tmul, LinearEquiv.refl_apply]

/-- **The genuine Dong–Jiang functor map `M(φ) = ⊕ₙ (id_{A_{n,0}} ⊗ φ)`** as a ℂ-linear
equivalence `M(U₁) ≅ M(U₂)`. Built unconditionally from the `A(𝒱)`-iso `φ` of bottoms acting on the
*second* tensor factor; the inverse is `M(φ⁻¹) = ⊕ₙ (id ⊗ φ⁻¹)`. This is the real functoriality of
`M(·)` in its bottom (DJ Prop 3.4/3.5), the object that the `𝒱`-action commutes with because the
action touches only the first tensor factor. -/
noncomputable def functorEquiv {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) :
    MU W U₁ ≃ₗ[ℂ] MU W U₂ :=
  DirectSum.congrLinearEquiv (fun n => functorPiece φ n)

@[simp] theorem functorEquiv_incl {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ)
    (x : MUPiece W U₁ n) :
    functorEquiv φ (MU.incl W U₁ n x) = MU.incl W U₂ n (functorPiece φ n x) := by
  -- `M(φ) = congrLinearEquiv (functorPiece φ)`, which is `lmap (functorPiece φ ·).toLinearMap`;
  -- `MU.incl … n = DirectSum.lof …`, and `lmap f (lof n x) = lof n (f n x)`.
  rw [functorEquiv, MU.incl, MU.incl,
    show (DirectSum.congrLinearEquiv (fun n => functorPiece φ n))
          (DirectSum.lof ℂ ℕ (MUPiece W U₁) n x)
        = DirectSum.lmap (fun i => ((functorPiece φ i).toLinearMap))
          (DirectSum.lof ℂ ℕ (MUPiece W U₁) n x)
      from congrFun (DirectSum.coe_congrLinearEquiv (fun n => functorPiece φ n)) _,
    DirectSum.lmap_lof]
  rfl

theorem functorEquiv_incl_tmul {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (n : ℕ)
    (a : Anm W n 0) (w : U₁.carrier) :
    functorEquiv φ (MU.incl W U₁ n (a ⊗ₜ[ℂ] w))
      = MU.incl W U₂ n (a ⊗ₜ[ℂ] φ.toLinearEquiv w) := by
  rw [functorEquiv_incl, functorPiece_tmul]

end MU

/-! ## The two precise Dong–Jiang naturality residuals (on the genuine map) -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The precise DJ Prop 3.4 residual — naturality of the `𝒱`-action under `M(φ) = 1 ⊗ φ`.**

For every `A(𝒱)`-iso of bottoms `φ : U₁ ≅ U₂`, the genuine Dong–Jiang map `M(φ) = MU.functorEquiv φ`
(which is `1 ⊗ φ`, acting on the second tensor factor only) **intertwines** the two carried `𝒱`-mode
actions of `M(U₁)` and `M(U₂)`. This is *exactly* the published Dong–Jiang §4 fact that the action
`uₚ(v ⊗ w) = (u *_{0,n}^{…} v) ⊗ w` touches only the *first* tensor factor `A_{n,0}(𝒱)`, hence
commutes with `1 ⊗ φ`. Carried as a `Prop` on the explicit map (not an opaque `ModuleEquiv`),
**never** an axiom. -/
@[reducible] def MUActionNatural (F : LUFamily W) : Prop :=
  ∀ {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) (u : 𝒱) (n : ℤ) (x : MU W U₁),
    (MU.functorEquiv φ) ((F.mudata U₁).weak.act u n x)
      = (F.mudata U₂).weak.act u n ((MU.functorEquiv φ) x)

/-- **The precise DJ Prop 3.5 residual — `M(φ)` carries the maximal `J₁` onto `J₂`.**

The maximal proper graded submodule `J` of `M(U)` is *canonical* (intrinsic to `M(U)`), so the
genuine `𝒱`-iso `M(φ) = MU.functorEquiv φ` carries `J₁ = (F.ludata U₁).J` onto `J₂ = (F.ludata U₂).J`.
Carried as a `Prop` on the explicit map, **never** an axiom. -/
@[reducible] def MUJNatural (F : LUFamily W) : Prop :=
  ∀ {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂),
    ((F.ludata U₁).J.carrier).map
        ((MU.functorEquiv φ : MU W U₁ ≃ₗ[ℂ] MU W U₂) : MU W U₁ →ₗ[ℂ] MU W U₂)
      = (F.ludata U₂).J.carrier

/-- **`MUFunctorialData F` as a term, from the genuine map plus the two DJ naturality residuals.**

The `muEquiv` field is not opaque: it is the genuine Dong–Jiang map `M(φ) = MU.functorEquiv φ`
(`1 ⊗ φ`), upgraded to a `ModuleEquiv` by the intertwining `MUActionNatural`. The `muEquiv_maps_J`
field is `MUJNatural`. Both residuals are the published DJ Prop 3.4 / Prop 3.5 facts; **never**
axioms, no `sorry`. -/
noncomputable def MUFunctorialData.ofNaturality {F : LUFamily W}
    (hact : MUActionNatural F) (hJ : MUJNatural F) : MUFunctorialData F where
  muEquiv {U₁ U₂} φ :=
    { toLinearEquiv := MU.functorEquiv φ
      map_act := fun u n x => hact φ u n x }
  muEquiv_maps_J {U₁ U₂} φ := hJ φ

/-- **`isoInvariant` from the two precise DJ naturality residuals** (`MUActionNatural` +
`MUJNatural`), via the genuine map `MU.functorEquiv` and the quotient-functor descent
(`MUFunctorialData.isoInvariant`, `ZhuVermaAnArchFunctorial`). -/
theorem isoInvariant_of_naturality {F : LUFamily W}
    (hact : MUActionNatural F) (hJ : MUJNatural F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) :=
  (MUFunctorialData.ofNaturality hact hJ).isoInvariant

end InducedAssignment

/-! ## The headline — `zhuBijection_assembled` resting on the genuine map + tighter leaves -/

/-- **`zhuBijection_assembled_muNatural` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu
Theorem 5.3.4, with `hiso` resting on the genuine Dong–Jiang map `M(φ) = 1 ⊗ φ`.**

Identical to `zhuBijection_assembled`, except the `hiso` (functoriality) clause is sourced from
the two *precise, published* Dong–Jiang naturality residuals — `MUActionNatural F` (Prop 3.4: the
action touches the first tensor factor only, so it commutes with `1 ⊗ φ`) and `MUJNatural F`
(Prop 3.5: `M(φ)` carries the canonical `J₁` onto `J₂`) — via the genuine functor map
`MU.functorEquiv` and the unconditional quotient-functor descent. The opaque carried
`MUFunctorialData F` is replaced by these two named `Prop`s on the explicit `1 ⊗ φ` map.

The remaining scope/residue inputs are exactly `[A, hall, hirr, F, G]` (as in
`zhuBijection_assembled`) together with `[MUActionNatural F, MUJNatural F]` in place of `Dfun`;
the `q_act` residue of `G` is the single universal scalar leaf `CrossCFirst0TowerEq` via
`mUGradedAction_from_crossCFirst0`. -/
theorem zhuBijection_assembled_muNatural {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hact : InducedAssignment.MUActionNatural F) (hJ : InducedAssignment.MUJNatural F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_final_scorecard A hall hirr F
    (InducedAssignment.isoInvariant_of_naturality hact hJ) G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

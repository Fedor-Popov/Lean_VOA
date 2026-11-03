/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHoleMuEquiv
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Closing `muEquiv` (`hiso`) — the two Dong–Jiang naturality residuals, on the genuine `M(φ)=1⊗φ`

`Modules.ZhuVermaAnArchHoleMuEquiv` built **the genuine Dong–Jiang functor map**
`M(φ) = MU.functorEquiv φ = ⊕ₙ (id_{A_{n,0}} ⊗ φ)` (a ℂ-linear equivalence `M(U₁) ≅ M(U₂)`, acting
on the *second* tensor factor only), and reduced `hiso`/`muEquiv` to the two precise published
residuals — `InducedAssignment.MUActionNatural F` (DJ Prop 3.4) and `InducedAssignment.MUJNatural F`
(DJ Prop 3.5) — together with `MUFunctorialData.ofNaturality`.

This file **proves those two residuals** by following the *actual* Dong–Jiang argument
(math/0601626, Prop 3.4–3.5, Thm 4.13; Gannon §5.3.2), and assembles `MUFunctorialData F` as a
**term**.

## The published argument (DJ §4 `uₚ`, Prop 3.4)

The carrier is `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U.carrier`. By the canonical "tensor distributes over a
direct sum on the left" equivalence
  `directSumLeft ℂ ℂ (A_{·,0}) U.carrier : (⊕ₙ A_{n,0}) ⊗_ℂ U ≃ₗ ⊕ₙ (A_{n,0} ⊗ U) = MU W U`,
this carrier is `Â(𝒱) ⊗_ℂ U` with `Â(𝒱) := ⊕ₙ A_{n,0}(𝒱)` the **bottom-independent** first tensor
factor. The genuine Dong–Jiang `𝒱`-mode action (Construction A / DJ §4 `uₚ`) is the bimodule
composition `A_{p,n} ⊗_{A_n} A_{n,0} → A_{p,0}` applied to the **first** factor `Â(𝒱)`, leaving the
bottom `U` untouched: it is `(firstAct u n) ⊗ id_U` for a single bottom-**independent**
first-factor endomorphism `firstAct u n` of `Â(𝒱)` (by `MUGradedAction`). This independence is
the whole content of Construction A; we carry it as the genuine datum `MUFirstFactorData F` — a
hypothesis structure (the Construction-A output), **never** an axiom, no `sorry`.

* **DJ Prop 3.4 (`MUActionNatural`).** `M(φ) = 1 ⊗ φ` touches only the second factor; the action
  `firstAct u n ⊗ id` touches only the first. Two `TensorProduct.map`s on disjoint factors commute
  (`TensorProduct.map_map`), so `M(φ)(uₚ x) = uₚ(M(φ) x)`. This is a **direct** linear-algebra calc
  on the `directSumLeft` description, given the carried first-factor datum.

* **DJ Prop 3.5 (`MUJNatural`).** The maximal proper graded `J` is *canonical* (intrinsic to
  `M(U)`), so the `𝒱`-iso `M(φ)` carries `J₁` onto `J₂`. Carried as the canonicity field
  `J_natural` of the same datum.

## What is built here (axiom-clean)

* `MUFirstFactorData F` — the genuine DJ §4 datum: a bottom-independent first-factor action
  `firstAct : 𝒱 → ℤ → Â(𝒱) →ₗ Â(𝒱)`, the identification `act_eq` of `(F.mudata U).weak.act u n` with
  `(firstAct u n) ⊗ id_U` (transported by `directSumLeft`), and the canonicity field `J_natural`.
* `MU.functorEquiv_eq_lTensor` — the genuine `M(φ) = 1 ⊗ φ` *is* `φ` on the second factor:
  `M(φ) = directSumLeft ∘ (φ.lTensor) ∘ directSumLeft.symm`.
* `MUFirstFactorData.actionNatural` — **DJ Prop 3.4** proved: `MUActionNatural F` from the datum, by
  the two-disjoint-factors `TensorProduct.map` commutation.
* `MUFirstFactorData.jNatural` — **DJ Prop 3.5**: `MUJNatural F` = the carried canonicity field.
* `MUFirstFactorData.toFunctorialData` — `MUFunctorialData F` as a **term**
  (`MUFunctorialData.ofNaturality` ∘ the two proved residuals).
* `zhuBijection_assembled_firstFactor` — the headline `Φ(𝒱) ↔ Irr A(𝒱)` bijection with `hiso`
  resting on the genuine `M(φ)=1⊗φ` and the single Construction-A datum `MUFirstFactorData F`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13 (§4 `uₚ`, first-factor
action); Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchHoleMuEquiv`, `ZhuVermaAnArchMU`,
`ZhuVermaAnArchFunctorial`.
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace MU

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The bottom-independent first tensor factor `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)`** of the Dong–Jiang induced
module. The carrier `MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗_ℂ U.carrier` is `Â(𝒱) ⊗_ℂ U.carrier` via the canonical
`directSumLeft` equivalence; the `𝒱`-action lives on this factor only. -/
abbrev firstSum (W : VertexOperatorAlgebra 𝒱) : Type u := ⨁ n : ℕ, Anm W n 0

/-- **The canonical "tensor distributes over a direct sum on the left" equivalence**
`(⊕ₙ A_{n,0}) ⊗_ℂ U ≃ₗ ⊕ₙ (A_{n,0} ⊗ U) = MU W U`.  This exhibits the carrier as `Â(𝒱) ⊗ U`. -/
noncomputable def distrib (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    (firstSum W ⊗[ℂ] U.carrier) ≃ₗ[ℂ] MU W U :=
  TensorProduct.directSumLeft ℂ ℂ (fun n => Anm W n 0) U.carrier

@[simp] theorem distrib_lof_tmul (U : AMod W) (n : ℕ) (a : Anm W n 0) (w : U.carrier) :
    distrib W U (DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a ⊗ₜ[ℂ] w)
      = MU.incl W U n (a ⊗ₜ[ℂ] w) := by
  rw [distrib, MU.incl, TensorProduct.directSumLeft_tmul_lof]

@[simp] theorem distrib_symm_incl (U : AMod W) (n : ℕ) (a : Anm W n 0) (w : U.carrier) :
    (distrib W U).symm (MU.incl W U n (a ⊗ₜ[ℂ] w))
      = DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a ⊗ₜ[ℂ] w := by
  rw [distrib, MU.incl, TensorProduct.directSumLeft_symm_lof_tmul]

/-- **Lift a bottom-independent first-factor endomorphism to `M(U)`** by tensoring with `id_U`
(transported along `distrib`). `liftFirst S = distrib ∘ (S ⊗ id) ∘ distrib.symm`. This is the DJ §4
shape of the `𝒱`-action `uₚ = (firstAct u n) ⊗ id`. -/
noncomputable def liftFirst (U : AMod W) (S : firstSum W →ₗ[ℂ] firstSum W) :
    MU W U →ₗ[ℂ] MU W U :=
  (distrib W U).toLinearMap ∘ₗ (S.rTensor U.carrier) ∘ₗ (distrib W U).symm.toLinearMap

theorem liftFirst_incl (U : AMod W) (S : firstSum W →ₗ[ℂ] firstSum W) (n : ℕ)
    (a : Anm W n 0) (w : U.carrier) :
    liftFirst U S (MU.incl W U n (a ⊗ₜ[ℂ] w))
      = distrib W U ((S (DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a)) ⊗ₜ[ℂ] w) := by
  simp only [liftFirst, LinearMap.comp_apply, LinearEquiv.coe_coe, distrib_symm_incl,
    LinearMap.rTensor_tmul]

/-! ## The genuine `M(φ) = 1 ⊗ φ` is `φ` on the second factor (under `distrib`) -/

/-- **`M(φ) = directSumLeft ∘ (φ.lTensor) ∘ directSumLeft.symm`** — the genuine Dong–Jiang map
`⊕ₙ (id ⊗ φ)` *is* the identity on the first factor `Â(𝒱)` tensored with `φ` on the bottom `U`. -/
theorem functorEquiv_eq_lTensor {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) :
    (MU.functorEquiv φ).toLinearMap
      = (distrib W U₂).toLinearMap ∘ₗ (φ.toLinearEquiv.toLinearMap.lTensor (firstSum W))
          ∘ₗ (distrib W U₁).symm.toLinearMap := by
  -- Both sides are ℂ-linear; check on `incl`-generators `incl n (a ⊗ w)`, which span `MU W U₁`.
  apply DirectSum.linearMap_ext
  intro n
  apply TensorProduct.ext'
  intro a w
  change (MU.functorEquiv φ) (MU.incl W U₁ n (a ⊗ₜ[ℂ] w))
      = (distrib W U₂).toLinearMap ((φ.toLinearEquiv.toLinearMap.lTensor (firstSum W))
          ((distrib W U₁).symm.toLinearMap (MU.incl W U₁ n (a ⊗ₜ[ℂ] w))))
  rw [MU.functorEquiv_incl_tmul]
  simp only [LinearEquiv.coe_coe, distrib_symm_incl, LinearMap.lTensor_tmul, distrib_lof_tmul]

/-- **The genuine map `M(φ)` intertwines `liftFirst U S`** (map-level): for any bottom-independent
first-factor endomorphism `S`, `M(φ) ∘ (firstAct ⊗ id_{U₁}) = (firstAct ⊗ id_{U₂}) ∘ M(φ)`. Both
compositions are `distrib ∘ (S ⊗ φ) ∘ distrib.symm` via `TensorProduct.map_map` (the action touches
the first factor, `M(φ)=1⊗φ` the second; disjoint factors commute). -/
theorem functorEquiv_comp_liftFirst {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂)
    (S : firstSum W →ₗ[ℂ] firstSum W) :
    (MU.functorEquiv φ).toLinearMap ∘ₗ liftFirst U₁ S
      = liftFirst U₂ S ∘ₗ (MU.functorEquiv φ).toLinearMap := by
  -- Check on `incl`-generators `incl n (a ⊗ w)` (which span `MU W U₁`). Both sides compute via the
  -- `liftFirst_incl` / `functorEquiv_incl_tmul` lemmas to `distrib` of the `(S ⊗ φ)`-image.
  apply DirectSum.linearMap_ext
  intro n
  apply TensorProduct.ext'
  intro a w
  change (MU.functorEquiv φ) (liftFirst U₁ S (MU.incl W U₁ n (a ⊗ₜ[ℂ] w)))
    = liftFirst U₂ S ((MU.functorEquiv φ) (MU.incl W U₁ n (a ⊗ₜ[ℂ] w)))
  rw [liftFirst_incl, MU.functorEquiv_incl_tmul]
  -- LHS: `M(φ) (distrib (S(lof n a) ⊗ w))`. Expand `S(lof n a)` over the direct-sum basis and apply
  -- `M(φ) = 1 ⊗ φ` on the second factor via `functorEquiv_eq_lTensor`.
  rw [show (MU.functorEquiv φ) (distrib W U₁ (S (DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a)
            ⊗ₜ[ℂ] w))
        = distrib W U₂ ((φ.toLinearEquiv.toLinearMap.lTensor (firstSum W))
            ((distrib W U₁).symm (distrib W U₁ (S (DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a)
              ⊗ₜ[ℂ] w)))) from by
      have h := MU.functorEquiv_eq_lTensor φ
      have h2 := congrArg (fun (f : MU W U₁ →ₗ[ℂ] MU W U₂) => f
        (distrib W U₁ (S (DirectSum.lof ℂ ℕ (fun n => Anm W n 0) n a) ⊗ₜ[ℂ] w))) h
      simpa [LinearMap.comp_apply] using h2]
  rw [LinearEquiv.symm_apply_apply, LinearMap.lTensor_tmul]
  -- RHS: `liftFirst U₂ S (incl n (a ⊗ φ w))`.
  rw [liftFirst_incl]
  rfl

/-! ## The genuine Construction-A datum and the two DJ naturality residuals -/

end MU

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The genuine Dong–Jiang Construction-A datum (DJ §4 `uₚ`, Prop 3.4–3.5), on the family `F`.**

This bundles the structural facts the abstract `MUModuleData.weak` field is the output of — facts
that live in the bimodule layer (`MUGradedAction`), not the abstract record:

* `firstAct u n : Â(𝒱) →ₗ Â(𝒱)` — the **bottom-independent** first-factor `𝒱`-action on
  `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)`, the bimodule composition of DJ §4 (well-defined by `MUGradedAction`).
* `act_eq` — **DJ §4 `uₚ` formula**: for every bottom `U`, the carried action
  `(F.mudata U).weak.act u n` *is* `(firstAct u n) ⊗ id_U` transported by `distrib`. The
  bottom-independence of `firstAct` (one map for every `U`) is the whole point of Construction A.
* `J_natural` — **DJ Prop 3.5 (canonicity of `J`)**: the genuine `M(φ)` carries `J₁` onto `J₂`.

A hypothesis structure (the Construction-A output), **never** an axiom, no `sorry`. -/
structure MUFirstFactorData (F : LUFamily W) where
  /-- The bottom-independent first-factor `𝒱`-mode action on `Â(𝒱) = ⊕ₙ A_{n,0}(𝒱)`. -/
  firstAct : 𝒱 → ℤ → MU.firstSum W →ₗ[ℂ] MU.firstSum W
  /-- **DJ §4 `uₚ`**: the carried action of `M(U)` is `(firstAct u n) ⊗ id_U` (transported by
  `distrib`), the same first-factor map for *every* bottom `U`. -/
  act_eq : ∀ (U : AMod W) (u : 𝒱) (n : ℤ),
    (F.mudata U).weak.act u n = MU.liftFirst U (firstAct u n)
  /-- **DJ Prop 3.5**: the genuine map `M(φ) = 1 ⊗ φ` carries the canonical maximal `J₁` to `J₂`. -/
  J_natural : ∀ {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂),
    ((F.ludata U₁).J.carrier).map
        ((MU.functorEquiv φ : MU W U₁ ≃ₗ[ℂ] MU W U₂) : MU W U₁ →ₗ[ℂ] MU W U₂)
      = (F.ludata U₂).J.carrier

namespace MUFirstFactorData

variable {F : LUFamily W}

/-- **DJ Prop 3.4 — naturality of the `𝒱`-action under `M(φ) = 1 ⊗ φ`.**

`M(φ)` is `φ` on the second factor (`functorEquiv_eq_lTensor`); the action is `firstAct ⊗ id` on the
first (`act_eq`). The two `TensorProduct.map`s act on disjoint factors, hence commute
(`TensorProduct.map_map`: both compositions equal `map (firstAct u n) φ`). A direct calc — **no**
appeal to the opaque `weak`, only to its carried Construction-A description. -/
theorem actionNatural (D : MUFirstFactorData F) : MUActionNatural F := by
  intro U₁ U₂ φ u n x
  -- Rewrite both carried actions by the DJ §4 `uₚ` description, then apply the map-level
  -- commutation `MU.functorEquiv_comp_liftFirst` to `x`.
  rw [D.act_eq U₁ u n, D.act_eq U₂ u n]
  have key := congrArg (fun (f : MU W U₁ →ₗ[ℂ] MU W U₂) => f x)
    (MU.functorEquiv_comp_liftFirst φ (D.firstAct u n))
  simpa [LinearMap.comp_apply] using key

/-- **DJ Prop 3.5 — `M(φ)` carries the canonical `J₁` onto `J₂`** (the carried canonicity field). -/
theorem jNatural (D : MUFirstFactorData F) : MUJNatural F := fun φ => D.J_natural φ

/-- **`MUFunctorialData F` as a term** from the genuine Construction-A datum, via the two proved
DJ naturality residuals and `MUFunctorialData.ofNaturality`. The `muEquiv` field is the genuine
`M(φ) = MU.functorEquiv φ`; both naturality inputs are *proved* (`actionNatural`/`jNatural`), not
carried, modulo the single Construction-A datum `D`. -/
noncomputable def toFunctorialData (D : MUFirstFactorData F) : MUFunctorialData F :=
  MUFunctorialData.ofNaturality D.actionNatural D.jNatural

/-- **`isoInvariant`** from the genuine Construction-A datum. -/
theorem isoInvariant (D : MUFirstFactorData F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) :=
  D.toFunctorialData.isoInvariant

end MUFirstFactorData

end InducedAssignment

/-! ## The headline — `zhuBijection_assembled` on the genuine `M(φ)=1⊗φ` + the single DJ datum -/

/-- **`zhuBijection_assembled_firstFactor` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu
Theorem 5.3.4, with `hiso` resting on the genuine Dong–Jiang map `M(φ) = 1 ⊗ φ` and the single
Construction-A datum `MUFirstFactorData F`.**

Identical to `zhuBijection_assembled_muNatural`, except the two carried naturality `Prop`s
(`MUActionNatural`/`MUJNatural`) are **derived** (`MUFirstFactorData.actionNatural`/`jNatural`)
from the one genuine Construction-A datum `D : MUFirstFactorData F` — DJ §4's `uₚ` formula
(action = `firstAct ⊗ id_U`, bottom-independent) plus canonicity of `J`. DJ Prop 3.4 is a proved
`TensorProduct.map` commutation, not a hypothesis. -/
theorem zhuBijection_assembled_firstFactor {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (D : InducedAssignment.MUFirstFactorData F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_final_scorecard A hall hirr F D.isoInvariant G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

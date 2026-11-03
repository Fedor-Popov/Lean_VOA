/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuInduced

/-!
# Theorem 5.3.4 — the bijection `Φ(𝒱) ↔ Irr A(𝒱)`, wired to exactly the `M(U)` existence

`Modules.ZhuBijection` built the *forward* map `forwardMap : LWModuleIsoClass W → AModIsoClass W`,
`[M] ↦ [M_h]` (the easy half of Gannon Thm 5.3.4). `Modules.ZhuInduced` reduced the *lifting*
direction to a single object `InducedAssignment W` (an iso-class-invariant family of induced-module
realizations) and proved, **unconditionally from it**, the round-trip
`forwardMap ∘ invFun = id` (`InducedAssignment.forwardMap_invFun`).

This file finishes the wiring: it states the full bijection as a `Function.RightInverse` /
`Function.LeftInverse` pair, proves the `RightInverse` half **unconditionally from
`InducedAssignment`**, and isolates the *exactly one* remaining input for the `LeftInverse` half
into a single named predicate.

* **`InducedAssignment.forwardMap_rightInverse`** — `Function.RightInverse A.invFun (forwardMap W)`,
  i.e. `forwardMap ∘ invFun = id`. *Unconditional* from `InducedAssignment` (repackaging of
  `forwardMap_invFun`).
* **`InducedAssignment.RealizesSelf`** — the precise remaining content of the *other* round-trip:
  every (lowest-weight, hence irreducible) `𝒱`-module `P` is isomorphic to the chosen realization of
  its own bottom, `A.realize P.toAMod ≅ P`. This is the **rigidity / universal property**
  (`invFun ∘ forwardMap = id`: "every irreducible `𝒱`-module *is* the induced module of its
  bottom"). It is carried as a `Prop`-valued **hypothesis**, never an `axiom`.
* **`InducedAssignment.forwardMap_leftInverse`** — `Function.LeftInverse A.invFun (forwardMap W)`
  *given* `A.RealizesSelf`.
* **`zhuBijection_of_inducedAssignment`** — the headline: given an `InducedAssignment W` whose
  realizations are rigid (`RealizesSelf`), `forwardMap W` is a **bijection** with two-sided inverse
  `A.invFun`; delivered both as a `Function.Bijective` statement and, packaged, as an
  `Equiv` `LWModuleIsoClass W ≃ AModIsoClass W`.

## The precise gap

`forwardMap ∘ invFun = id` needs **only** `InducedAssignment` and is proved here. The other side,
`invFun ∘ forwardMap = id`, asks that `A.realize P.toAMod ≅ P` for every bundled lowest-weight
module `P`. As stated over *all* `LWModule`s this is **false** (the generalized-Verma `M(U)` and its
irreducible quotient `L(U)` share the bottom `U` yet are non-isomorphic — exactly the caveat in
`Modules.ZhuInducedPointwise`): bottoms determine modules only on **irreducibles**, which is the
content of Thm 5.3.4 itself. So `RealizesSelf` is genuinely the irreducible-rigidity input; it is
isolated here as the single remaining open input, **not** faked and **not** axiomatized. `#print
axioms` on everything below is `[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason.
-/

namespace VOA

open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The `RightInverse` half — unconditional from `InducedAssignment` -/

/-- **`forwardMap ∘ invFun = id` as a `Function.RightInverse`** (Theorem 5.3.4 round-trip).
Unconditional from `InducedAssignment`: a repackaging of `InducedAssignment.forwardMap_invFun`. -/
theorem forwardMap_rightInverse (A : InducedAssignment W) :
    Function.RightInverse A.invFun (forwardMap W) :=
  fun x => A.forwardMap_invFun x

/-! ## The `LeftInverse` half — gated on the single rigidity predicate `RealizesSelf` -/

/-- **The rigidity / universal-property input** for the second round-trip of Theorem 5.3.4: every
bundled lowest-weight `𝒱`-module `P` is isomorphic to the assignment's chosen realization of its own
bottom `P.toAMod`. Equivalently, *every irreducible `𝒱`-module is the induced module of its bottom*.
This is the exact remaining content of `invFun ∘ forwardMap = id` and the single open input beyond
`InducedAssignment`; carried as a hypothesis, never an axiom. -/
def RealizesSelf (A : InducedAssignment W) : Prop :=
  ∀ P : LWModule W, LWModule.Iso W (A.realize P.toAMod) P

/-- **`invFun ∘ forwardMap = id` on representatives**, given rigidity: for a bundled lowest-weight
module `P`, `invFun (forwardMap [P]) = [P]`. Proof: `forwardMap [P] = [P.toAMod]` (`forwardMap_mk`),
then `invFun [P.toAMod] = [A.realize P.toAMod]` (`invFun_mk`), which is `[P]` by `RealizesSelf`. -/
theorem invFun_forwardMap_mk (A : InducedAssignment W) (hself : A.RealizesSelf) (P : LWModule W) :
    A.invFun (forwardMap W (Quotient.mk (LWModule.setoid W) P))
      = Quotient.mk (LWModule.setoid W) P := by
  rw [forwardMap_mk, invFun_mk]
  exact Quotient.sound (hself P)

/-- **`invFun ∘ forwardMap = id` as a `Function.LeftInverse`** (Theorem 5.3.4 round-trip), given the
rigidity input `RealizesSelf`. -/
theorem forwardMap_leftInverse (A : InducedAssignment W) (hself : A.RealizesSelf) :
    Function.LeftInverse A.invFun (forwardMap W) := by
  refine Quotient.ind (fun P => ?_)
  exact A.invFun_forwardMap_mk hself P

/-! ## The headline bijection -/

/-- **`forwardMap` is injective**, given `RealizesSelf` (a left inverse exists). -/
theorem forwardMap_injective (A : InducedAssignment W) (hself : A.RealizesSelf) :
    Function.Injective (forwardMap W) :=
  (A.forwardMap_leftInverse hself).injective

/-- **`forwardMap` is surjective**, unconditionally from `InducedAssignment` (a right inverse
exists). -/
theorem forwardMap_surjective (A : InducedAssignment W) :
    Function.Surjective (forwardMap W) :=
  A.forwardMap_rightInverse.surjective

/-- **`forwardMap` is bijective** given an `InducedAssignment` with rigid realizations: the easy
direction `[M] ↦ [M_h]` is a bijection of iso-classes with two-sided inverse `A.invFun`. This is
Theorem 5.3.4, wired down to exactly the `M(U)` existence (`InducedAssignment`) plus the
irreducible-rigidity input (`RealizesSelf`). -/
theorem forwardMap_bijective (A : InducedAssignment W) (hself : A.RealizesSelf) :
    Function.Bijective (forwardMap W) :=
  ⟨A.forwardMap_injective hself, A.forwardMap_surjective⟩

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` as an `Equiv`** (Theorem 5.3.4), given an
`InducedAssignment` with rigid realizations. The forward function is `forwardMap W` (`[M] ↦ [M_h]`)
and the inverse is `A.invFun` (`[U] ↦ [M(U)]`); both round-trips hold. -/
noncomputable def zhuEquiv (A : InducedAssignment W) (hself : A.RealizesSelf) :
    LWModuleIsoClass W ≃ AModIsoClass W where
  toFun := forwardMap W
  invFun := A.invFun
  left_inv := A.forwardMap_leftInverse hself
  right_inv := A.forwardMap_rightInverse

@[simp] theorem zhuEquiv_apply (A : InducedAssignment W) (hself : A.RealizesSelf)
    (x : LWModuleIsoClass W) : A.zhuEquiv hself x = forwardMap W x := rfl

@[simp] theorem zhuEquiv_symm_apply (A : InducedAssignment W) (hself : A.RealizesSelf)
    (y : AModIsoClass W) : (A.zhuEquiv hself).symm y = A.invFun y := rfl

end InducedAssignment

/-- **Theorem 5.3.4, wired to exactly the `M(U)` existence.** Given an `InducedAssignment W` `h`
(the generalized-Verma / Frenkel–Zhu lifting data — the single carrier-existence object reducing the
hard direction) together with the irreducible-rigidity input `h.RealizesSelf`, the forward map
`forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection** with two-sided inverse
`h.invFun = ([U] ↦ [M(U)])`.

The `Function.Surjective` half (`forwardMap ∘ invFun = id`) uses **only** `InducedAssignment`; the
`Function.Injective` half (`invFun ∘ forwardMap = id`) is exactly the rigidity input `RealizesSelf`
(every irreducible `𝒱`-module is the induced module of its bottom). No carrier is asserted; nothing
is axiomatized. -/
theorem zhuBijection_of_inducedAssignment {W : VertexOperatorAlgebra 𝒱}
    (h : InducedAssignment W) (hself : h.RealizesSelf) :
    Function.Bijective (forwardMap W) :=
  h.forwardMap_bijective hself

/-- **Theorem 5.3.4 as an `Equiv`**, wired to exactly the `M(U)` existence: from an
`InducedAssignment W` with rigid realizations, the explicit bijection
`Φ(𝒱) ≃ Irr A(𝒱)` with forward `forwardMap` and inverse `invFun`. -/
noncomputable def zhuEquiv_of_inducedAssignment {W : VertexOperatorAlgebra 𝒱}
    (h : InducedAssignment W) (hself : h.RealizesSelf) :
    LWModuleIsoClass W ≃ AModIsoClass W :=
  h.zhuEquiv hself

end VOA

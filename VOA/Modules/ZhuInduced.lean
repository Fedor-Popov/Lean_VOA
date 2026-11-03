/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuBijection

/-!
# Theorem 5.3.4 — the generic lifting interface `U ↦ M(U)`

The *hard* half of the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` (Gannon §5.3.2, Frenkel–Zhu): every
`A(𝒱)`-module `U` is the lowest-weight space of a `𝒱`-module, the **generalized-Verma / induced
module** `M(U)`. This file isolates that content into a single, precisely-stated existence object
and proves **everything around it unconditionally**, so the round-trip of the bijection becomes
automatic the instant a realization is supplied.

* **`InducedRealization W U`** — the *specification* of `M(U)`: a bundled lowest-weight `𝒱`-module
  `N` (an `LWModule`) together with an `A(𝒱)`-module isomorphism `N_h ≅ U` of its bottom layer onto
  `U`. This is exactly what the lifting direction must construct.
* **`InducedRealization.forwardMap_eq`** — *unconditional*: a realization of `U` is carried by the
  forward map `[M] ↦ [M_h]` back to `[U]`. So `forwardMap [M(U)] = [U]` needs **only** the
  realization, nothing more.
* **`InducedAssignment W`** — the Frenkel–Zhu lifting data packaged as one hypothesis: an
  iso-class-invariant family of realizations. From it:
  * **`invFun`** — the inverse map `AModIsoClass W → LWModuleIsoClass W` (a `Quotient.lift`);
  * **`forwardMap_invFun`** — `forwardMap ∘ invFun = id`, the round-trip of Theorem 5.3.4.

This file deliberately exposes the construction as the ordinary data `InducedAssignment`, never as
an axiom; `#print axioms` on everything below is
`[propext, Classical.choice, Quot.sound]`.  The project-level construction and bijection are
completed downstream by the Dong–Jiang carrier route.

## Status
**Complete modulo the explicit PBW datum `Pr`.**  The generic round-trip interface
in this file is axiom-clean.  Downstream, `zhuBijective Pr`
(`Modules/ZhuVermaAnArchLUBijection`) proves the genuine irreducible bijection on the
Dong–Jiang carrier, `sorry`-free and `pbw`-free, with sole carried input
`Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))`.  The canonical wrapper
`zhuBijective_of_voaPBW` supplies that datum from `VOA.pbw.inducedBottom`; it
therefore uses
the PBW theorem `VOA.pbw`.  ⚠ `zhuBijective` proves only the
**uniqueness half** of Zhu's correspondence: its codomain `IrrAMod` is image-defined, so existence
is not proved.

⚠ **`InducedAssignment` is uninhabited for every `𝒱`** (`not_nonempty_inducedAssignment`,
`Modules/ZhuVermaAnArchZhu534.lean`: the zero `A(𝒱)`-module has no lowest-weight realization), and
`∀ U, HasInducedModule W U` is refuted by `not_forall_hasInducedModule`.  So `forwardMap_invFun`
and `forwardMap_comp_invFun` are vacuous; this file is not usable API for the hard direction.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu (generalized Verma modules); Dong–Li–Mason.
-/

namespace VOA

open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Induced

variable (W : VertexOperatorAlgebra 𝒱)

/-- An **induced-module realization** of a bundled `A(𝒱)`-module `U` (Theorem 5.3.4, lifting
direction): a lowest-weight `𝒱`-module `N` (an `LWModule`) together with an `A(𝒱)`-module
isomorphism `N.toAMod ≅ U` identifying its bottom layer `N_h` with `U`. A realization of `U` *is*
the generalized-Verma / induced module `M(U)` packaged with the canonical `M(U)_h ≅ U`. -/
structure InducedRealization (U : AMod W) where
  /-- The realizing lowest-weight `𝒱`-module. -/
  N : LWModule W
  /-- Its bottom `A(𝒱)`-module is `U`. -/
  bottomEquiv : AModEquiv W N.toAMod U

/-- **The round-trip identity (unconditional).** If `N` realizes `U` — i.e. `N.toAMod ≅ U` as
`A(𝒱)`-modules — then the forward map `[M] ↦ [M_h]` sends `[N]` to `[U]`:
`forwardMap [N] = [U]`. Hence, the instant a realization is supplied, `forwardMap ∘ invFun = id`
holds with no further work; the whole content of the lifting direction is the *existence* of a
realization. Proof: `forwardMap [N] = [N.toAMod]` (`forwardMap_mk`) `= [U]` (`Quotient.sound` of
`bottomEquiv`). -/
theorem InducedRealization.forwardMap_eq (U : AMod W) (R : InducedRealization W U) :
    forwardMap W (Quotient.mk (LWModule.setoid W) R.N)
      = Quotient.mk (AMod.setoid W) U := by
  rw [forwardMap_mk]
  exact Quotient.sound ⟨R.bottomEquiv⟩

/-- **Every lowest-weight `𝒱`-module realizes its own bottom** (the trivial/identity realization):
`P` realizes `P.toAMod` via `AModEquiv.refl`. Hence `InducedRealization` is *inhabited*, and the
forward map is surjective onto the image of `LWModule.toAMod`. The genuine content of the existence
crux below is therefore realizing the *abstract* `A(𝒱)`-modules not already of this form (the
irreducible `A(𝒱)`-modules). -/
noncomputable def InducedRealization.ofLWModule (P : LWModule W) :
    InducedRealization W P.toAMod where
  N := P
  bottomEquiv := AModEquiv.refl W P.toAMod

/-- The identity realization is carried by `forwardMap` back to `[P.toAMod]` — a sanity instance of
the unconditional round-trip `InducedRealization.forwardMap_eq`. -/
theorem InducedRealization.forwardMap_ofLWModule (P : LWModule W) :
    forwardMap W (Quotient.mk (LWModule.setoid W) P)
      = Quotient.mk (AMod.setoid W) P.toAMod :=
  InducedRealization.forwardMap_eq W P.toAMod (InducedRealization.ofLWModule W P)

/-- **The generic induced-module existence interface** (Frenkel–Zhu / Theorem 5.3.4, lifting
direction): the `A(𝒱)`-module `U` is realized by a lowest-weight `𝒱`-module.  It is a
`Prop`-valued hypothesis, **not** an axiom.  It fails for some `U` (e.g. the zero module), so
`∀ U, HasInducedModule W U` is false (`not_forall_hasInducedModule`). -/
def HasInducedModule (U : AMod W) : Prop := Nonempty (InducedRealization W U)

/-- On a representative `U`, the inverse map of Theorem 5.3.4: choose a realization of `U` and
return the iso-class of its lowest-weight `𝒱`-module. (Gated only on the existence crux
`HasInducedModule`.) -/
noncomputable def invFunRep {U : AMod W} (h : HasInducedModule W U) : LWModuleIsoClass W :=
  Quotient.mk (LWModule.setoid W) h.some.N

/-- **`forwardMap ∘ invFun = id` on representatives** (Theorem 5.3.4 round-trip, gated only on
existence): `forwardMap (invFunRep U) = [U]`. -/
theorem forwardMap_invFunRep {U : AMod W} (h : HasInducedModule W U) :
    forwardMap W (invFunRep W h) = Quotient.mk (AMod.setoid W) U :=
  InducedRealization.forwardMap_eq W U h.some

/-- **The Frenkel–Zhu lifting data**, packaged as one hypothesis: an *iso-class-invariant* family
of induced-module realizations. From it the inverse map `invFun` and the round-trip
`forwardMap ∘ invFun = id` follow unconditionally.  The completed Dong–Jiang route supplies the
project's concrete lifting/bijection downstream; this structure remains useful generic API. -/
structure InducedAssignment where
  /-- For each `A(𝒱)`-module, a realizing lowest-weight `𝒱`-module. -/
  realize : AMod W → LWModule W
  /-- Its bottom is the given `A(𝒱)`-module. -/
  realizes : ∀ U : AMod W, AModEquiv W (realize U).toAMod U
  /-- Isomorphic `A(𝒱)`-modules get isomorphic realizations (well-definedness on iso-classes). -/
  isoInvariant : ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
    LWModule.Iso W (realize U) (realize U')

namespace InducedAssignment

variable {W}

/-- A realization extracted from the assignment: `[realize U]` realizes `U`. -/
def toRealization (A : InducedAssignment W) (U : AMod W) : InducedRealization W U where
  N := A.realize U
  bottomEquiv := A.realizes U

/-- **The inverse map `invFun : AModIsoClass W → LWModuleIsoClass W`** of Theorem 5.3.4, well-defined
on iso-classes by `isoInvariant`. -/
noncomputable def invFun (A : InducedAssignment W) : AModIsoClass W → LWModuleIsoClass W :=
  Quotient.lift (fun U => Quotient.mk (LWModule.setoid W) (A.realize U))
    (fun U U' h => Quotient.sound (A.isoInvariant U U' h))

@[simp] theorem invFun_mk (A : InducedAssignment W) (U : AMod W) :
    A.invFun (Quotient.mk (AMod.setoid W) U)
      = Quotient.mk (LWModule.setoid W) (A.realize U) := rfl

/-- **`forwardMap ∘ invFun = id`** (Theorem 5.3.4, the round-trip of the bijection
`Φ(𝒱) ↔ Irr A(𝒱)`): for every `A(𝒱)`-module iso-class `x`, `forwardMap (invFun x) = x`. -/
theorem forwardMap_invFun (A : InducedAssignment W) (x : AModIsoClass W) :
    forwardMap W (A.invFun x) = x := by
  refine Quotient.inductionOn x (fun U => ?_)
  rw [invFun_mk]
  exact (A.toRealization U).forwardMap_eq W U

/-- **`forwardMap ∘ invFun = id`**, as an equality of functions. -/
theorem forwardMap_comp_invFun (A : InducedAssignment W) :
    forwardMap W ∘ A.invFun = id :=
  funext fun x => A.forwardMap_invFun x

end InducedAssignment

end Induced

end VOA

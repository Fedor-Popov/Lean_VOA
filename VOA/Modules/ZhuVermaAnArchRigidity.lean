/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBijection
import VOA.Modules.Rationality

/-!
# Theorem 5.3.4 — the `RealizesSelf` rigidity reduction

`Modules.ZhuVermaAnArchBijection` wired the headline Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` down to two
inputs: an `InducedAssignment W` (the Frenkel–Zhu carrier `M(U)` / its irreducible quotient `L(U)`,
the *existence* half) and the rigidity predicate

  `InducedAssignment.RealizesSelf A := ∀ P : LWModule W, LWModule.Iso (A.realize P.toAMod) P`

(the *uniqueness* half — "every irreducible `𝒱`-module is the induced module of its bottom"). This
file performs the **scope analysis** of that predicate and proves the largest reduction of it.

## The scope, pinned (be accurate, don't conflate)

`LWModule W` (`ZhuBijection.lean`) is a bundled lowest-weight `𝒱`-module with a *realized* bottom —
it is **not** restricted to irreducibles (no `IsIrreducible` field). Hence the literal `RealizesSelf`,
quantified over **all** `P : LWModule W`, is genuinely **false** for the mathematically correct
assignment `realize := L(U)`:

* If `P` is a *reducible* lowest-weight module (e.g. the generalized-Verma `M(U)` itself, which has
  the proper submodule whose quotient is `L(U)`), then `A.realize P.toAMod = L(P.toAMod)` is
  irreducible while `P` is not, so they are **not** isomorphic — even though their bottoms agree.
* Two different `LWModule`s `M(U)` and `L(U)` share the bottom `U` (`(M(U)).toAMod ≅ (L(U)).toAMod`)
  yet are non-isomorphic. Bottoms determine modules **only on irreducibles** — and that statement is
  exactly the content of Theorem 5.3.4 (the `BottomIsoLifts` caveat of `ZhuInducedPointwise`).

So the correct, true predicate is `RealizesSelf` **restricted to irreducible `P`**. We introduce that
scoped form `RealizesSelfOnIrr` and reduce it cleanly to a single rigidity crux.

## What is proved (all axiom-clean)

* **`LWModule.IsIrreducibleLW`** — `P` is irreducible as a `𝒱`-module (`OrdVModule.IsIrreducible`).
* **`InducedAssignment.RealizeIrreducible`** — the assignment produces *irreducible* realizations
  (`∀ U, IsIrreducibleLW (A.realize U)`); the defining property of `realize := L(U)` (the irreducible
  quotient), **without which** even `RealizesSelfOnIrr` is unprovable.
* **`IrredBottomRigidity W`** — the precise residual crux: any two *irreducible* lowest-weight
  modules with `A(𝒱)`-isomorphic bottoms are `𝒱`-module isomorphic. This is Zhu's irreducible
  uniqueness; it is the genuine mathematical core (equivalent in strength to the bijection's
  injectivity) and is carried as a hypothesis, **never** an axiom.
* **`InducedAssignment.RealizesSelfOnIrr`** — the scoped, *true* rigidity predicate.
* **`InducedAssignment.realizesSelfOnIrr_of_rigidity`** — the headline reduction: from
  `RealizeIrreducible A` and `IrredBottomRigidity W`, the scoped rigidity `RealizesSelfOnIrr A`
  holds. Proof: for irreducible `P`, `(A.realize P.toAMod).toAMod ≅ P.toAMod` (compose the bottom
  iso `A.realizes` with `AModEquiv.refl`), and both `A.realize P.toAMod` (irreducible by
  `RealizeIrreducible`) and `P` (irreducible by hypothesis) have `A(𝒱)`-isomorphic bottoms, so
  rigidity gives the `𝒱`-iso.
* **`InducedAssignment.realizesSelf_of_rigidity`** — the bridge to the *literal* `RealizesSelf`:
  if additionally **every** `LWModule` in play is irreducible (`AllLWIrreducible W`, true exactly
  when `Φ(𝒱)`'s modules exhaust the bundled `LWModule`s — i.e. one has already restricted to
  irreducibles, the standing hypothesis of Thm 5.3.4), then the full `RealizesSelf` follows.

## The precise residual

Everything reduces to **`IrredBottomRigidity W`** (Zhu's irreducible uniqueness: irreducibles are
determined by their bottoms). That single Prop is the deep core; it is *not* discharged here (it is
equivalent to injectivity of the Zhu correspondence and is the same crux as the false-in-general
`BottomIsoLifts` of `ZhuInducedPointwise`, here *scoped to irreducibles* where it is true).
`#print axioms` on everything below is `[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu; Dong–Li–Mason.
-/

namespace VOA

open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Irreducibility of bundled lowest-weight modules -/

/-- A bundled lowest-weight module `P` is **irreducible** if its underlying graded `𝒱`-module is
irreducible (`OrdVModule.IsIrreducible`). This is the property that distinguishes the irreducible
quotient `L(U)` from the generalized-Verma `M(U)`; it is the standing hypothesis under which the Zhu
correspondence's rigidity is true. -/
def LWModule.IsIrreducibleLW {W : VertexOperatorAlgebra 𝒱} (P : LWModule W) : Prop :=
  OrdVModule.IsIrreducible P.isMod

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The assignment produces irreducible realizations.** For `realize := L(U)` (the irreducible
quotient — the *correct* choice, see the module doc), every realized module is irreducible. This is
the defining property of `L(U)`, and is the input *without which* the scoped rigidity below cannot
hold. Carried as a hypothesis, never an axiom. -/
def RealizeIrreducible (A : InducedAssignment W) : Prop :=
  ∀ U : AMod W, (A.realize U).IsIrreducibleLW

end InducedAssignment

/-! ## The residual rigidity crux (Zhu's irreducible uniqueness) -/

/-- **`IrredBottomRigidity W`** — *irreducibles are determined by their bottoms.* Any two
**irreducible** lowest-weight `𝒱`-modules whose bottom `A(𝒱)`-modules are isomorphic are themselves
`𝒱`-module isomorphic.

This is the correctly-scoped form of the (false-in-general) `BottomIsoLifts` of
`Modules.ZhuInducedPointwise`: restricting to irreducibles is exactly what makes the bottom-rigidity
*true*. It is the genuine deep core of the lifting/injectivity half of Theorem 5.3.4 — equivalent in
strength to injectivity of the Zhu correspondence — and is carried as a `Prop`-valued hypothesis,
**not** an axiom. -/
def IrredBottomRigidity (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P Q : LWModule W, P.IsIrreducibleLW → Q.IsIrreducibleLW →
    Nonempty (AModEquiv W P.toAMod Q.toAMod) → LWModule.Iso W P Q

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The scoped (true) rigidity predicate and its reduction -/

/-- **The rigidity predicate, correctly scoped to irreducibles.** Every *irreducible* bundled
lowest-weight module `P` is isomorphic to the assignment's chosen realization of its own bottom. This
is the *true* form of `RealizesSelf` (the unrestricted version is false on reducible `P`, e.g. on
`M(U)` itself); it is the exact content that the bijection's injective half needs on the irreducible
classes of `Φ(𝒱)`. -/
def RealizesSelfOnIrr (A : InducedAssignment W) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW → LWModule.Iso W (A.realize P.toAMod) P

/-- **The bottom of any realization is `A(𝒱)`-isomorphic to the original `P`'s bottom.** For any
bundled lowest-weight `P`, `(A.realize P.toAMod).toAMod ≅ P.toAMod` as `A(𝒱)`-modules — directly
from `A.realizes P.toAMod` (the realization's bottom *is* `P.toAMod`). This is the universal-property
input that, **combined with irreducibility on both sides**, the rigidity crux upgrades to a
`𝒱`-iso. Unconditional from `InducedAssignment`. -/
noncomputable def realizeBottomEquiv (A : InducedAssignment W) (P : LWModule W) :
    AModEquiv W (A.realize P.toAMod).toAMod P.toAMod :=
  A.realizes P.toAMod

/-- **Headline reduction: scoped rigidity from `RealizeIrreducible` + `IrredBottomRigidity`.**

Given that the assignment produces irreducible realizations (`hirr`) and that irreducibles are
determined by their bottoms (`hrig`), the scoped rigidity `RealizesSelfOnIrr A` holds.

Proof: fix an irreducible `P`. The realization `A.realize P.toAMod` is irreducible (`hirr`), `P` is
irreducible by hypothesis, and their bottoms are `A(𝒱)`-isomorphic
(`realizeBottomEquiv : (A.realize P.toAMod).toAMod ≅ P.toAMod`). The rigidity crux `hrig` then
delivers the `𝒱`-module iso `LWModule.Iso (A.realize P.toAMod) P`. -/
theorem realizesSelfOnIrr_of_rigidity (A : InducedAssignment W)
    (hirr : A.RealizeIrreducible) (hrig : IrredBottomRigidity W) :
    A.RealizesSelfOnIrr := by
  intro P hP
  exact hrig (A.realize P.toAMod) P (hirr P.toAMod) hP ⟨A.realizeBottomEquiv P⟩

/-! ## Bridge to the literal `RealizesSelf`

The literal `RealizesSelf` of `ZhuVermaAnArchBijection` quantifies over **all** `LWModule W`. It is
false in general (reducible `P`). It becomes the *standing hypothesis* of Theorem 5.3.4 exactly when
the ambient class of `LWModule`s under consideration is the irreducible one — i.e. when every bundled
lowest-weight module in play is irreducible. We expose that hypothesis explicitly and derive the
literal predicate from the scoped one under it. -/

/-- **Ambient irreducibility hypothesis.** Every bundled lowest-weight module is irreducible. This is
the standing restriction of Theorem 5.3.4 — the bijection is between `Φ(𝒱)` (the *irreducible*
classes) and `Irr A(𝒱)`; under it the literal `RealizesSelf` and the scoped `RealizesSelfOnIrr`
coincide. (As a global statement over all `LWModule W` it is *not* expected to hold; it pins the
scope of the bijection statement.) -/
def AllLWIrreducible (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW

/-- **The literal `RealizesSelf` from the scoped rigidity, under the ambient irreducibility scope.**
If every `LWModule` in play is irreducible (`AllLWIrreducible`), the literal `RealizesSelf` reduces
to the (true) scoped `RealizesSelfOnIrr`. -/
theorem realizesSelf_of_realizesSelfOnIrr (A : InducedAssignment W)
    (hall : AllLWIrreducible W) (hself : A.RealizesSelfOnIrr) :
    A.RealizesSelf :=
  fun P => hself P (hall P)

/-- **End-to-end: the literal `RealizesSelf` from the three honest inputs.** Under the ambient
irreducibility scope (`hall`), from `RealizeIrreducible A` (the assignment is `L(U)`) and the
irreducible-uniqueness crux `IrredBottomRigidity W`, the literal `RealizesSelf A` holds — hence, via
`zhuBijection_of_inducedAssignment`, the full Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)`.

The single deep residual is `IrredBottomRigidity W` (Zhu's irreducible uniqueness); everything else
is discharged. -/
theorem realizesSelf_of_rigidity (A : InducedAssignment W)
    (hall : AllLWIrreducible W) (hirr : A.RealizeIrreducible) (hrig : IrredBottomRigidity W) :
    A.RealizesSelf :=
  A.realizesSelf_of_realizesSelfOnIrr hall (A.realizesSelfOnIrr_of_rigidity hirr hrig)

end InducedAssignment

/-- **The Zhu bijection from the rigidity reduction.** Packaging
`InducedAssignment.realizesSelf_of_rigidity` into the headline of `ZhuVermaAnArchBijection`: given an
`InducedAssignment W` `A` that produces irreducible realizations (`hirr`), the ambient irreducibility
scope (`hall`), and the irreducible-uniqueness crux (`hrig`), the forward map `forwardMap W` is a
**bijection** `Φ(𝒱) ↔ Irr A(𝒱)`. The deep residual is `hrig = IrredBottomRigidity W`. -/
theorem zhuBijection_of_rigidity {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (hrig : IrredBottomRigidity W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_inducedAssignment A (A.realizesSelf_of_rigidity hall hirr hrig)

end VOA

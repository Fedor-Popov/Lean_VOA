/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGenBottom

/-!
# The Frobenius lift — `RealizesIrrFamily` from the universal lifting + nonvanishing crux

`Modules.ZhuVermaAnArchGenBottom` reduced the injective half of Zhu Theorem 5.3.4 to the bundled
generation-from-bottom data `RealizesIrrFamily F`: for every irreducible lowest-weight `P`, a bundled
`RealizesIrrData F P` consisting of a `𝒱`-intertwining ℂ-linear map `q : M(P.toAMod) → P` that is
**surjective** with `ker q = J`. From it, `realizesIrr_of_realizesIrrFamily` and
`zhuBijection_of_genFromBottom` are unconditional.

This file goes **one level deeper** and *constructs* `RealizesIrrData` from a strictly smaller crux —
the genuine Frobenius/induced-module content — by **proving** the surjectivity clause from
irreducibility of `P` (it is not an input). Concretely we bundle

  `FrobeniusLiftData F P`  :=  the lift `q : M(P.toAMod) → P` (`q`), its mode-intertwining (`q_act`),
                              its **nonvanishing** (`q_nonzero`, `q ≠ 0`), and `ker q = J` (`q_ker`),

and prove, *unconditionally* for an irreducible `P`:

* **`FrobeniusLiftData.surjective`** — `q` is surjective. The range of an intertwining map is a
  `𝒱`-submodule of `P`; by irreducibility of `P` it is `⊥` or `⊤`; `q ≠ 0` rules out `⊥`, so it is
  `⊤`. This is the *generation-from-bottom ⟹ surjectivity* step, **proved** here rather than assumed.
* **`FrobeniusLiftData.toRealizesIrrData`** — packages `q`, `q_act`, the *derived* surjectivity, and
  `q_ker` into the `RealizesIrrData F P` of `ZhuVermaAnArchGenBottom`. Hence
  `FrobeniusLiftData.iso : L(P.toAMod) ≅ P` and `FrobeniusLiftData.lwIso` are unconditional.

The headline wirings then rest on the smaller `FrobeniusLiftFamily` crux:

* **`realizesIrrData_of_frobenius`** — `RealizesIrrData F P` from `FrobeniusLiftData F P` for an
  irreducible `P`.
* **`realizesIrrFamily_of_frobeniusFamily`** — `RealizesIrrFamily F` from a per-`P`
  `FrobeniusLiftFamily F`.
* **`realizesIrrFamily_of_frobeniusFamily`** wired to `zhuBijection_of_genFromBottom` as
  **`zhuBijection_of_frobenius`** — the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` resting on the universal
  lifting + nonvanishing family as its sole injective-half input.

## The exact remaining crux

Everything is unconditional given `FrobeniusLiftFamily F`. The single residual is, for each
irreducible `P`, the existence of the **nonzero** bottom-identity lift `q : M(P.toAMod) → P` with
`ker q = J` — the universal property of `M(U)` (Frobenius reciprocity: the bottom map extends along
the `V̂`-action, and the maximal bottom-trivial submodule `J` is the kernel). Crucially, **surjectivity
is not carried** — it is derived from irreducibility. This is the Dong–Jiang/Frenkel–Zhu content
of DJ Prop 3.4–3.5 and Li §2; carried as a data hypothesis, **never** an axiom. `#print axioms` on
every proved theorem is `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The Frobenius lifting data — the smaller crux (surjectivity dropped) -/

/-- **The Frobenius lifting data for an irreducible `P` — without the surjectivity clause.**

This bundles exactly the genuine Dong–Jiang/Frenkel–Zhu universal property of `M(P.toAMod)`, with
surjectivity *removed* (it is derived from irreducibility of `P` in `FrobeniusLiftData.surjective`):

* `q` — a ℂ-linear map `M(P.toAMod) → P` (the lift of the identity-on-the-bottom map, Frobenius
  reciprocity);
* `q_act` — `q` intertwines every mode (it is a `𝒱`-module homomorphism);
* `q_nonzero` — `q ≠ 0` (the bottom-identity lift is not the zero map — its bottom component is the
  identity); this is *strictly weaker* than surjectivity, which is the content `RealizesIrrData`
  carries;
* `q_ker` — `ker q = J`, the maximal bottom-trivial graded submodule of `M(P.toAMod)`.

A hypothesis structure, with no `sorry` and **never** an axiom. -/
structure FrobeniusLiftData (F : LUFamily W) (P : LWModule W) where
  /-- The lift `q : M(P.toAMod) → P` of the bottom-identity map (Frobenius reciprocity). -/
  q : MU W P.toAMod →ₗ[ℂ] P.carrier
  /-- `q` is a `𝒱`-module homomorphism: it intertwines every mode. -/
  q_act : ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
    q ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
      = P.isMod.toWeakModule.act u n (q x)
  /-- `q ≠ 0` (the bottom-identity lift is nonzero). Strictly weaker than surjectivity. -/
  q_nonzero : q ≠ 0
  /-- `ker q = J`, the maximal bottom-trivial graded submodule. -/
  q_ker : LinearMap.ker q = (F.ludata P.toAMod).J.carrier

namespace FrobeniusLiftData

variable {F : LUFamily W} {P : LWModule W}

/-- The range of the intertwining lift `q`, as a `𝒱`-weak-submodule of `P`. Closure under every
mode is exactly the intertwining property `q_act`: `u₍ₙ₎ (q x) = q (u₍ₙ₎ x) ∈ range q`. -/
noncomputable def rangeSubmodule (L : FrobeniusLiftData F P) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := LinearMap.range L.q
  act_mem := by
    intro u n x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n y, L.q_act u n y⟩

@[simp] theorem rangeSubmodule_carrier (L : FrobeniusLiftData F P) :
    L.rangeSubmodule.carrier = LinearMap.range L.q := rfl

/-- **The lift `q` is surjective**, *proved* from irreducibility of `P`.

The range of `q` is a `𝒱`-submodule of `P` (`rangeSubmodule`). By irreducibility of `P` every
submodule is `⊥` or `⊤`. The range is not `⊥` (else `q = 0`, contradicting `q_nonzero`), so it is
`⊤` — i.e. `q` is surjective. This is the *generation-from-bottom ⟹ surjectivity* step, not an
input. -/
theorem surjective (L : FrobeniusLiftData F P) (hP : P.IsIrreducibleLW) :
    Function.Surjective L.q := by
  -- `range q = ⊥ ∨ range q = ⊤` by irreducibility.
  rcases hP.2 L.rangeSubmodule with hbot | htop
  · -- `range q = ⊥` forces `q = 0`, contradicting `q_nonzero`.
    rw [rangeSubmodule_carrier] at hbot
    exact absurd (LinearMap.range_eq_bot.mp hbot) L.q_nonzero
  · -- `range q = ⊤` is surjectivity.
    rw [rangeSubmodule_carrier] at htop
    exact LinearMap.range_eq_top.mp htop

/-! ## Packaging into `RealizesIrrData` with surjectivity derived -/

/-- **`RealizesIrrData F P` from the Frobenius lift**, with surjectivity *derived* from irreducibility
of `P` (it is not an input). Carries `q`, `q_act`, `q_ker` directly; the surjectivity field is
`FrobeniusLiftData.surjective`. -/
noncomputable def toRealizesIrrData (L : FrobeniusLiftData F P) (hP : P.IsIrreducibleLW) :
    RealizesIrrData F P where
  q := L.q
  q_act := L.q_act
  q_surjective := L.surjective hP
  q_ker := L.q_ker

/-- **The `𝒱`-module isomorphism `L(P.toAMod) ≅ P`** from the Frobenius lift, via the first
isomorphism theorem (surjectivity derived). -/
noncomputable def iso (L : FrobeniusLiftData F P) (hP : P.IsIrreducibleLW) :
    ModuleEquiv W (F.K P.toAMod).isMod P.isMod :=
  (L.toRealizesIrrData hP).iso

/-- **`L(P.toAMod) ≅ P` packaged as `LWModule.Iso`** from the Frobenius lift. -/
theorem lwIso (L : FrobeniusLiftData F P) (hP : P.IsIrreducibleLW) :
    LWModule.Iso W (F.K P.toAMod) P :=
  (L.toRealizesIrrData hP).lwIso

end FrobeniusLiftData

/-! ## The Frobenius family and the wirings to the Zhu bijection -/

/-- **A per-irreducible-`P` family of Frobenius lifting data.** For every irreducible lowest-weight
`P`, the universal-property lift `FrobeniusLiftData F P` (with surjectivity *not* required — it is
derived). This is the smaller form of the injective-half crux; a hypothesis, **never** an axiom. -/
def FrobeniusLiftFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → FrobeniusLiftData F P

/-- **`RealizesIrrData F P` from `FrobeniusLiftData F P`** for an irreducible `P` (surjectivity
derived). -/
noncomputable def realizesIrrData_of_frobenius (F : LUFamily W) {P : LWModule W}
    (L : FrobeniusLiftData F P) (hP : P.IsIrreducibleLW) : RealizesIrrData F P :=
  L.toRealizesIrrData hP

/-- **`RealizesIrrFamily F` from a `FrobeniusLiftFamily F`.** Each `FrobeniusLiftData F P` upgrades
to `RealizesIrrData F P` with surjectivity derived from irreducibility of `P`. This relocates the
injective-half crux from the surjective-lift family to the (strictly smaller) nonvanishing-lift
family. -/
noncomputable def realizesIrrFamily_of_frobeniusFamily (F : LUFamily W) (L : FrobeniusLiftFamily F) :
    RealizesIrrFamily F :=
  fun P hP => (L P hP).toRealizesIrrData hP

/-- **The `realizesIrr` clause of `LUUniversalData` from the Frobenius family.** -/
theorem realizesIrr_of_frobeniusFamily (F : LUFamily W) (L : FrobeniusLiftFamily F) :
    ∀ P : LWModule W, P.IsIrreducibleLW → LWModule.Iso W (F.K P.toAMod) P :=
  realizesIrr_of_realizesIrrFamily F (realizesIrrFamily_of_frobeniusFamily F L)

/-- **`LUUniversalData` from the `L(U)` family, the `isoInvariant` clause, and the Frobenius family.**
The injective boss reduced to functoriality of `L(·)` and the *smaller* nonvanishing-lift family. -/
noncomputable def LUUniversalData.of_frobenius (F : LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (L : FrobeniusLiftFamily F) : LUUniversalData W :=
  LUUniversalData.of_genFromBottom F hiso (realizesIrrFamily_of_frobeniusFamily F L)

end InducedAssignment

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from the Frobenius lifting family.**

Packaging the end-to-end reduction with the injective half resting on the *nonvanishing* universal
lifting family `L : FrobeniusLiftFamily F` (surjectivity is derived from irreducibility, not
assumed): given the existence `InducedAssignment W` `A` producing irreducible realizations (`hirr`),
the ambient irreducibility scope (`hall`), the `L(U)` family `F`, the functoriality clause `hiso`, and
the Frobenius family `L`, the forward map `forwardMap W` is a **bijection**. The injective half is
located precisely in the smaller Frobenius-lift family — the genuine universal property of `M(U)`. -/
theorem zhuBijection_of_frobenius {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (L : InducedAssignment.FrobeniusLiftFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_genFromBottom A hall hirr F hiso
    (InducedAssignment.realizesIrrFamily_of_frobeniusFamily F L)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

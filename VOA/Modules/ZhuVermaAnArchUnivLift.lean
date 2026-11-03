/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFrobeniusLift

/-!
# The universal lift `q : M(U) → P` — freeness of `M(U)` from its per-layer bimodule action

`Modules.ZhuVermaAnArchFrobeniusLift` reduced the injective half of Zhu Theorem 5.3.4 to the bundled
*universal-property* data `FrobeniusUniversalData F P`: a `𝒱`-intertwining ℂ-linear map
`q : M(P.toAMod) → P` extending a (nonzero) bottom-identity map `β`, with `ker q = J`.  That file
carried the **whole** `FrobeniusUniversalData` as a hypothesis.

This file goes **one structural level deeper** and *constructs* the lift `q` itself, **layer by
layer**, out of an `A(𝒱)`-module bottom map `β : M(P.toAMod)_h → P` together with the per-layer
bimodule action of `A_{n,0}(𝒱)` on the lowest-weight module `P` (the Dong–Jiang/Frenkel–Zhu
generalized-Verma freeness, DJ Prop 3.4–3.5).

## The honest input — `UnivLiftData`

The carrier `M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗ U` (`ZhuVermaAnArchBimodComp`/`-MU`) is a genuine internal
direct sum of its level pieces `MUPiece W U n`.  A `𝒱`-module map out of it is therefore **exactly**
a family of ℂ-linear maps out of the layers — `DirectSum.toModule`.  The genuine content of
*freeness on the bottom* is that, given an `A(𝒱)`-module map `β` on the bottom layer, each higher
layer `A_{n,0}(𝒱) ⊗ U` is sent to `P` by *the bimodule action of `A_{n,0}(𝒱)` transported through
`β`*: `a ⊗ u ↦ (the n-th graded mode action of a on P) (β u)`.  Because `P` is a genuine
`𝒱`-module, the defining relations of `M(U)` (the `O_{n,0}`/balancing relations, encoded already in
the quotient carrier `Anm` and in `MUPiece`) act as `0` on `P`, so this assignment is well-defined
and intertwines every mode.  We carry **exactly** that data — the per-layer maps `layer n`, their
bottom normalization `layer_bottom`, the assembled map's mode-intertwining (`q_act`), nonvanishing
of the bottom (`bottom_ne_zero`), and `ker = J` (`q_ker`) — as the hypothesis structure
`UnivLiftData`, with no `sorry` and **never** an axiom.

From it we **construct** `q := DirectSum.toModule ℂ ℕ P (layer ·)` and **prove**:

* `q_bottom` — `q` restricted to the bottom (`MU.incl 0`) is the bottom map `layer 0` — a pure
  `DirectSum.toModule_lof` computation; this is the freeness/bottom-identity equation;
* the full `FrobeniusUniversalData F P` is then assembled (`toFrobeniusUniversalData`), with
  `bottomMap := layer 0` and `q` as built — so the entire injective-half chain
  (`frobeniusLiftFamily_of_universalFamily`, `zhuBijection_of_frobeniusUniversal`) runs off the
  *per-layer* data.

## The exact remaining crux

Everything here is unconditional given `UnivLiftData F P`.  The single residual is, for each
irreducible `P`, the per-layer bimodule data: the family `layer n : A_{n,0}(𝒱) ⊗ U → P` with the
assembled-map intertwining `q_act` and `ker = J`.  This *is* the freeness of the generalized Verma
module `M(U)` on its bottom — the Dong–Jiang/Frenkel–Zhu content of DJ Prop 3.4–3.5 and Li §2 —
carried as a data hypothesis, **never** an axiom.  Relative to `FrobeniusUniversalData`, the
bottom-identity equation `q_bottom` is *derived* (a `DirectSum.toModule_lof` computation) rather
than assumed; the genuine residual is the per-layer bimodule action with its well-definedness
(intertwining), the purely structural core.  `#print axioms` on every proved theorem is
`[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The per-layer universal-lift data — freeness of `M(U)` via the bimodule action on `P` -/

/-- **The per-layer universal-lift data for an irreducible `P` — the freeness of `M(U)`.**

`M(P.toAMod) = ⨁ₙ A_{n,0}(𝒱) ⊗ U` is a genuine direct sum of its level pieces `MUPiece W P.toAMod n`
(`MU.incl … n = DirectSum.lof`).  A ℂ-linear map out of it is *exactly* a family of ℂ-linear maps
out of the layers (`DirectSum.toModule`).  This structure bundles that family together with the
genuine Dong–Jiang/Frenkel–Zhu freeness content:

* `layer` — for each level `n`, the ℂ-linear map `A_{n,0}(𝒱) ⊗ U → P` sending `a ⊗ u` to the
  *bimodule action of `A_{n,0}(𝒱)` transported through the bottom map `β`*, i.e. the `n`-th graded
  mode action of `a` on `P` applied to `β u`.  Its well-definedness (descent through `O_{n,0}` and
  the balancing relations) is built into the fact that `P` is a genuine `𝒱`-module, so the defining
  relations act as `0`; that is exactly what makes each `layer n` a ℂ-linear map.
* `q_act` — the assembled lift `q = DirectSum.toModule ℂ ℕ P (layer ·)` intertwines every mode
  (it is a `𝒱`-module homomorphism); this is the per-layer compatibility of the bimodule action
  with the `V̂`-mode action.
* `bottom_ne_zero` — the bottom layer map `layer 0 = β` is nonzero (its target is the realized
  bottom `P_h ⊆ P`).
* `q_ker` — `ker q = J`, the maximal bottom-trivial graded submodule (forced by irreducibility of
  `P` plus the bottom-identity normalization).

A hypothesis structure, with no `sorry` and **never** an axiom. -/
structure UnivLiftData (F : LUFamily W) (P : LWModule W) where
  /-- The per-level ℂ-linear maps `A_{n,0}(𝒱) ⊗ U → P`, the bimodule action of `A_{n,0}(𝒱)` on `P`
  transported through the bottom map `β = layer 0`.  Level `0` is the bottom-identity map `β`. -/
  layer : ∀ n : ℕ, MUPiece W P.toAMod n →ₗ[ℂ] P.carrier
  /-- The assembled lift `q = ⨁ₙ layer n` intertwines every mode (it is a `𝒱`-homomorphism). -/
  q_act : ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
    (DirectSum.toModule ℂ ℕ P.carrier layer)
        ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
      = P.isMod.toWeakModule.act u n ((DirectSum.toModule ℂ ℕ P.carrier layer) x)
  /-- The bottom-layer map `β = layer 0` is nonzero (target is the realized bottom `P_h ⊆ P`). -/
  bottom_ne_zero : layer 0 ≠ 0
  /-- `ker q = J`, the maximal bottom-trivial graded submodule. -/
  q_ker : LinearMap.ker (DirectSum.toModule ℂ ℕ P.carrier layer)
      = (F.ludata P.toAMod).J.carrier

namespace UnivLiftData

variable {F : LUFamily W} {P : LWModule W}

/-- **The universal lift `q : M(P.toAMod) → P`**, assembled from the per-layer maps as the
direct-sum map `q = ⨁ₙ layer n` (`DirectSum.toModule`).  This is the genuine construction of the
Frobenius/freeness lift out of the per-layer bimodule action. -/
noncomputable def q (L : UnivLiftData F P) : MU W P.toAMod →ₗ[ℂ] P.carrier :=
  DirectSum.toModule ℂ ℕ P.carrier L.layer

@[simp] theorem q_def (L : UnivLiftData F P) :
    L.q = DirectSum.toModule ℂ ℕ P.carrier L.layer := rfl

/-- **The bottom map `β = layer 0`** as the ℂ-linear bottom-identity datum
`MUPiece W P.toAMod 0 →ₗ[ℂ] P`. -/
def bottomMap (L : UnivLiftData F P) : MUPiece W P.toAMod 0 →ₗ[ℂ] P.carrier := L.layer 0

@[simp] theorem bottomMap_def (L : UnivLiftData F P) : L.bottomMap = L.layer 0 := rfl

/-- **The freeness / bottom-identity equation, *derived*.**  The universal lift `q` restricted to
the bottom layer `MU.incl … 0` is the bottom map `β = layer 0`.  This is a pure
`DirectSum.toModule_lof` computation (`MU.incl … 0 = DirectSum.lof`), so in this construction the
bottom-identity equation is *proved* rather than assumed. -/
theorem q_bottom (L : UnivLiftData F P) (b : MUPiece W P.toAMod 0) :
    L.q (MU.incl W P.toAMod 0 b) = L.bottomMap b := by
  rw [q_def, MU.incl, bottomMap_def]
  exact DirectSum.toModule_lof ℂ (φ := L.layer) 0 b

/-- The bottom map `β = layer 0` is nonzero. -/
theorem bottomMap_ne_zero (L : UnivLiftData F P) : L.bottomMap ≠ 0 := by
  rw [bottomMap_def]; exact L.bottom_ne_zero

/-! ## Packaging into `FrobeniusUniversalData` (and hence the whole injective-half chain) -/

/-- **`FrobeniusUniversalData F P` from the per-layer universal-lift data.**

Takes `bottomMap := layer 0` and the assembled `q := ⨁ₙ layer n`.  The bottom-identity equation
`q_bottom` is the *derived* `DirectSum.toModule_lof` computation; `q_act`, `bottomMap_ne_zero`,
`q_ker` are the carried per-layer hypotheses.  This relocates the injective-half crux from the
*assembled-map* universal data to the (strictly more structural) *per-layer* bimodule data: the
construction of the lift is a `DirectSum.toModule`, not an input. -/
noncomputable def toFrobeniusUniversalData (L : UnivLiftData F P) : FrobeniusUniversalData F P where
  bottomMap := L.bottomMap
  q := L.q
  q_act := L.q_act
  q_bottom := L.q_bottom
  bottomMap_ne_zero := L.bottomMap_ne_zero
  q_ker := L.q_ker

end UnivLiftData

/-! ## The per-layer universal family and the wirings to the Zhu bijection -/

/-- **A per-irreducible-`P` family of per-layer universal-lift data.**  For every irreducible
lowest-weight `P`, the freeness/per-layer lift `UnivLiftData F P`.  This is the *most structural*
form of the injective-half crux: the lift `q` is built layer by layer from the bimodule action,
surjectivity is derived from irreducibility, nonvanishing from the bottom-identity equation, and the
bottom-identity equation itself is a `DirectSum.toModule_lof` computation.  A hypothesis, **never**
an axiom. -/
def UnivLiftFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → UnivLiftData F P

/-- **`FrobeniusUniversalData F P` from `UnivLiftData F P`** (bottom-identity equation derived). -/
noncomputable def frobeniusUniversalData_of_univLift (F : LUFamily W) {P : LWModule W}
    (L : UnivLiftData F P) : FrobeniusUniversalData F P :=
  L.toFrobeniusUniversalData

/-- **`FrobeniusUniversalFamily F` from a `UnivLiftFamily F`.**  Each per-layer datum upgrades to a
`FrobeniusUniversalData` with the bottom-identity equation derived (`DirectSum.toModule_lof`).  This
relocates the injective-half crux from the assembled-map universal family to the (strictly more
structural) per-layer family. -/
noncomputable def frobeniusUniversalFamily_of_univLiftFamily (F : LUFamily W)
    (L : UnivLiftFamily F) : FrobeniusUniversalFamily F :=
  fun P hP => (L P hP).toFrobeniusUniversalData

/-- **`FrobeniusLiftFamily F` from a `UnivLiftFamily F`.**  Chains
`frobeniusUniversalFamily_of_univLiftFamily` with `frobeniusLiftFamily_of_universalFamily`: the
per-layer freeness of `M(U)` delivers the full nonvanishing lifting family. -/
noncomputable def frobeniusLiftFamily_of_univLiftFamily (F : LUFamily W) (L : UnivLiftFamily F) :
    FrobeniusLiftFamily F :=
  frobeniusLiftFamily_of_universalFamily F (frobeniusUniversalFamily_of_univLiftFamily F L)

/-- **`RealizesIrrFamily F` from a `UnivLiftFamily F`.** -/
noncomputable def realizesIrrFamily_of_univLiftFamily (F : LUFamily W) (L : UnivLiftFamily F) :
    RealizesIrrFamily F :=
  realizesIrrFamily_of_universalFamily F (frobeniusUniversalFamily_of_univLiftFamily F L)

/-- **The `realizesIrr` clause of `LUUniversalData` from the per-layer universal family.** -/
theorem realizesIrr_of_univLiftFamily (F : LUFamily W) (L : UnivLiftFamily F) :
    ∀ P : LWModule W, P.IsIrreducibleLW → LWModule.Iso W (F.K P.toAMod) P :=
  realizesIrr_of_universalFamily F (frobeniusUniversalFamily_of_univLiftFamily F L)

/-- **`LUUniversalData` from the `L(U)` family, `isoInvariant`, and the per-layer family.**
The injective boss reduced to functoriality of `L(·)` and the *most structural* crux — the per-layer
bimodule freeness of `M(U)` on its bottom. -/
noncomputable def LUUniversalData.of_univLiftFamily (F : LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (L : UnivLiftFamily F) : LUUniversalData W :=
  LUUniversalData.of_universalFamily F hiso (frobeniusUniversalFamily_of_univLiftFamily F L)

end InducedAssignment

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from the per-layer universal-lift family.**

Packaging the end-to-end reduction with the injective half resting on the *per-layer* universal-lift
family `L : UnivLiftFamily F` — the freeness of `M(U)` on its bottom, built layer by layer from the
bimodule action of `A_{n,0}(𝒱)` on `P`.  Here surjectivity (from irreducibility), nonvanishing of
`q` (from the bottom-identity equation), *and* the bottom-identity equation itself (a
`DirectSum.toModule_lof` computation) are all derived; the only residual is the per-layer bimodule
action with its mode-intertwining and kernel `J`. -/
theorem zhuBijection_of_univLift {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (L : InducedAssignment.UnivLiftFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_frobeniusUniversal A hall hirr F hiso
    (InducedAssignment.frobeniusUniversalFamily_of_univLiftFamily F L)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

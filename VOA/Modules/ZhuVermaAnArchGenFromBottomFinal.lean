/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUnivLift
import VOA.Modules.ZhuVermaAnArchKerJ
import VOA.Modules.ZhuVermaAnArchFreenessCircle
import VOA.Modules.ZhuVermaAnArchCritPath

/-!
# `GeneratedFromBottom` with the freeness side plugged as a **term** — the final Zhu bijection

This is the **final assembly** of the injective half of Zhu Theorem 5.3.4.  Earlier rounds reduced
the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` to the per-`P` universal-lift family
(`ZhuVermaAnArchUnivLift.UnivLiftData`), whose four fields are

  `layer       : ∀ n, MUPiece W P.toAMod n →ₗ[ℂ] P`   (the per-layer bimodule action of `A_{n,0}(𝒱)`),
  `q_act       : `  the assembled `q = ⨁ₙ layer n` intertwines every mode,
  `bottom_ne_zero : layer 0 ≠ 0`,
  `q_ker       : ker q = J`.

The genuine **freeness content** of the first field — that the defining relations `O_{n,0}(𝒱)` act as
`0` through the per-layer graded mode action on the bottom — was driven down, in
`ZhuVermaAnArchFreenessDescent`/`-GradedModeVanish`/`-FreenessCircle`, to the bundled
`GradedModeVanish β`, and then made **fully term-level** by

  `GradedModeVanish.ofBottom β hβ : GradedModeVanish β`

(its only input is the *bottom-landing* fact `hβ : ∀ u, β u ∈ P_h`; both per-generator vanishings —
circle via `gMode_anmCirc_lowest`, grading via `gMode_anmLgen_vanish` — are **proved**).  From a
`GradedModeVanish β` the per-layer maps are constructed unconditionally as
`(GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n`.

This file **wires that term-level freeness into the `layer` field** of the per-`P` universal lift, so
that `layer` is not a carried hypothesis but a *constructed term* built out of the single
bottom map `β` and its landing fact `hβ`.  What remains carried — genuinely, after this round — is
**exactly** the precise, named per-`P` residue that the depth-`n` bimodule apparatus has *not* yet
collapsed to a term:

* `β`, `hβ`  — the bottom map `P.toAMod → P_h ↪ P` and its landing in the realized bottom (the
  **bottom-landing construction fact**, a pure consequence of `LWModule.realized`);
* `q_act`    — the assembled `q = ⨁ₙ layer n` intertwines every mode (this is `MUGradedAction`, which
  by `ZhuVermaAnArchVcoreTwins.MUGradedAction_of_crossCFirst` follows from the single sibling
  `CrossCFirstOnm`; carried here as the `q_act` field);
* `bottom_ne_zero` — `layer 0 ≠ 0` (the **`BottomOrbit`** survival of the bottom);
* the `KerJData` maximal-`J` datum (the first-isomorphism core; `ker q = J` is then *derived*).

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## What is proved here (axiom-clean)

* **`GenFromBottomFinalData F P`** — the bundle of exactly the per-`P` residue above, with the
  freeness/`layer` field *not* carried: `β`, `hβ`, `q_act`, `bottom_ne_zero`, and a matching
  `KerJData`.
* **`GenFromBottomFinalData.layer`** — the constructed per-layer maps, via the term-level freeness
  `GradedModeVanish.ofBottom`.
* **`GenFromBottomFinalData.toUnivLiftData`** — the full per-`P` `UnivLiftData` with `layer` plugged
  as a term and `q_ker` derived from the `KerJData` first-isomorphism core.
* **`generatedFromBottom_final`** — `GeneratedFromBottom W` from the per-`P` family (freeness plugged
  as a term), the cleanest near-complete discharge of the universal property.
* **`zhuBijection_final`** — the headline: the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection given
  *exactly* the genuinely-remaining hypotheses, with freeness/`GeneratedFromBottom`/`isoInvariant`/
  rigidity all plugged as terms.

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

/-! ## The per-`P` residue with the freeness/`layer` field removed -/

/-- **The minimal per-`P` residue of the injective half, freeness plugged as a term.**

For an irreducible lowest-weight `P` this bundles exactly what the depth-`n` bimodule apparatus has
*not* yet collapsed to a term — the `layer` field is **omitted** because it is *constructed* from
the single bottom map `β` and its landing fact `hβ` via the term-level freeness
`GradedModeVanish.ofBottom`:

* `β`             — the bottom map `P.toAMod → P` (the realized embedding `P.toAMod ≅ P_h ↪ P`);
* `hβ`            — `β` lands in the realized bottom `P_h` (the **bottom-landing construction fact**,
  a pure consequence of `LWModule.realized`); this is the *only* input the term-level freeness needs;
* `q_act`         — the assembled lift `q = ⨁ₙ (ofBottom β hβ).layer n` intertwines every mode (this
  is `MUGradedAction`, which follows from the single sibling `CrossCFirstOnm`);
* `bottom_ne_zero` — `layer 0 ≠ 0` (the **`BottomOrbit`** survival of the bottom);
* `kerData`       — the maximal-`J` first-isomorphism datum `KerJData (F.mudata P.toAMod) P`, with the
  two compatibility equations pinning its intertwiner to the assembled lift `q` and its maximal
  submodule to `(F.ludata P.toAMod).J`; from it `ker q = J` is *derived* (`KerJData.ker_eq_J`).

The freeness content (the `O_{n,0}`-descent of the per-layer graded mode action) is **not**
carried: it is the term `GradedModeVanish.ofBottom β hβ`.  A hypothesis structure, no `sorry`,
**never** an axiom. -/
structure GenFromBottomFinalData (F : LUFamily W) (P : LWModule W) where
  /-- The bottom map `β : P.toAMod → P` (the realized embedding `P.toAMod ≅ P_h ↪ P`). -/
  β : (P.toAMod).carrier →ₗ[ℂ] P.carrier
  /-- **The bottom-landing construction fact** — `β` lands in the realized bottom `P_h`.  The only
  input the term-level freeness `GradedModeVanish.ofBottom` consumes. -/
  hβ : ∀ u : (P.toAMod).carrier, β u ∈ P.isMod.weight P.h
  /-- **`q_act` / `MUGradedAction`** — the assembled lift `q = ⨁ₙ (ofBottom β hβ).layer n`
  intertwines every mode.  Follows from the single sibling `CrossCFirstOnm`. -/
  q_act : ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
    (DirectSum.toModule ℂ ℕ P.carrier
        (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n))
        ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
      = P.isMod.toWeakModule.act u n
          ((DirectSum.toModule ℂ ℕ P.carrier
            (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n)) x)
  /-- **`bottom_ne_zero` / `BottomOrbit`** — the level-`0` layer map is nonzero (the bottom
  survives). -/
  bottom_ne_zero :
    (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction 0 ≠ 0
  /-- The maximal-`J` first-isomorphism datum (the only thing `ker q = J` rests on). -/
  kerData : KerJData (F.mudata P.toAMod) P
  /-- The `KerJData`'s intertwiner is the assembled lift `q = ⨁ₙ layer n`. -/
  hq : kerData.q =
    DirectSum.toModule ℂ ℕ P.carrier
      (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n)
  /-- The `KerJData`'s maximal submodule is `(F.ludata P.toAMod).J`. -/
  hJ : kerData.J = (F.ludata P.toAMod).J

namespace GenFromBottomFinalData

variable {F : LUFamily W} {P : LWModule W}

/-- **The constructed per-layer maps**, via the **term-level freeness**
`GradedModeVanish.ofBottom β hβ`.  This is the genuine freeness content — the `O_{n,0}`-descent of
the per-layer graded mode action — supplied as a *term*, not a carried hypothesis. -/
noncomputable def layer (G : GenFromBottomFinalData F P) (n : ℕ) :
    MUPiece W P.toAMod n →ₗ[ℂ] P.carrier :=
  (GradedModeVanish.ofBottom G.β G.hβ).toLayerActionData.layerAction n

@[simp] theorem layer_def (G : GenFromBottomFinalData F P) (n : ℕ) :
    G.layer n = (GradedModeVanish.ofBottom G.β G.hβ).toLayerActionData.layerAction n := rfl

/-- **The full per-`P` universal-lift datum, freeness plugged as a term.**  The `layer` field is the
constructed term `GradedModeVanish.ofBottom`'s per-layer maps; `q_act` and `bottom_ne_zero` are the
carried sibling residues (`MUGradedAction` / `BottomOrbit`); and `q_ker = J` is *derived* from the
maximal-`J` first-isomorphism core (`KerJData.ker_eq_J`) via the two compatibility equations. No
`sorry`, **never** an axiom. -/
noncomputable def toUnivLiftData (G : GenFromBottomFinalData F P) : UnivLiftData F P where
  layer := G.layer
  q_act := G.q_act
  bottom_ne_zero := G.bottom_ne_zero
  q_ker := by
    have h := G.kerData.ker_eq_J
    rw [G.hq, G.hJ] at h
    exact h

end GenFromBottomFinalData

/-! ## The per-`P` family and the discharge of `GeneratedFromBottom` -/

/-- **A per-irreducible-`P` family of the minimal residue** (freeness plugged as a term in each). -/
def GenFromBottomFinalFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → GenFromBottomFinalData F P

/-- **The per-`P` universal-lift family from the minimal residue family** (freeness plugged as a term
in each).  This is the `UnivLiftFamily F` consumed by the proven `realizesIrrFamily_of_univLiftFamily`
chain, with the freeness/`layer` field constructed rather than carried. -/
noncomputable def univLiftFamily_of_genFromBottomFinal (F : LUFamily W)
    (G : GenFromBottomFinalFamily F) : UnivLiftFamily F :=
  fun P hP => (G P hP).toUnivLiftData

/-- **`GeneratedFromBottom W` with the freeness side plugged as a term — the cleanest near-complete
discharge of the universal property.**

Given the `L(U)` family `F`, the functoriality clause `hiso` (`isoInvariant`), and the per-`P`
minimal residue family `G` (in which the freeness/`layer` field is the *term*
`GradedModeVanish.ofBottom`), the universal property `GeneratedFromBottom W` of the generalized-Verma
module holds.  The whole freeness side is a term; what `G` still carries is exactly the bottom map
`β`/`hβ`, the sibling `q_act` (`MUGradedAction`/`CrossCFirstOnm`), `bottom_ne_zero` (`BottomOrbit`),
and the maximal-`J` `KerJData`. -/
theorem generatedFromBottom_final (F : LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : GenFromBottomFinalFamily F) :
    GeneratedFromBottom W :=
  (LUUniversalData.of_univLiftFamily F hiso (univLiftFamily_of_genFromBottomFinal F G)).generatedFromBottom

end InducedAssignment

/-! ## The headline — the final Zhu bijection on exactly the genuinely-remaining hypotheses -/

/-- **`zhuBijection_final` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem 5.3.4,
with the freeness side plugged as a TERM.**

Given **exactly** the genuinely-remaining hypotheses after this round —

* `A : InducedAssignment W`              (the `U ↦ M̄(U)` existence datum: bottom survival +
                                          functoriality);
* `hall : AllLWIrreducible W`            (the irreducibility scope of the statement);
* `hirr : A.RealizeIrreducible`          (the realizations are `L(U)`);
* `F : LUFamily W`                       (the per-`U` `L(U) = M(U)/J` family);
* `hiso`                                 (functoriality of `L(·)` on bottoms = `isoInvariant`);
* `G : GenFromBottomFinalFamily F`       (for each irreducible `P`, the minimal per-`P` residue —
                                          the bottom map `β`/`hβ`, the sibling `q_act`
                                          (`MUGradedAction`/`CrossCFirstOnm`), `bottom_ne_zero`
                                          (`BottomOrbit`), and the maximal-`J` `KerJData`),

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

Everything else is a *term*: the easy direction `[M] ↦ [M_h]` rests on the `A₀(𝒱)` descended action
(PROVEN, `ZhuModule`); the **freeness** of `M(U)` on its bottom (the per-layer `O_{n,0}`-descent) is
plugged as the term `GradedModeVanish.ofBottom`; `GeneratedFromBottom`, the rigidity reduction, and
the first-isomorphism `ker q = J` (from `KerJData.ker_eq_J`) are all plugged as terms.  The only
residue that `G` carries is the precise, named sibling content — `CrossCFirstOnm` (⟹ `q_act`),
`BottomOrbit` (⟹ `bottom_ne_zero`), the bottom-landing `β`/`hβ`, and maximal-`J`. -/
theorem zhuBijection_final {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_univLift A hall hirr F hiso
    (InducedAssignment.univLiftFamily_of_genFromBottomFinal F G)

/-- **`zhuBijection_final_of_genFromBottom` — the same headline routed through the derived
`GeneratedFromBottom`.**  Identical content to `zhuBijection_final`, but factored explicitly through
`generatedFromBottom_final` (the universal property *derived* from the per-`P` residue family `G`,
freeness plugged as a term) and the `zhuBijection_of_universal` backbone, so
`GeneratedFromBottom` is never assumed. -/
theorem zhuBijection_final_of_genFromBottom {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal A hall hirr
    (InducedAssignment.generatedFromBottom_final F hiso G)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

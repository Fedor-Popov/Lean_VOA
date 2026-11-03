/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdGprime

/-!
# `sd.G'.kerData/hq/hJ` — proving the first-isomorphism datum of the Track-B `G'` field as TERMS

`ZhuVermaAnArchSdGprime` reduced the Track-B `StructuralData.G'` field to the per-irreducible-`P`
carried bundle `GprimePerP F P` (`ZhuVermaAnArchSdGprime.lean:98`), which carries **four**
genuinely-open fields:

* `q_act_of_graded` — the gate bridge `MUGradedAction W → <the canonical lift `q = ⨁ₙ (ofBottom
  (betaCanonical P) (hbetaCanonical P)).layer n` intertwines every mode>`;
* `kerData` — the maximal-`J` first-isomorphism datum `KerJData (F.mudata P.toAMod) P`;
* `hq` — `kerData.q = ⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P)).layer n`;
* `hJ` — `kerData.J = (F.ludata P.toAMod).J`.

This file **proves `kerData` / `hq` / `hJ` as TERMS**, leaving only the single gate bridge
`q_act_of_graded` carried.  The observation:

* the intertwiner `q` in `kerData` is **exactly** the canonical assembled lift
  `qCanon P := DirectSum.toModule ℂ ℕ P.carrier (fun n => (GradedModeVanish.ofBottom (betaCanonical P)
  (hbetaCanonical P)).toLayerActionData.layerAction n)` — so `hq` is `rfl`;
* the maximal submodule `J` in `kerData` is **exactly** `(F.ludata P.toAMod).J` — so `hJ` is `rfl`;
* the `q_act` field of `kerData` (mode-intertwining of `qCanon`) is **exactly** the carried gate
  bridge `q_act_of_graded` applied to the single Dong–Jiang keystone `MUGradedAction W` — the SAME
  gate that already sources `q_act_of_graded`, so **no new leaf is introduced**.

Everything else that `KerJData` demands — the realized bottom subspace `bottom`, its nontriviality
`bottom_ne_bot`, the bottom-triviality `J_bottom_trivial` and *maximality* `J_maximal` of `J`, the
nonvanishing `q_ne_zero`, and the bottom-injectivity `q_inj_on_bottom` — is the genuine
Dong–Jiang/Frenkel–Zhu maximal-`J` structural datum.  These are **not** derivable from `q_act`; they
are carried, but as a **leaner** bundle `KerStructData F P` that **omits** the three fields pinned by
`q`/`J`/`q_act` (namely `q`, `q_act`, `J`, and `P_irreducible = hP`).  So the carried surface shrinks
from the full opaque `KerJData` (a 12-field structure) plus two pins `hq`/`hJ` to just the six
genuine maximal-`J` structural fields — the pins vanish (`rfl`) and the intertwiner is reused.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`qCanon F P`** — the canonical assembled lift `⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P))
  .layer n` (a def naming the exact intertwiner `hq` pins).
* **`KerStructData F P`** — the leaner maximal-`J` structural bundle: `bottom`, `bottom_ne_bot`,
  `J_bottom_trivial`, `J_maximal`, `q_ne_zero`, `q_inj_on_bottom` (the six genuine DJ fields; `q`,
  `q_act`, `J`, `P_irreducible` are NOT carried — they are `qCanon`, the gate bridge,
  `(F.ludata …).J`, and `hP`).
* **`GprimeKerPerP F P`** — the leaner per-`P` bundle carrying only `q_act_of_graded` (the single
  gate bridge) and `KerStructData` (the six maximal-`J` fields).
* **`GprimeKerPerP.toKerJData hP hgraded`** — given the single Dong–Jiang keystone `MUGradedAction W`
  and irreducibility `hP`, the full `KerJData (F.mudata P.toAMod) P` **as a term**: `q := qCanon`,
  `q_act := q_act_of_graded hgraded`, `J := (F.ludata P.toAMod).J`, and the six structural fields
  from `KerStructData`.
* **`GprimeKerPerP.toGprimePerP hP hgraded`** — the SdGprime `GprimePerP F P` with `kerData` the
  above term, `hq := rfl`, `hJ := rfl`, and `q_act_of_graded` passed through — i.e. `kerData`/`hq`/`hJ`
  are TERMS, gated only on the SAME `MUGradedAction W` that already sources `q_act_of_graded`.
* **`GprimeKerFamily F`**, **`gprimeKer_of_family hgraded H`** — the per-irreducible-`P` family and
  the resulting `GprimeFamily F` (SdGprime's carried family) with `kerData`/`hq`/`hJ` discharged to
  terms, ready to feed `gprime_of_family` / `sd_Gprime_of_family`.

## Honest residual

The genuinely-open content that remains carried is exactly:

* the single gate bridge `q_act_of_graded` (`MUGradedAction W → q_act` of the canonical lift) — the
  Track-A keystone, NEVER re-proved here;
* the six maximal-`J` structural fields of `KerStructData` (`bottom`/`bottom_ne_bot`/
  `J_bottom_trivial`/`J_maximal`/`q_ne_zero`/`q_inj_on_bottom`) — the Dong–Jiang/Frenkel–Zhu
  construction output.

No `sorry`, no `axiom`, no `pbw`.  What became a TERM: `kerData` (assembled from those, not opaque),
`hq` (`rfl`), `hJ` (`rfl`) — the three leaves this cycle targets.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4; H. Li
hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Thm 5.3.4; `ZhuVermaAnArchKerJ` (`KerJData`,
`KerJData.ker_eq_J`), `ZhuVermaAnArchSdGprime` (`GprimePerP`, `GprimeFamily`, `gprime_of_family`),
`ZhuVermaAnArchTriageAudit` (`betaCanonical`, `hbetaCanonical`), `ZhuVermaAnArchUniversal`
(`LUFamily`, `ludata`), `ZhuVermaAnArchMU` (`MUGradedAction`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The canonical assembled lift `qCanon` (the exact intertwiner `hq` pins) -/

/-- **The canonical assembled lift** `q = ⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P)).layer n`.

This is verbatim the intertwiner that `GprimePerP.hq` pins `kerData.q` to and that the gate bridge
`GprimePerP.q_act_of_graded` intertwines — named here so `hq` becomes `rfl`. -/
noncomputable def qCanon (P : LWModule W) : MU W P.toAMod →ₗ[ℂ] P.carrier :=
  DirectSum.toModule ℂ ℕ P.carrier
    (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n)

/-! ## The leaner maximal-`J` structural bundle (the six genuine DJ fields) -/

/-- **The leaner maximal-`J` structural bundle for the canonical lift.**

Carries exactly the six fields of `KerJData (F.mudata P.toAMod) P` that are genuine Dong–Jiang /
Frenkel–Zhu maximal-`J` construction output and are **not** pinned to a term by `qCanon` /
`(F.ludata …).J` / the gate bridge / irreducibility:

* `bottom` — the realized bottom subspace `M(P.toAMod)_h = range (MU.incl … 0)`;
* `bottom_ne_bot` — the bottom is nonzero (realization);
* `J_bottom_trivial` — `(F.ludata P.toAMod).J ⊓ bottom = ⊥`;
* `J_maximal` — *maximality*: any `𝒱`-submodule meeting the bottom trivially is `⊆ (F.ludata …).J`;
* `q_ne_zero` — the canonical lift `qCanon P ≠ 0`;
* `q_inj_on_bottom` — `qCanon P` is injective on `bottom` (its bottom component is an iso).

The three fields `q` / `q_act` / `J` of `KerJData`, and `P_irreducible`, are NOT here: they are
`qCanon P` / the gate bridge / `(F.ludata P.toAMod).J` / the irreducibility `hP` respectively.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure KerStructData (F : LUFamily W) (P : LWModule W) where
  /-- The realized bottom subspace `M(P.toAMod)_h = range (MU.incl … 0)`. -/
  bottom : Submodule ℂ (MU W P.toAMod)
  /-- The bottom is nonzero (realization). -/
  bottom_ne_bot : bottom ≠ ⊥
  /-- `(F.ludata P.toAMod).J` meets the bottom trivially. -/
  J_bottom_trivial : (F.ludata P.toAMod).J.carrier ⊓ bottom = ⊥
  /-- **Maximality:** any `𝒱`-submodule meeting the bottom trivially is `⊆ (F.ludata P.toAMod).J`. -/
  J_maximal : ∀ N : WeakModule.Submodule' (F.mudata P.toAMod).toOrdVModule.toWeakModule,
    N.carrier ⊓ bottom = ⊥ → N.carrier ≤ (F.ludata P.toAMod).J.carrier
  /-- The canonical lift is nonzero. -/
  q_ne_zero : qCanon P ≠ 0
  /-- The canonical lift is injective on the bottom (its bottom component is an iso). -/
  q_inj_on_bottom : ∀ x ∈ bottom, qCanon P x = 0 → x = 0

/-! ## The leaner per-`P` bundle: only the gate bridge + the six structural fields -/

/-- **The leaner Track-B `G'` per-`P` bundle**, carrying only the single gate bridge and the six
maximal-`J` structural fields.  Compared with `GprimePerP` (`ZhuVermaAnArchSdGprime.lean:98`) this
**drops** the opaque `kerData` and the two pins `hq`/`hJ`: they are reconstructed as terms in
`toGprimePerP`.

* `q_act_of_graded` — the gate bridge `MUGradedAction W → <`qCanon P` intertwines every mode>` (the
  SAME field as in `GprimePerP`, verbatim — the Track-A keystone, never re-proved);
* `struct` — the leaner maximal-`J` structural bundle `KerStructData F P`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure GprimeKerPerP (F : LUFamily W) (P : LWModule W) where
  /-- **The gate bridge — `q_act = MUGradedAction`** for the canonical lift `qCanon P` (verbatim the
  `GprimePerP.q_act_of_graded` field). -/
  q_act_of_graded : MUGradedAction W →
    ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
      (DirectSum.toModule ℂ ℕ P.carrier
          (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n))
          ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
        = P.isMod.toWeakModule.act u n
            ((DirectSum.toModule ℂ ℕ P.carrier
              (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n)) x)
  /-- The leaner maximal-`J` structural bundle (the six genuine DJ fields). -/
  struct : KerStructData F P

namespace GprimeKerPerP

variable {F : LUFamily W} {P : LWModule W}

/-- **`kerData` as a TERM.**  Given the single Dong–Jiang keystone `MUGradedAction W` and
irreducibility `hP`, assemble the full first-isomorphism datum `KerJData (F.mudata P.toAMod) P`:

* `q := qCanon P` (the canonical assembled lift);
* `q_act := H.q_act_of_graded hgraded` (the gate bridge fed the single keystone — no new leaf);
* `J := (F.ludata P.toAMod).J`;
* `bottom`/`bottom_ne_bot`/`J_bottom_trivial`/`J_maximal`/`q_ne_zero`/`q_inj_on_bottom` from `struct`;
* `P_irreducible := hP`.

`ker (qCanon P) = (F.ludata P.toAMod).J` is then the *derived* term `KerJData.ker_eq_J`.  No `sorry`,
**never** an axiom. -/
noncomputable def toKerJData (H : GprimeKerPerP F P) (hP : P.IsIrreducibleLW)
    (hgraded : MUGradedAction W) : KerJData (F.mudata P.toAMod) P where
  bottom := H.struct.bottom
  bottom_ne_bot := H.struct.bottom_ne_bot
  J := (F.ludata P.toAMod).J
  J_bottom_trivial := H.struct.J_bottom_trivial
  J_maximal := H.struct.J_maximal
  q := qCanon P
  q_act := H.q_act_of_graded hgraded
  q_ne_zero := H.struct.q_ne_zero
  q_inj_on_bottom := H.struct.q_inj_on_bottom
  P_irreducible := hP

/-- **`kerData`/`hq`/`hJ` discharged to terms — the SdGprime `GprimePerP F P`.**

Given the single Dong–Jiang keystone `MUGradedAction W` and irreducibility `hP`, upgrade the leaner
bundle to the full `GprimePerP F P` consumed by `GprimePerP.toGData` / `gprime_of_family`:

* `q_act_of_graded` — passed through verbatim (the SAME carried gate bridge);
* `kerData := H.toKerJData hP hgraded` (the assembled term above);
* `hq := rfl` — `kerData.q = qCanon P` is definitional (`toKerJData.q := qCanon P`, and `qCanon P`
  unfolds to exactly the `⨁ₙ layer n` that `hq` pins);
* `hJ := rfl` — `kerData.J = (F.ludata P.toAMod).J` is definitional (`toKerJData.J`).

So `kerData`/`hq`/`hJ` are TERMS, gated only on the SAME `MUGradedAction W` that already sources
`q_act_of_graded`; the carried surface is `q_act_of_graded` + the six `KerStructData` fields.  No
`sorry`, **never** an axiom. -/
noncomputable def toGprimePerP (H : GprimeKerPerP F P) (hP : P.IsIrreducibleLW)
    (hgraded : MUGradedAction W) : GprimePerP F P where
  q_act_of_graded := H.q_act_of_graded
  kerData := H.toKerJData hP hgraded
  hq := rfl
  hJ := rfl

end GprimeKerPerP

/-! ## The per-`P` family and the SdGprime `GprimeFamily` with the three leaves proved -/

/-- **A per-irreducible-`P` family of the leaner bundle.** -/
def GprimeKerFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → GprimeKerPerP F P

/-- **The SdGprime `GprimeFamily F` from the leaner family and one gate `MUGradedAction W`.**

For each irreducible `P`, the leaner bundle `H P hP` upgrades (via `toGprimePerP`) to the full
`GprimePerP F P` with `kerData`/`hq`/`hJ` as terms — gated only on the single Dong–Jiang keystone
`MUGradedAction W`, the SAME gate that already sources `q_act_of_graded`.  Feed this into
`gprime_of_family` / `sd_Gprime_of_family` (`ZhuVermaAnArchSdGprime.lean:151/167`) to obtain the
Track-B `G'` field.  No `sorry`, **never** an axiom. -/
noncomputable def gprimeKer_of_family (F : LUFamily W)
    (hgraded : MUGradedAction W) (H : GprimeKerFamily F) : GprimeFamily F :=
  fun P hP => (H P hP).toGprimePerP hP hgraded

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

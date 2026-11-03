/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VOA

/-!
# Affine (WZW) VOAs `𝒱(𝔤, k)` — the `𝔰𝔩₂` Sugawara construction  (Gannon §5.2.2, pp. 326–327)

The VOAs built from affine Kac–Moody algebras, generalising the Heisenberg VOA from abelian
`h̄` to any simple `ḡ`.  These are the chiral algebras of WZW conformal field theories.  This
file assembles the level-`k` affine `𝔰𝔩₂` VOA `𝒱(𝔰𝔩₂, k)` on the single vacuum module
`WakModule k = 𝒱(𝔰𝔩₂, k) = U(ĝ)⧸J(k)` (`Examples.AffineSl2`/`AffineSl2VOA`).

## What is assembled here (all `sorry`-free)

Re-exported from `Examples.AffineSl2VOA`:

* `AffineVOA.affineSl2VOA k hk YA … : VertexOperatorAlgebra (WakModule k)` — the affine
  `𝔰𝔩₂` VOA at level `k` (`k + 2 ≠ 0`), **assembled down to a single reconstruction input**.
  Every basis-free datum is the proved data of `AffineSl2VOA`: the `ℓ₀`-grading
  (`gradingZA_isInternal`) with finite-dimensional bounded-below pieces, the vacuum
  (`vacuumA`; nonzero by `vacuumA_ne_zero` via `pbw`, or `pbw`-free by
  `Wak.vacuumA_ne_zero_free`), CFT-type (`gradingZA_positivity`), regularity
  (`J_regularity`), locality of the generating currents (`Jfield_local`), the **Sugawara
  conformal vector** `ω = omegaA k` and the **central charge** `c = centralChargeA k`.
* `AffineVOA.centralChargeA k = 3k/(k+2) = k·dim 𝔰𝔩₂ /(k + h∨)` (Gannon (3.2.9c), with
  `dim 𝔰𝔩₂ = 3`, dual Coxeter `h∨ = 2`) — `AffineVOA.centralChargeA_eq`,
  `AffineVOA.affineSl2_central_charge`.

## The reconstruction input (supplied)

The complete instance is `AffineVOA.affineSl2VOA_closed k hk` (`Examples.AffineSl2Virasoro`),
which feeds the reconstructed vertex map `YA k hk` and its proved axioms into the shell below.
The paragraph that follows is the original design note.

`WakModule k = U(ĝ)⧸J(k)` is a *cyclic quotient* module, not a free `Finsupp`-based Fock
space (the Heisenberg recipe assembles `Y` as `Finsupp.linearCombination` over the monomial
basis — unavailable here, since `PBWPrinciple` exposes affine-vacuum nonvanishing and generic
relative-induction bottom injectivity, not a free creation-monomial basis). Building the all-states vertex map
`YA : WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k))` from the generating local currents
`Jfield k a` therefore needs the **module-polymorphic reconstruction theorem** — build `Y` on a
cyclic module from a generating family of mutually local fields (Kac §4.5; FLM §8.5).  The
instance `affineSl2VOA` consumes exactly that `YA` and its seven `YA`-dependent axioms (VA1–VA5
mode-grading/vacuum/creation/locality/regularity, VOA1–3 Virasoro/`L₀`/translation), and
discharges every other field.  The reconstruction was later supplied (here by
`affineSl2VOA_closed`; for general-`c` Virasoro by `VirModule.virasoroVOA`).

## Dependencies
* `VOA.Examples.AffineSl2VOA` (the assembled instance shell and conformal datum),
  `VOA.Foundations.AffineLie` (the vacuum module, transitively).

## Status
This file re-exports the shell `affineSl2VOA` and the central charge `3k/(k+2)`.  The
complete instance on the level-`k` vacuum module is `AffineVOA.affineSl2VOA_closed k hk`
(`Examples.AffineSl2Virasoro`).

## References
* Gannon §5.2.2, eq. (5.2.6); Sugawara; Frenkel–Zhu; Kac §10, §4.5; Lepowsky–Li Ch. 6.
-/

namespace VOA

/-! ## Re-exported main facts

`AffineVOA.affineSl2VOA` and `AffineVOA.centralChargeA` are defined in `Examples.AffineSl2VOA`;
we restate the two main facts at the `VOA` namespace level. -/

/-- **The dual-Coxeter central charge of the affine `𝔰𝔩₂` VOA is `3k/(k+2)`** (Gannon
(3.2.9c), `c = k·dim 𝔤/(k+h∨)` with `dim 𝔰𝔩₂ = 3`, `h∨ = 2`). -/
theorem affineSl2VOA_centralCharge (k : ℂ) :
    AffineVOA.centralChargeA k = 3 * k / (k + 2) :=
  AffineVOA.centralChargeA_eq k

end VOA

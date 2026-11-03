/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Strong
import VOA.Examples.WakimotoEightFifths
import VOA.Examples.AffineSimpleQuotient

/-!
# `V^{-8/5}(𝔰𝔩₂)` is **not simple**, and `L_{-8/5}(𝔰𝔩₂)` is a **proper** quotient

This is the first place in the library where a universal affine vertex operator algebra is
shown to be non-simple **unconditionally** — no PBW input, no unestablished independence
hypothesis, no `sorry`.

## The chain

Three separate pieces meet here:

1. `Sl2Sing85.sl2Singular85_pos` — the explicit weight-`5`, charge-`+2` vector `s` of
   `V^{-8/5}(𝔰𝔩₂)` is annihilated by every current mode `Jᵃₘ` with `m ≥ 1`
   (`Examples/AffineSl2Singular85`).
2. `WakLY.sl2Singular85_ne_zero` — `s ≠ 0`, proved on the Wakimoto free-field side
   (`Examples/WakimotoEightFifths`), which is where the nonvanishing becomes unconditional.
3. `AffineVOA.Strong.strongly_singular_of_SingP` and `AffineVOA.Strong.affineSl2_qp`
   (`Examples/AffineSl2Strong`) — the two structural upgrades: positive current modes ⟹ all
   non-weight-raising modes of all states, and quasi-primarity of `𝒱₁`.

Feeding these into `SingVec.not_isSimple_of_stronglySingular_FHL` (`Core/SingularVector`) —
which runs through the **right radical of the canonical normalised fully invariant form**,
i.e. Li's theorem in `Core/InvariantFormRadical` — gives `not_isSimple_85`.

## ⚠ Properness of `(s)` without the PBW factorisation

The standard argument for properness of the ideal `(s)` factors
`U(𝔰𝔩₂^) = U(𝔫₋)U(𝔤₀)U(𝔫₊)`, a PBW input that this route avoids
(compare `Examples/WakimotoEightFifths`, §8): the FHL right-radical route needs no PBW at all — a strongly singular vector
pairs to zero against all of `𝒱` under the invariant form, so `𝟙` cannot lie in `(s)`.  The
§8 preamble has been corrected accordingly.

## Axiom status

Every declaration below is `#print axioms`-clean, `[propext, Classical.choice, Quot.sound]`,
and in particular **`VOA.pbw`-free**.  The one trap: `Inst.closed_vacuum_ne_zero`
(`Examples/AffineSl2VOAInstance`) *does* consume `pbw` and is type-correct for the `hne` slot;
`vacuum85_ne_zero` below routes through `WakLY.vacuumA85_ne_zero` instead.
-/

namespace VOA.Sl2NotSimple85

open VOA VOA.AffineVOA VOA.AffineVOA.Inst
open VOA.AffineVOA.Strong VOA.WakLY VOA.Sl2Sing85

/-- The singular vector `s` of `V^{-8/5}(𝔰𝔩₂)` is killed by every positive current mode. -/
theorem singP85 : SingP (-8 / 5 : ℂ) sl2Singular85 := fun a _ hi => sl2Singular85_pos a hi

/-- `s` is **strongly singular** of weight `5`: *every* non-weight-raising mode of *every*
state annihilates it. -/
theorem stronglySingular85 :
    SingVec.IsStronglySingularOfWeight (affineSl2VOA_closed (-8 / 5 : ℂ) hk85) 5 sl2Singular85 :=
  isStronglySingular_of_SingP (-8 / 5 : ℂ) hk85 singP85 sl2Singular85_ne_zero (by norm_num)
    sl2Singular85_mem

/-- The vacuum of `V^{-8/5}(𝔰𝔩₂)` is nonzero — via the Wakimoto free-field realisation, which
is `pbw`-free (unlike `Inst.closed_vacuum_ne_zero`). -/
theorem vacuum85_ne_zero : (affineSl2VOA_closed (-8 / 5 : ℂ) hk85).vacuum ≠ 0 :=
  vacuumA85_ne_zero

/-- Weight-one states of `V^{-8/5}(𝔰𝔩₂)` are quasi-primary. -/
theorem qp85 : ∀ v, v ∈ (affineSl2VOA_closed (-8 / 5 : ℂ) hk85).grading 1 →
    (affineSl2VOA_closed (-8 / 5 : ℂ) hk85).L 1 v = 0 :=
  affineSl2_qp (-8 / 5 : ℂ) hk85

/-- **M1: the universal affine VOA `V^{-8/5}(𝔰𝔩₂)` is not simple.**  Unconditional:
no `pbw`, no open hypothesis. -/
theorem not_isSimple_85 : ¬ (affineSl2VOA_closed (-8 / 5 : ℂ) hk85).IsSimple :=
  SingVec.not_isSimple_of_stronglySingular_FHL vacuum85_ne_zero qp85 stronglySingular85

/-! ## The quotient-side consequences

These are the statements the rigidity programme actually consumes: not merely "`V^{-8/5}` is
not simple", but "`s` dies in `L_{-8/5}(𝔰𝔩₂)`, whose defining ideal is therefore nonzero".
All three are immediate from `Examples/AffineSimpleQuotient`, §3. -/

/-- `s` lies in the maximal graded ideal. -/
theorem mem_maxGradedIdeal_85 :
    sl2Singular85 ∈ QuotVOA.maxGradedIdeal (affineSl2VOA_closed (-8 / 5 : ℂ) hk85) :=
  SimpleQuot.mem_maxGradedIdeal_of_stronglySingular vacuum85_ne_zero qp85 stronglySingular85

/-- `s ↦ 0` in the simple quotient `L_{-8/5}(𝔰𝔩₂)`. -/
theorem mkQ_sl2Singular85_eq_zero :
    (QuotVOA.maxGradedIdeal (affineSl2VOA_closed (-8 / 5 : ℂ) hk85)).mkQ sl2Singular85 = 0 :=
  SimpleQuot.mkQ_eq_zero_of_stronglySingular vacuum85_ne_zero qp85 stronglySingular85

/-- The maximal graded ideal of `V^{-8/5}(𝔰𝔩₂)` is nonzero. -/
theorem maxGradedIdeal_85_ne_bot :
    QuotVOA.maxGradedIdeal (affineSl2VOA_closed (-8 / 5 : ℂ) hk85) ≠ ⊥ :=
  SimpleQuot.maxGradedIdeal_ne_bot_of_stronglySingular vacuum85_ne_zero qp85 stronglySingular85

/-- `L_{-8/5}(𝔰𝔩₂)` is a **proper** quotient of `V^{-8/5}(𝔰𝔩₂)`: the projection is not
injective. -/
theorem mkQ_85_not_injective :
    ¬ Function.Injective
      (QuotVOA.maxGradedIdeal (affineSl2VOA_closed (-8 / 5 : ℂ) hk85)).mkQ :=
  SimpleQuot.mkQ_not_injective_of_stronglySingular vacuum85_ne_zero qp85 stronglySingular85

end VOA.Sl2NotSimple85

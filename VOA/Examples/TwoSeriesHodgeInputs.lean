/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeHarmonic
import VOA.Examples.LevelOneUnitaryPositivity

/-!
# The BRST/Hodge package for every coset level datum

The level-generic port of the Lee–Yang chain (`TwoSeriesHodgeGeometry`, `TwoSeriesHodgeGood`,
`TwoSeriesHodgeGoodness`, `TwoSeriesHodgeKahler`, `TwoSeriesHodgeBG`, `TwoSeriesHodgeGhostConj`,
`TwoSeriesHodgeConjIdentity`, `TwoSeriesHodgeHarmonic`) discharges the hypothesis `hodge` of the
general coset-transfer theorem for **every** `L : CosetLevels`:

* `endpointKahler L hA : BRSTKahlerGeometry L` — the concrete Beem–Garner Kähler geometry on the
  actual level-`L` relative complexes (standard ghost grading, colour-weighted ghost form, the
  corrected Beem–Garner package with both BRST conjugation identities proved);
* `brstHodgeInputs L hA : BRSTHodgeInputs L` — all seven fields proved;
* `cosetLevels_gradedUnitary_of_affine_hodgeFree` — `hA ∧ SqueezeInput ⇒ VirGradedUnitary L.c`;
* `twoSeries_gradedUnitary_of_affine_hodgeFree` — the `(2, 2n+3)` specialization.

The only inputs left are `hA` (graded unitarity of `L_k(sl₂)`) and the dimension squeeze input.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge GradedUnitaryCohomology VirGradedUnitarity

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

private abbrev endpointPkg
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :=
  (bgGhostRemainderI L hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg
    LevelOneUnitary.bUnitary

/-- The concrete Beem–Garner Kähler geometry on the level-`L` relative complexes. -/
abbrev endpointKahler
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    BRSTKahlerGeometry L :=
  sp2Kahler L hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd (endpointPkg L hA).sp2

/-- **The BRST/Hodge package at every level datum**, from `hA` alone. -/
def brstHodgeInputs
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    BRSTHodgeInputs L where
  kahler := endpointKahler L hA
  weakGU := concreteKahler_weakGU LevelOneUnitary.bUnitary bgPG_pos _
  gu := sp2GUData0 L hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd
    (endpointPkg L hA).sp2 (endpointPkg L hA).conj0
  generators hp :=
    have h := interpretedGenerators_std L bgGh hA LevelOneUnitary.bUnitary bgPG_pos _ _ _
      bgGh_isStd hp
    ⟨h.vacuum, h.creation⟩
  vacuumNormalized hp := harmonicVacuumNormalized_proved L hA LevelOneUnitary.bUnitary hp
  creationAdjoint i n m hpn hpm x y hx hy :=
    harmonicCreationAdjoint_proved L hA LevelOneUnitary.bUnitary i n m hpn hpm x y hx hy
  wordsReal n hp w hw := harmonicWordsReal_proved L hA LevelOneUnitary.bUnitary n hp w hw

/-- **Coset transfer for any level datum, with the Hodge package discharged.** Graded unitarity
of `L_{kA}(sl₂)` and the dimension squeeze input for the concrete Kähler geometry imply graded
unitarity of the simple Virasoro VOA `L(c)`. -/
theorem cosetLevels_gradedUnitary_of_affine_hodgeFree
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hsq : SqueezeInput L (brstHodgeInputs L hA).kahler) :
    VirGradedUnitary L.c (targetRealStructure L) :=
  cosetLevels_gradedUnitary_of_affine L hA (brstHodgeInputs L hA) hsq

/-- **The `(2, 2n+3)` series, with the Hodge package discharged.** For `k = -2 + 2/(2n+1)`:
graded unitarity of `L_k(sl₂)` and the dimension squeeze input imply graded unitarity of the
minimal model `M(2, 2n+3)`, of central charge
`(twoSeriesLevels n).c = boundaryCharge (n+1) = 1 - 3(2n+1)²/(2n+3)` (`twoSeriesLevels_c`). -/
theorem twoSeries_gradedUnitary_of_affine_hodgeFree (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (hsq : SqueezeInput (twoSeriesLevels n) (brstHodgeInputs (twoSeriesLevels n) hA).kahler) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  cosetLevels_gradedUnitary_of_affine_hodgeFree (twoSeriesLevels n) hA hsq

end

end VOA.TwoSeries

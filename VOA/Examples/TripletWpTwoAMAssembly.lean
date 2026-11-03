/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMSchur
import VOA.Examples.TripletWpTwoVirasoroCoords

/-!
# Final assembly of the `p = 2` Adamovic--Milas identity

This file compares the independently evaluated screened state, normal product, and twelve
background-charge Virasoro coordinates.  It is separate from the evaluator implementations so
that the final coefficient comparison remains an auditable consumer.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpTwoAMAssembly

open scoped BigOperators TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2
open VOA.LatGen.WpTwoAMSchur
open VOA.LatGen.WpTwoVirasoroCoords

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private abbrev alphaTwo : Ltwo.carrier := alphaP 2

/-- An assembly-side copy of the independently evaluated normal-product coordinates.  Keeping
this literal list outside the evaluator makes accidental self-rewriting visible. -/
noncomputable def hProductExpectedAssembly : APolyTwo :=
  [(1 / 12, [0, 0, 0, 1, 1, 2]),
   (1 / 4, [0, 1, 1, 1, 2]),
   (1 / 12, [0, 0, 0, 0, 2, 2]),
   (1 / 4, [0, 0, 1, 2, 2]),
   (1 / 6, [1, 1, 2, 2]),
   (1 / 6, [0, 2, 2, 2]),
   (1 / 6, [0, 0, 0, 0, 1, 3]),
   (1 / 2, [0, 0, 1, 1, 3]),
   (5 / 12, [0, 0, 0, 2, 3]),
   (19 / 12, [0, 1, 2, 3]),
   (5 / 6, [2, 2, 3]),
   (1, [0, 0, 3, 3]),
   (1, [1, 3, 3]),
   (1 / 12, [0, 0, 0, 0, 0, 4]),
   (2 / 3, [0, 0, 0, 1, 4]),
   (5 / 4, [0, 1, 1, 4]),
   (13 / 6, [0, 0, 2, 4]),
   (17 / 6, [1, 2, 4]),
   (4, [0, 3, 4]),
   (2, [4, 4]),
   (5 / 12, [0, 0, 0, 0, 5]),
   (13 / 4, [0, 0, 1, 5]),
   (2, [1, 1, 5]),
   (29 / 6, [0, 2, 5]),
   (4, [3, 5]),
   (17 / 6, [0, 0, 0, 6]),
   (17 / 2, [0, 1, 6]),
   (17 / 3, [2, 6]),
   (9, [0, 0, 7]),
   (9, [1, 7]),
   (22, [0, 8]),
   (26, [9])]

noncomputable def schur3Ledger : APolyTwo :=
  [((1 / 3 : ℂ), [2]),
   ((1 / 2 : ℂ), [0, 1]),
   ((1 / 6 : ℂ), [0, 0, 0])]

noncomputable def schur4Ledger : APolyTwo :=
  [((1 / 4 : ℂ), [3]),
   ((1 / 3 : ℂ), [0, 2]),
   ((1 / 8 : ℂ), [1, 1]),
   ((1 / 4 : ℂ), [0, 0, 1]),
   ((1 / 24 : ℂ), [0, 0, 0, 0])]

noncomputable def schur5Ledger : APolyTwo :=
  [((1 / 5 : ℂ), [4]),
   ((1 / 4 : ℂ), [0, 3]),
   ((1 / 6 : ℂ), [1, 2]),
   ((1 / 6 : ℂ), [0, 0, 2]),
   ((1 / 8 : ℂ), [0, 1, 1]),
   ((1 / 12 : ℂ), [0, 0, 0, 1]),
   ((1 / 120 : ℂ), [0, 0, 0, 0, 0])]

noncomputable def schur6Ledger : APolyTwo :=
  [((1 / 6 : ℂ), [5]),
   ((1 / 5 : ℂ), [0, 4]),
   ((1 / 8 : ℂ), [1, 3]),
   ((1 / 18 : ℂ), [2, 2]),
   ((1 / 8 : ℂ), [0, 0, 3]),
   ((1 / 6 : ℂ), [0, 1, 2]),
   ((1 / 48 : ℂ), [1, 1, 1]),
   ((1 / 18 : ℂ), [0, 0, 0, 2]),
   ((1 / 16 : ℂ), [0, 0, 1, 1]),
   ((1 / 48 : ℂ), [0, 0, 0, 0, 1]),
   ((1 / 720 : ℂ), [0, 0, 0, 0, 0, 0])]

noncomputable def schur7Ledger : APolyTwo :=
  [((1 / 7 : ℂ), [6]),
   ((1 / 6 : ℂ), [0, 5]),
   ((1 / 10 : ℂ), [1, 4]),
   ((1 / 12 : ℂ), [2, 3]),
   ((1 / 10 : ℂ), [0, 0, 4]),
   ((1 / 8 : ℂ), [0, 1, 3]),
   ((1 / 18 : ℂ), [0, 2, 2]),
   ((1 / 24 : ℂ), [1, 1, 2]),
   ((1 / 24 : ℂ), [0, 0, 0, 3]),
   ((1 / 12 : ℂ), [0, 0, 1, 2]),
   ((1 / 48 : ℂ), [0, 1, 1, 1]),
   ((1 / 72 : ℂ), [0, 0, 0, 0, 2]),
   ((1 / 48 : ℂ), [0, 0, 0, 1, 1]),
   ((1 / 240 : ℂ), [0, 0, 0, 0, 0, 1]),
   ((1 / 5040 : ℂ), [0, 0, 0, 0, 0, 0, 0])]

noncomputable def screenedLedger : APolyTwo :=
  [((2 / 21 : ℂ), [2, 6]),
   ((-1 / 3 : ℂ), [3, 5]),
   ((6 / 25 : ℂ), [4, 4]),
   ((1 / 7 : ℂ), [0, 1, 6]),
   ((-1 / 3 : ℂ), [0, 2, 5]),
   ((1 / 5 : ℂ), [0, 3, 4]),
   ((-1 / 6 : ℂ), [1, 1, 5]),
   ((7 / 15 : ℂ), [1, 2, 4]),
   ((-1 / 4 : ℂ), [1, 3, 3]),
   ((-1 / 18 : ℂ), [2, 2, 3]),
   ((1 / 21 : ℂ), [0, 0, 0, 6]),
   ((-1 / 6 : ℂ), [0, 0, 1, 5]),
   ((-1 / 15 : ℂ), [0, 0, 2, 4]),
   ((1 / 8 : ℂ), [0, 0, 3, 3]),
   ((1 / 5 : ℂ), [0, 1, 1, 4]),
   ((-1 / 9 : ℂ), [0, 2, 2, 2]),
   ((-1 / 6 : ℂ), [1, 1, 1, 3]),
   ((5 / 36 : ℂ), [1, 1, 2, 2]),
   ((-1 / 15 : ℂ), [0, 0, 0, 1, 4]),
   ((1 / 9 : ℂ), [0, 0, 0, 2, 3]),
   ((-1 / 9 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 12 : ℂ), [0, 1, 1, 1, 2]),
   ((-1 / 48 : ℂ), [1, 1, 1, 1, 1]),
   ((-1 / 75 : ℂ), [0, 0, 0, 0, 0, 4]),
   ((1 / 36 : ℂ), [0, 0, 0, 0, 2, 2]),
   ((-1 / 36 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((1 / 96 : ℂ), [0, 0, 1, 1, 1, 1]),
   ((-1 / 180 : ℂ), [0, 0, 0, 0, 0, 0, 3]),
   ((1 / 180 : ℂ), [0, 0, 0, 0, 0, 1, 2]),
   ((-1 / 1260 : ℂ), [0, 0, 0, 0, 0, 0, 0, 2]),
   ((1 / 720 : ℂ), [0, 0, 0, 0, 0, 0, 1, 1]),
   ((1 / 5040 : ℂ), [0, 0, 0, 0, 0, 0, 0, 0, 1]),
   ((1 / 50400 : ℂ), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]

noncomputable def v2Ledger : APolyTwo :=
  [((1 / 4 : ℂ), [1]),
   ((1 / 8 : ℂ), [0, 0])]

noncomputable def v3Ledger : APolyTwo :=
  [((1 / 2 : ℂ), [2]),
   ((1 / 4 : ℂ), [0, 1])]

noncomputable def v4Ledger : APolyTwo :=
  [((3 / 4 : ℂ), [3]),
   ((1 / 4 : ℂ), [0, 2]),
   ((1 / 8 : ℂ), [1, 1])]

noncomputable def v5Ledger : APolyTwo :=
  [((1 : ℂ), [4]),
   ((1 / 4 : ℂ), [0, 3]),
   ((1 / 4 : ℂ), [1, 2])]

noncomputable def v10Ledger : APolyTwo :=
  [((9 / 4 : ℂ), [9]),
   ((1 / 4 : ℂ), [0, 8]),
   ((1 / 4 : ℂ), [1, 7]),
   ((1 / 4 : ℂ), [2, 6]),
   ((1 / 4 : ℂ), [3, 5]),
   ((1 / 8 : ℂ), [4, 4])]

noncomputable def v22Ledger : APolyTwo :=
  [((1 / 2 : ℂ), [3]),
   ((1 / 4 : ℂ), [0, 2]),
   ((1 / 16 : ℂ), [1, 1]),
   ((1 / 16 : ℂ), [0, 0, 1]),
   ((1 / 64 : ℂ), [0, 0, 0, 0])]

noncomputable def v32Ledger : APolyTwo :=
  [((1 / 2 : ℂ), [4]),
   ((1 / 4 : ℂ), [0, 3]),
   ((1 / 8 : ℂ), [1, 2]),
   ((1 / 16 : ℂ), [0, 0, 2]),
   ((1 / 16 : ℂ), [0, 1, 1]),
   ((1 / 32 : ℂ), [0, 0, 0, 1])]

noncomputable def v42Ledger : APolyTwo :=
  [((1 / 2 : ℂ), [5]),
   ((1 / 4 : ℂ), [0, 4]),
   ((3 / 16 : ℂ), [1, 3]),
   ((3 / 32 : ℂ), [0, 0, 3]),
   ((1 / 16 : ℂ), [0, 1, 2]),
   ((1 / 32 : ℂ), [1, 1, 1]),
   ((1 / 32 : ℂ), [0, 0, 0, 2]),
   ((1 / 64 : ℂ), [0, 0, 1, 1])]

noncomputable def v33Ledger : APolyTwo :=
  [((3 / 2 : ℂ), [5]),
   ((1 / 2 : ℂ), [0, 4]),
   ((1 / 4 : ℂ), [1, 3]),
   ((1 / 4 : ℂ), [2, 2]),
   ((1 / 4 : ℂ), [0, 1, 2]),
   ((1 / 16 : ℂ), [0, 0, 1, 1])]

noncomputable def v222Ledger : APolyTwo :=
  [((2 : ℂ), [5]),
   ((3 / 4 : ℂ), [0, 4]),
   ((3 / 8 : ℂ), [1, 3]),
   ((1 / 4 : ℂ), [2, 2]),
   ((3 / 16 : ℂ), [0, 0, 3]),
   ((3 / 16 : ℂ), [0, 1, 2]),
   ((1 / 64 : ℂ), [1, 1, 1]),
   ((3 / 32 : ℂ), [0, 0, 0, 2]),
   ((3 / 128 : ℂ), [0, 0, 1, 1]),
   ((3 / 256 : ℂ), [0, 0, 0, 0, 1]),
   ((1 / 512 : ℂ), [0, 0, 0, 0, 0, 0])]

noncomputable def v322Ledger : APolyTwo :=
  [((2 : ℂ), [6]),
   ((3 / 4 : ℂ), [0, 5]),
   ((1 / 4 : ℂ), [1, 4]),
   ((1 / 2 : ℂ), [2, 3]),
   ((1 / 8 : ℂ), [0, 0, 4]),
   ((1 / 4 : ℂ), [0, 1, 3]),
   ((1 / 8 : ℂ), [0, 2, 2]),
   ((1 / 32 : ℂ), [1, 1, 2]),
   ((1 / 16 : ℂ), [0, 0, 0, 3]),
   ((3 / 32 : ℂ), [0, 0, 1, 2]),
   ((1 / 64 : ℂ), [0, 1, 1, 1]),
   ((1 / 128 : ℂ), [0, 0, 0, 0, 2]),
   ((1 / 64 : ℂ), [0, 0, 0, 1, 1]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 0, 1])]

noncomputable def v2222Ledger : APolyTwo :=
  [((12 : ℂ), [7]),
   ((15 / 4 : ℂ), [0, 6]),
   ((2 : ℂ), [1, 5]),
   ((9 / 4 : ℂ), [2, 4]),
   ((3 / 4 : ℂ), [3, 3]),
   ((1 : ℂ), [0, 0, 5]),
   ((3 / 4 : ℂ), [0, 1, 4]),
   ((3 / 4 : ℂ), [0, 2, 3]),
   ((3 / 16 : ℂ), [1, 1, 3]),
   ((1 / 4 : ℂ), [1, 2, 2]),
   ((3 / 8 : ℂ), [0, 0, 0, 4]),
   ((3 / 16 : ℂ), [0, 0, 1, 3]),
   ((5 / 16 : ℂ), [0, 0, 2, 2]),
   ((3 / 32 : ℂ), [0, 1, 1, 2]),
   ((1 / 256 : ℂ), [1, 1, 1, 1]),
   ((3 / 64 : ℂ), [0, 0, 0, 0, 3]),
   ((3 / 32 : ℂ), [0, 0, 0, 1, 2]),
   ((1 / 128 : ℂ), [0, 0, 1, 1, 1]),
   ((3 / 128 : ℂ), [0, 0, 0, 0, 0, 2]),
   ((3 / 512 : ℂ), [0, 0, 0, 0, 1, 1]),
   ((1 / 512 : ℂ), [0, 0, 0, 0, 0, 0, 1]),
   ((1 / 4096 : ℂ), [0, 0, 0, 0, 0, 0, 0, 0])]

noncomputable def v22222Ledger : APolyTwo :=
  [((96 : ℂ), [9]),
   ((105 / 4 : ℂ), [0, 8]),
   ((15 : ℂ), [1, 7]),
   ((15 : ℂ), [2, 6]),
   ((10 : ℂ), [3, 5]),
   ((27 / 4 : ℂ), [4, 4]),
   ((15 / 2 : ℂ), [0, 0, 7]),
   ((75 / 16 : ℂ), [0, 1, 6]),
   ((5 : ℂ), [0, 2, 5]),
   ((15 / 4 : ℂ), [0, 3, 4]),
   ((5 / 4 : ℂ), [1, 1, 5]),
   ((45 / 16 : ℂ), [1, 2, 4]),
   ((15 / 16 : ℂ), [1, 3, 3]),
   ((5 / 4 : ℂ), [2, 2, 3]),
   ((75 / 32 : ℂ), [0, 0, 0, 6]),
   ((5 / 4 : ℂ), [0, 0, 1, 5]),
   ((105 / 32 : ℂ), [0, 0, 2, 4]),
   ((15 / 32 : ℂ), [0, 0, 3, 3]),
   ((15 / 32 : ℂ), [0, 1, 1, 4]),
   ((15 / 16 : ℂ), [0, 1, 2, 3]),
   ((5 / 8 : ℂ), [0, 2, 2, 2]),
   ((5 / 64 : ℂ), [1, 1, 1, 3]),
   ((5 / 32 : ℂ), [1, 1, 2, 2]),
   ((5 / 16 : ℂ), [0, 0, 0, 0, 5]),
   ((15 / 32 : ℂ), [0, 0, 0, 1, 4]),
   ((15 / 32 : ℂ), [0, 0, 0, 2, 3]),
   ((15 / 128 : ℂ), [0, 0, 1, 1, 3]),
   ((25 / 64 : ℂ), [0, 0, 1, 2, 2]),
   ((5 / 128 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 1024 : ℂ), [1, 1, 1, 1, 1]),
   ((15 / 128 : ℂ), [0, 0, 0, 0, 0, 4]),
   ((15 / 256 : ℂ), [0, 0, 0, 0, 1, 3]),
   ((5 / 32 : ℂ), [0, 0, 0, 0, 2, 2]),
   ((15 / 256 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((5 / 2048 : ℂ), [0, 0, 1, 1, 1, 1]),
   ((5 / 512 : ℂ), [0, 0, 0, 0, 0, 0, 3]),
   ((15 / 512 : ℂ), [0, 0, 0, 0, 0, 1, 2]),
   ((5 / 2048 : ℂ), [0, 0, 0, 0, 1, 1, 1]),
   ((5 / 1024 : ℂ), [0, 0, 0, 0, 0, 0, 0, 2]),
   ((5 / 4096 : ℂ), [0, 0, 0, 0, 0, 0, 1, 1]),
   ((5 / 16384 : ℂ), [0, 0, 0, 0, 0, 0, 0, 0, 1]),
   ((1 / 32768 : ℂ), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]

noncomputable def v82Ledger : APolyTwo :=
  [((1 / 2 : ℂ), [9]),
   ((1 / 4 : ℂ), [0, 8]),
   ((7 / 16 : ℂ), [1, 7]),
   ((7 / 32 : ℂ), [0, 0, 7]),
   ((1 / 16 : ℂ), [0, 1, 6]),
   ((1 / 16 : ℂ), [1, 1, 5]),
   ((1 / 16 : ℂ), [1, 2, 4]),
   ((1 / 32 : ℂ), [1, 3, 3]),
   ((1 / 32 : ℂ), [0, 0, 0, 6]),
   ((1 / 32 : ℂ), [0, 0, 1, 5]),
   ((1 / 32 : ℂ), [0, 0, 2, 4]),
   ((1 / 64 : ℂ), [0, 0, 3, 3])]

noncomputable def v73Ledger : APolyTwo :=
  [((3 / 2 : ℂ), [9]),
   ((1 / 2 : ℂ), [0, 8]),
   ((1 / 4 : ℂ), [1, 7]),
   ((3 / 4 : ℂ), [2, 6]),
   ((3 / 8 : ℂ), [0, 1, 6]),
   ((1 / 8 : ℂ), [0, 2, 5]),
   ((1 / 8 : ℂ), [1, 2, 4]),
   ((1 / 8 : ℂ), [2, 2, 3]),
   ((1 / 16 : ℂ), [0, 0, 1, 5]),
   ((1 / 16 : ℂ), [0, 1, 1, 4]),
   ((1 / 16 : ℂ), [0, 1, 2, 3])]

noncomputable def v64Ledger : APolyTwo :=
  [((3 : ℂ), [9]),
   ((3 / 4 : ℂ), [0, 8]),
   ((1 / 2 : ℂ), [1, 7]),
   ((1 / 4 : ℂ), [2, 6]),
   ((15 / 16 : ℂ), [3, 5]),
   ((5 / 16 : ℂ), [0, 2, 5]),
   ((3 / 16 : ℂ), [0, 3, 4]),
   ((5 / 32 : ℂ), [1, 1, 5]),
   ((3 / 16 : ℂ), [1, 3, 3]),
   ((3 / 32 : ℂ), [2, 2, 3]),
   ((1 / 16 : ℂ), [0, 0, 2, 4]),
   ((1 / 32 : ℂ), [0, 1, 1, 4]),
   ((1 / 16 : ℂ), [0, 1, 2, 3]),
   ((1 / 32 : ℂ), [0, 2, 2, 2]),
   ((1 / 32 : ℂ), [1, 1, 1, 3]),
   ((1 / 64 : ℂ), [1, 1, 2, 2])]

noncomputable def v622Ledger : APolyTwo :=
  [((2 : ℂ), [9]),
   ((3 / 4 : ℂ), [0, 8]),
   ((1 / 4 : ℂ), [1, 7]),
   ((1 / 4 : ℂ), [2, 6]),
   ((5 / 8 : ℂ), [3, 5]),
   ((1 / 8 : ℂ), [0, 0, 7]),
   ((1 / 8 : ℂ), [0, 1, 6]),
   ((5 / 16 : ℂ), [0, 2, 5]),
   ((1 / 8 : ℂ), [0, 3, 4]),
   ((5 / 64 : ℂ), [1, 1, 5]),
   ((1 / 8 : ℂ), [1, 3, 3]),
   ((1 / 16 : ℂ), [2, 2, 3]),
   ((1 / 16 : ℂ), [0, 0, 0, 6]),
   ((5 / 64 : ℂ), [0, 0, 1, 5]),
   ((1 / 16 : ℂ), [0, 0, 2, 4]),
   ((1 / 64 : ℂ), [0, 1, 1, 4]),
   ((1 / 16 : ℂ), [0, 1, 2, 3]),
   ((1 / 32 : ℂ), [0, 2, 2, 2]),
   ((1 / 64 : ℂ), [1, 1, 1, 3]),
   ((1 / 128 : ℂ), [1, 1, 2, 2]),
   ((5 / 256 : ℂ), [0, 0, 0, 0, 5]),
   ((1 / 64 : ℂ), [0, 0, 0, 1, 4]),
   ((1 / 64 : ℂ), [0, 0, 1, 1, 3]),
   ((1 / 128 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 0, 4]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 1, 3]),
   ((1 / 512 : ℂ), [0, 0, 0, 0, 2, 2])]

noncomputable def v55Ledger : APolyTwo :=
  [((5 : ℂ), [9]),
   ((1 : ℂ), [0, 8]),
   ((3 / 4 : ℂ), [1, 7]),
   ((1 / 2 : ℂ), [2, 6]),
   ((1 / 4 : ℂ), [3, 5]),
   ((1 : ℂ), [4, 4]),
   ((1 / 2 : ℂ), [0, 3, 4]),
   ((1 / 2 : ℂ), [1, 2, 4]),
   ((1 / 16 : ℂ), [0, 0, 3, 3]),
   ((1 / 8 : ℂ), [0, 1, 2, 3]),
   ((1 / 16 : ℂ), [1, 1, 2, 2])]

noncomputable def v532Ledger : APolyTwo :=
  [((5 / 2 : ℂ), [9]),
   ((1 : ℂ), [0, 8]),
   ((3 / 8 : ℂ), [1, 7]),
   ((1 / 4 : ℂ), [2, 6]),
   ((1 / 4 : ℂ), [3, 5]),
   ((1 / 2 : ℂ), [4, 4]),
   ((3 / 16 : ℂ), [0, 0, 7]),
   ((1 / 4 : ℂ), [0, 1, 6]),
   ((1 / 8 : ℂ), [0, 2, 5]),
   ((3 / 8 : ℂ), [0, 3, 4]),
   ((1 / 16 : ℂ), [1, 1, 5]),
   ((1 / 4 : ℂ), [1, 2, 4]),
   ((1 / 16 : ℂ), [0, 0, 0, 6]),
   ((3 / 32 : ℂ), [0, 0, 1, 5]),
   ((1 / 16 : ℂ), [0, 0, 2, 4]),
   ((1 / 16 : ℂ), [0, 0, 3, 3]),
   ((1 / 16 : ℂ), [0, 1, 1, 4]),
   ((3 / 32 : ℂ), [0, 1, 2, 3]),
   ((1 / 32 : ℂ), [1, 1, 2, 2]),
   ((1 / 32 : ℂ), [0, 0, 0, 1, 4]),
   ((1 / 64 : ℂ), [0, 0, 0, 2, 3]),
   ((1 / 64 : ℂ), [0, 0, 1, 1, 3]),
   ((1 / 64 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 64 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 128 : ℂ), [0, 0, 0, 0, 1, 3]),
   ((1 / 128 : ℂ), [0, 0, 0, 1, 1, 2])]

noncomputable def v442Ledger : APolyTwo :=
  [((3 : ℂ), [9]),
   ((5 / 4 : ℂ), [0, 8]),
   ((3 / 4 : ℂ), [1, 7]),
   ((3 / 4 : ℂ), [3, 5]),
   ((1 / 4 : ℂ), [4, 4]),
   ((3 / 8 : ℂ), [0, 0, 7]),
   ((3 / 16 : ℂ), [0, 1, 6]),
   ((1 / 4 : ℂ), [0, 2, 5]),
   ((3 / 8 : ℂ), [0, 3, 4]),
   ((1 / 4 : ℂ), [1, 1, 5]),
   ((1 / 16 : ℂ), [1, 2, 4]),
   ((9 / 64 : ℂ), [1, 3, 3]),
   ((3 / 32 : ℂ), [0, 0, 0, 6]),
   ((1 / 16 : ℂ), [0, 0, 1, 5]),
   ((5 / 32 : ℂ), [0, 0, 2, 4]),
   ((9 / 128 : ℂ), [0, 0, 3, 3]),
   ((1 / 16 : ℂ), [0, 1, 1, 4]),
   ((3 / 32 : ℂ), [0, 1, 2, 3]),
   ((3 / 64 : ℂ), [1, 1, 1, 3]),
   ((3 / 64 : ℂ), [0, 0, 0, 2, 3]),
   ((3 / 128 : ℂ), [0, 0, 1, 1, 3]),
   ((1 / 64 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 64 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 256 : ℂ), [1, 1, 1, 1, 1]),
   ((1 / 128 : ℂ), [0, 0, 0, 0, 2, 2]),
   ((1 / 128 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((1 / 512 : ℂ), [0, 0, 1, 1, 1, 1])]

noncomputable def v433Ledger : APolyTwo :=
  [((9 : ℂ), [9]),
   ((5 / 2 : ℂ), [0, 8]),
   ((1 : ℂ), [1, 7]),
   ((3 / 2 : ℂ), [2, 6]),
   ((13 / 8 : ℂ), [3, 5]),
   ((1 / 2 : ℂ), [4, 4]),
   ((3 / 4 : ℂ), [0, 1, 6]),
   ((7 / 8 : ℂ), [0, 2, 5]),
   ((3 / 8 : ℂ), [0, 3, 4]),
   ((3 / 16 : ℂ), [1, 1, 5]),
   ((1 / 4 : ℂ), [1, 2, 4]),
   ((3 / 16 : ℂ), [1, 3, 3]),
   ((3 / 16 : ℂ), [2, 2, 3]),
   ((1 / 4 : ℂ), [0, 0, 1, 5]),
   ((1 / 8 : ℂ), [0, 0, 2, 4]),
   ((3 / 16 : ℂ), [0, 1, 1, 4]),
   ((1 / 4 : ℂ), [0, 1, 2, 3]),
   ((1 / 16 : ℂ), [0, 2, 2, 2]),
   ((1 / 32 : ℂ), [1, 1, 1, 3]),
   ((1 / 32 : ℂ), [1, 1, 2, 2]),
   ((3 / 64 : ℂ), [0, 0, 1, 1, 3]),
   ((1 / 16 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 32 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 64 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((1 / 128 : ℂ), [0, 0, 1, 1, 1, 1])]

noncomputable def v4222Ledger : APolyTwo :=
  [((12 : ℂ), [9]),
   ((15 / 4 : ℂ), [0, 8]),
   ((3 / 2 : ℂ), [1, 7]),
   ((3 / 2 : ℂ), [2, 6]),
   ((9 / 4 : ℂ), [3, 5]),
   ((3 / 4 : ℂ), [4, 4]),
   ((3 / 4 : ℂ), [0, 0, 7]),
   ((9 / 16 : ℂ), [0, 1, 6]),
   ((7 / 8 : ℂ), [0, 2, 5]),
   ((15 / 16 : ℂ), [0, 3, 4]),
   ((11 / 32 : ℂ), [1, 1, 5]),
   ((3 / 16 : ℂ), [1, 2, 4]),
   ((9 / 32 : ℂ), [1, 3, 3]),
   ((3 / 16 : ℂ), [2, 2, 3]),
   ((9 / 32 : ℂ), [0, 0, 0, 6]),
   ((3 / 32 : ℂ), [0, 0, 1, 5]),
   ((15 / 32 : ℂ), [0, 0, 2, 4]),
   ((9 / 64 : ℂ), [0, 0, 3, 3]),
   ((9 / 64 : ℂ), [0, 1, 1, 4]),
   ((15 / 64 : ℂ), [0, 1, 2, 3]),
   ((1 / 16 : ℂ), [0, 2, 2, 2]),
   ((15 / 256 : ℂ), [1, 1, 1, 3]),
   ((1 / 32 : ℂ), [1, 1, 2, 2]),
   ((3 / 128 : ℂ), [0, 0, 0, 0, 5]),
   ((3 / 64 : ℂ), [0, 0, 0, 1, 4]),
   ((15 / 128 : ℂ), [0, 0, 0, 2, 3]),
   ((21 / 512 : ℂ), [0, 0, 1, 1, 3]),
   ((3 / 64 : ℂ), [0, 0, 1, 2, 2]),
   ((7 / 256 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 512 : ℂ), [1, 1, 1, 1, 1]),
   ((3 / 256 : ℂ), [0, 0, 0, 0, 0, 4]),
   ((9 / 1024 : ℂ), [0, 0, 0, 0, 1, 3]),
   ((3 / 128 : ℂ), [0, 0, 0, 0, 2, 2]),
   ((9 / 512 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((3 / 1024 : ℂ), [0, 0, 1, 1, 1, 1]),
   ((3 / 2048 : ℂ), [0, 0, 0, 0, 0, 0, 3]),
   ((3 / 1024 : ℂ), [0, 0, 0, 0, 0, 1, 2]),
   ((3 / 2048 : ℂ), [0, 0, 0, 0, 1, 1, 1]),
   ((1 / 2048 : ℂ), [0, 0, 0, 0, 0, 0, 0, 2]),
   ((1 / 4096 : ℂ), [0, 0, 0, 0, 0, 0, 1, 1])]

noncomputable def v3322Ledger : APolyTwo :=
  [((14 : ℂ), [9]),
   ((9 / 2 : ℂ), [0, 8]),
   ((5 / 4 : ℂ), [1, 7]),
   ((3 : ℂ), [2, 6]),
   ((9 / 4 : ℂ), [3, 5]),
   ((1 / 2 : ℂ), [4, 4]),
   ((5 / 8 : ℂ), [0, 0, 7]),
   ((3 / 2 : ℂ), [0, 1, 6]),
   ((9 / 8 : ℂ), [0, 2, 5]),
   ((3 / 4 : ℂ), [0, 3, 4]),
   ((3 / 32 : ℂ), [1, 1, 5]),
   ((1 / 4 : ℂ), [1, 2, 4]),
   ((1 / 4 : ℂ), [1, 3, 3]),
   ((3 / 8 : ℂ), [2, 2, 3]),
   ((1 / 4 : ℂ), [0, 0, 0, 6]),
   ((15 / 32 : ℂ), [0, 0, 1, 5]),
   ((1 / 4 : ℂ), [0, 0, 2, 4]),
   ((3 / 16 : ℂ), [0, 0, 3, 3]),
   ((5 / 32 : ℂ), [0, 1, 1, 4]),
   ((7 / 16 : ℂ), [0, 1, 2, 3]),
   ((1 / 16 : ℂ), [0, 2, 2, 2]),
   ((1 / 64 : ℂ), [1, 1, 1, 3]),
   ((1 / 64 : ℂ), [1, 1, 2, 2]),
   ((3 / 128 : ℂ), [0, 0, 0, 0, 5]),
   ((3 / 32 : ℂ), [0, 0, 0, 1, 4]),
   ((1 / 16 : ℂ), [0, 0, 0, 2, 3]),
   ((7 / 64 : ℂ), [0, 0, 1, 1, 3]),
   ((5 / 64 : ℂ), [0, 0, 1, 2, 2]),
   ((1 / 64 : ℂ), [0, 1, 1, 1, 2]),
   ((1 / 128 : ℂ), [0, 0, 0, 0, 0, 4]),
   ((9 / 256 : ℂ), [0, 0, 0, 0, 1, 3]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 2, 2]),
   ((1 / 32 : ℂ), [0, 0, 0, 1, 1, 2]),
   ((1 / 256 : ℂ), [0, 0, 1, 1, 1, 1]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 0, 1, 2]),
   ((1 / 256 : ℂ), [0, 0, 0, 0, 1, 1, 1]),
   ((1 / 1024 : ℂ), [0, 0, 0, 0, 0, 0, 1, 1])]

private theorem mul_natCast_eq_smul (x : FockN (rank Ltwo)) (n : ℕ) :
    x * (n : FockN (rank Ltwo)) = (n : ℂ) • x := by
  rw [Algebra.smul_def, map_natCast]
  ring

private theorem mul_two_eq_smul (x : FockN (rank Ltwo)) :
    x * 2 = (2 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_three_eq_smul (x : FockN (rank Ltwo)) :
    x * 3 = (3 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_four_eq_smul (x : FockN (rank Ltwo)) :
    x * 4 = (4 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_five_eq_smul (x : FockN (rank Ltwo)) :
    x * 5 = (5 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_six_eq_smul (x : FockN (rank Ltwo)) :
    x * 6 = (6 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_seven_eq_smul (x : FockN (rank Ltwo)) :
    x * 7 = (7 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_eight_eq_smul (x : FockN (rank Ltwo)) :
    x * 8 = (8 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

private theorem mul_nine_eq_smul (x : FockN (rank Ltwo)) :
    x * 9 = (9 : ℂ) • x := by
  rw [Algebra.smul_def, map_ofNat]
  ring

/-- Canonicalize only the coordinate word; coefficients remain in the linear syntax. -/
def sortWord (w : List ℕ) : List ℕ := List.insertionSort (· ≤ ·) w

def sortAPoly (P : APolyTwo) : APolyTwo :=
  P.map fun t => (t.1, sortWord t.2)

private theorem evalAWord_perm {u v : List ℕ} (h : u.Perm v) :
    evalAWord u = evalAWord v := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [evalAWord]; rw [ih]
  | swap a b l => simp only [evalAWord]; ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem evalAWord_sortWord (w : List ℕ) :
    evalAWord (sortWord w) = evalAWord w :=
  evalAWord_perm (List.perm_insertionSort (· ≤ ·) w)

private theorem eval_sortAPoly (P : APolyTwo) :
    evalAPoly (sortAPoly P) = evalAPoly P := by
  induction P with
  | nil => simp [sortAPoly]
  | cons t P ih =>
      rcases t with ⟨c, w⟩
      change c • evalAWord (sortWord w) + evalAPoly (sortAPoly P) =
        c • evalAWord w + evalAPoly P
      rw [evalAWord_sortWord, ih]

/-- Finite Schur syntax mirroring the Newton recursion, before collection. -/
noncomputable def schurAPoly : ℕ → APolyTwo
  | 0 => [(1, [])]
  | N + 1 => scaleAPoly ((N + 1 : ℂ)⁻¹)
      ((List.range (N + 1)).flatMap fun m => prependA m (schurAPoly (N - m)))

private theorem evalAPoly_flatMap {ι : Type*} (l : List ι) (f : ι → APolyTwo) :
    evalAPoly (l.flatMap f) = (l.map fun i => evalAPoly (f i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem eval_schurAPoly (n : ℕ) :
    evalAPoly (schurAPoly n) = vSchur Ltwo alphaTwo n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [schurAPoly, evalAPoly, evalAWord, vSchur]; rw [vacuumN]
      | succ N =>
          rw [schurAPoly, eval_scaleAPoly, vSchur_succ, evalAPoly_flatMap]
          congr 1
          rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
          apply Finset.sum_congr rfl
          intro m hm
          rw [eval_prependA, ih (N - m) (by omega)]

def prependWord (w : List ℕ) (P : APolyTwo) : APolyTwo :=
  P.map fun t => (t.1, w ++ t.2)

noncomputable def mulAPoly (P Q : APolyTwo) : APolyTwo :=
  P.flatMap fun t => scaleAPoly t.1 (prependWord t.2 Q)

private theorem evalAWord_append (u v : List ℕ) :
    evalAWord (u ++ v) = evalAWord u * evalAWord v := by
  induction u with
  | nil => simp [evalAWord]; rw [vacuumN, one_mul]
  | cons i u ih => simp only [List.cons_append, evalAWord, ih]; ring

private theorem eval_prependWord (w : List ℕ) (P : APolyTwo) :
    evalAPoly (prependWord w P) = evalAWord w * evalAPoly P := by
  induction P with
  | nil => simp [prependWord]
  | cons t P ih =>
      rcases t with ⟨c, v⟩
      change c • evalAWord (w ++ v) + evalAPoly (prependWord w P) =
        evalAWord w * (c • evalAWord v + evalAPoly P)
      rw [evalAWord_append, ih, mul_add, mul_smul_comm]

private theorem eval_mulAPoly (P Q : APolyTwo) :
    evalAPoly (mulAPoly P Q) = evalAPoly P * evalAPoly Q := by
  induction P with
  | nil => simp [mulAPoly]
  | cons t P ih =>
      rcases t with ⟨c, w⟩
      change evalAPoly (scaleAPoly c (prependWord w Q) ++ mulAPoly P Q) =
        (c • evalAWord w + evalAPoly P) * evalAPoly Q
      rw [evalAPoly_append, eval_scaleAPoly, eval_prependWord, ih,
        add_mul, smul_mul_assoc]

noncomputable def screenedRaw : APolyTwo :=
  scaleAPoly (2 : ℂ) (mulAPoly schur3Ledger schur7Ledger) ++
    scaleAPoly (-8 : ℂ) (mulAPoly schur4Ledger schur6Ledger) ++
      scaleAPoly (6 : ℂ) (mulAPoly schur5Ledger schur5Ledger)

private theorem eval_screenedRaw :
    evalAPoly screenedRaw =
      (2 : ℂ) • (evalAPoly schur3Ledger * evalAPoly schur7Ledger) +
        (-8 : ℂ) • (evalAPoly schur4Ledger * evalAPoly schur6Ledger) +
          (6 : ℂ) • (evalAPoly schur5Ledger * evalAPoly schur5Ledger) := by
  rw [screenedRaw, evalAPoly_append, evalAPoly_append,
    eval_scaleAPoly, eval_scaleAPoly, eval_scaleAPoly,
    eval_mulAPoly, eval_mulAPoly, eval_mulAPoly]

attribute [local simp] Finset.sum_range_succ Finset.sum_range_zero
  List.range_succ List.range_zero mul_natCast_eq_smul
  mul_two_eq_smul mul_three_eq_smul mul_four_eq_smul mul_five_eq_smul
  mul_six_eq_smul mul_seven_eq_smul mul_eight_eq_smul mul_nine_eq_smul

set_option maxHeartbeats 400000 in
-- Finite normalization of the degree-three Schur ledger expands all ordered partitions.
private theorem vSchur_3_eq_ledger :
    vSchur Ltwo alphaTwo 3 = evalAPoly schur3Ledger := by
  rw [← eval_schurAPoly 3, ← eval_sortAPoly (schurAPoly 3), schur3Ledger]
  simp [sortAPoly, sortWord, schurAPoly, scaleAPoly, prependA,
    evalAPoly, evalAWord, vacuumN]
  module

set_option maxHeartbeats 400000 in
-- Finite normalization of the degree-four Schur ledger expands all ordered partitions.
private theorem vSchur_4_eq_ledger :
    vSchur Ltwo alphaTwo 4 = evalAPoly schur4Ledger := by
  rw [← eval_schurAPoly 4, ← eval_sortAPoly (schurAPoly 4), schur4Ledger]
  simp [sortAPoly, sortWord, schurAPoly, scaleAPoly, prependA,
    evalAPoly, evalAWord, vacuumN]
  module

set_option maxHeartbeats 400000 in
-- Finite normalization of the degree-five Schur ledger expands all ordered partitions.
private theorem vSchur_5_eq_ledger :
    vSchur Ltwo alphaTwo 5 = evalAPoly schur5Ledger := by
  rw [← eval_schurAPoly 5, ← eval_sortAPoly (schurAPoly 5), schur5Ledger]
  simp [sortAPoly, sortWord, schurAPoly, scaleAPoly, prependA,
    evalAPoly, evalAWord, vacuumN]
  module

set_option maxHeartbeats 400000 in
-- Finite normalization of the degree-six Schur ledger expands all ordered partitions.
private theorem vSchur_6_eq_ledger :
    vSchur Ltwo alphaTwo 6 = evalAPoly schur6Ledger := by
  rw [← eval_schurAPoly 6, ← eval_sortAPoly (schurAPoly 6), schur6Ledger]
  simp [sortAPoly, sortWord, schurAPoly, scaleAPoly, prependA,
    evalAPoly, evalAWord, vacuumN]
  module

set_option maxHeartbeats 400000 in
-- Finite normalization of the degree-seven Schur ledger expands all ordered partitions.
private theorem vSchur_7_eq_ledger :
    vSchur Ltwo alphaTwo 7 = evalAPoly schur7Ledger := by
  rw [← eval_schurAPoly 7, ← eval_sortAPoly (schurAPoly 7), schur7Ledger]
  simp [sortAPoly, sortWord, schurAPoly, scaleAPoly, prependA,
    evalAPoly, evalAWord, vacuumN]
  module

/-- Public semantic endpoint for the screened Schur expression, collected as a 33-term ledger in
the 42-dimensional neutral sector.  Downstream Zhu certificates reuse this transport instead of
recomputing the screening expression. -/
theorem screened_eq_ledger :
    (2 : ℂ) • (vSchur Ltwo alphaTwo 3 * vSchur Ltwo alphaTwo 7) +
        (-8 : ℂ) • (vSchur Ltwo alphaTwo 4 * vSchur Ltwo alphaTwo 6) +
          (6 : ℂ) • (vSchur Ltwo alphaTwo 5 * vSchur Ltwo alphaTwo 5) =
      evalAPoly screenedLedger := by
  rw [vSchur_3_eq_ledger, vSchur_4_eq_ledger, vSchur_5_eq_ledger,
    vSchur_6_eq_ledger, vSchur_7_eq_ledger]
  rw [← eval_screenedRaw, ← eval_sortAPoly screenedRaw]
  rw [screenedRaw, schur3Ledger, schur4Ledger, schur5Ledger, schur6Ledger,
    schur7Ledger, screenedLedger]
  simp [sortAPoly, sortWord, mulAPoly, prependWord, scaleAPoly,
    evalAPoly, evalAWord, vacuumN]
  module


private theorem eval_reify_v2 :
    evalAPoly (reifyVirWord [2]) = evalAPoly v2Ledger := by
  rw [v2Ledger]
  simp [reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v3 :
    evalAPoly (reifyVirWord [3]) = evalAPoly v3Ledger := by
  rw [← eval_sortAPoly (reifyVirWord [3]), v3Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v4 :
    evalAPoly (reifyVirWord [4]) = evalAPoly v4Ledger := by
  rw [← eval_sortAPoly (reifyVirWord [4]), v4Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v5 :
    evalAPoly (reifyVirWord [5]) = evalAPoly v5Ledger := by
  rw [← eval_sortAPoly (reifyVirWord [5]), v5Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v10 :
    evalAPoly (reifyVirWord [10]) = evalAPoly v10Ledger := by
  rw [← eval_sortAPoly (reifyVirWord [10]), v10Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v22 :
    evalAPoly (reifyVirWord [2, 2]) = evalAPoly v22Ledger := by
  change evalAPoly (virActPoly 2 (reifyVirWord [2])) = evalAPoly v22Ledger
  rw [eval_virActPoly 2 (by norm_num), eval_reify_v2,
    ← eval_virActPoly 2 (by norm_num) v2Ledger]
  rw [← eval_sortAPoly (virActPoly 2 v2Ledger)]
  rw [v2Ledger, v22Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v32 :
    evalAPoly (reifyVirWord [3, 2]) = evalAPoly v32Ledger := by
  change evalAPoly (virActPoly 3 (reifyVirWord [2])) = evalAPoly v32Ledger
  rw [eval_virActPoly 3 (by norm_num), eval_reify_v2,
    ← eval_virActPoly 3 (by norm_num) v2Ledger]
  rw [← eval_sortAPoly (virActPoly 3 v2Ledger)]
  rw [v2Ledger, v32Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v42 :
    evalAPoly (reifyVirWord [4, 2]) = evalAPoly v42Ledger := by
  change evalAPoly (virActPoly 4 (reifyVirWord [2])) = evalAPoly v42Ledger
  rw [eval_virActPoly 4 (by norm_num), eval_reify_v2,
    ← eval_virActPoly 4 (by norm_num) v2Ledger]
  rw [← eval_sortAPoly (virActPoly 4 v2Ledger)]
  rw [v2Ledger, v42Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v33 :
    evalAPoly (reifyVirWord [3, 3]) = evalAPoly v33Ledger := by
  change evalAPoly (virActPoly 3 (reifyVirWord [3])) = evalAPoly v33Ledger
  rw [eval_virActPoly 3 (by norm_num), eval_reify_v3,
    ← eval_virActPoly 3 (by norm_num) v3Ledger]
  rw [← eval_sortAPoly (virActPoly 3 v3Ledger)]
  rw [v3Ledger, v33Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v222 :
    evalAPoly (reifyVirWord [2, 2, 2]) = evalAPoly v222Ledger := by
  change evalAPoly (virActPoly 2 (reifyVirWord [2, 2])) = evalAPoly v222Ledger
  rw [eval_virActPoly 2 (by norm_num), eval_reify_v22,
    ← eval_virActPoly 2 (by norm_num) v22Ledger]
  rw [← eval_sortAPoly (virActPoly 2 v22Ledger)]
  rw [v22Ledger, v222Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v322 :
    evalAPoly (reifyVirWord [3, 2, 2]) = evalAPoly v322Ledger := by
  change evalAPoly (virActPoly 3 (reifyVirWord [2, 2])) = evalAPoly v322Ledger
  rw [eval_virActPoly 3 (by norm_num), eval_reify_v22,
    ← eval_virActPoly 3 (by norm_num) v22Ledger]
  rw [← eval_sortAPoly (virActPoly 3 v22Ledger)]
  rw [v22Ledger, v322Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v2222 :
    evalAPoly (reifyVirWord [2, 2, 2, 2]) = evalAPoly v2222Ledger := by
  change evalAPoly (virActPoly 2 (reifyVirWord [2, 2, 2])) = evalAPoly v2222Ledger
  rw [eval_virActPoly 2 (by norm_num), eval_reify_v222,
    ← eval_virActPoly 2 (by norm_num) v222Ledger]
  rw [← eval_sortAPoly (virActPoly 2 v222Ledger)]
  rw [v222Ledger, v2222Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v22222 :
    evalAPoly (reifyVirWord [2, 2, 2, 2, 2]) = evalAPoly v22222Ledger := by
  change evalAPoly (virActPoly 2 (reifyVirWord [2, 2, 2, 2])) = evalAPoly v22222Ledger
  rw [eval_virActPoly 2 (by norm_num), eval_reify_v2222,
    ← eval_virActPoly 2 (by norm_num) v2222Ledger]
  rw [← eval_sortAPoly (virActPoly 2 v2222Ledger)]
  rw [v2222Ledger, v22222Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v82 :
    evalAPoly (reifyVirWord [8, 2]) = evalAPoly v82Ledger := by
  change evalAPoly (virActPoly 8 (reifyVirWord [2])) = evalAPoly v82Ledger
  rw [eval_virActPoly 8 (by norm_num), eval_reify_v2,
    ← eval_virActPoly 8 (by norm_num) v2Ledger]
  rw [← eval_sortAPoly (virActPoly 8 v2Ledger)]
  rw [v2Ledger, v82Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v73 :
    evalAPoly (reifyVirWord [7, 3]) = evalAPoly v73Ledger := by
  change evalAPoly (virActPoly 7 (reifyVirWord [3])) = evalAPoly v73Ledger
  rw [eval_virActPoly 7 (by norm_num), eval_reify_v3,
    ← eval_virActPoly 7 (by norm_num) v3Ledger]
  rw [← eval_sortAPoly (virActPoly 7 v3Ledger)]
  rw [v3Ledger, v73Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v64 :
    evalAPoly (reifyVirWord [6, 4]) = evalAPoly v64Ledger := by
  change evalAPoly (virActPoly 6 (reifyVirWord [4])) = evalAPoly v64Ledger
  rw [eval_virActPoly 6 (by norm_num), eval_reify_v4,
    ← eval_virActPoly 6 (by norm_num) v4Ledger]
  rw [← eval_sortAPoly (virActPoly 6 v4Ledger)]
  rw [v4Ledger, v64Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v622 :
    evalAPoly (reifyVirWord [6, 2, 2]) = evalAPoly v622Ledger := by
  change evalAPoly (virActPoly 6 (reifyVirWord [2, 2])) = evalAPoly v622Ledger
  rw [eval_virActPoly 6 (by norm_num), eval_reify_v22,
    ← eval_virActPoly 6 (by norm_num) v22Ledger]
  rw [← eval_sortAPoly (virActPoly 6 v22Ledger)]
  rw [v22Ledger, v622Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v55 :
    evalAPoly (reifyVirWord [5, 5]) = evalAPoly v55Ledger := by
  change evalAPoly (virActPoly 5 (reifyVirWord [5])) = evalAPoly v55Ledger
  rw [eval_virActPoly 5 (by norm_num), eval_reify_v5,
    ← eval_virActPoly 5 (by norm_num) v5Ledger]
  rw [← eval_sortAPoly (virActPoly 5 v5Ledger)]
  rw [v5Ledger, v55Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v532 :
    evalAPoly (reifyVirWord [5, 3, 2]) = evalAPoly v532Ledger := by
  change evalAPoly (virActPoly 5 (reifyVirWord [3, 2])) = evalAPoly v532Ledger
  rw [eval_virActPoly 5 (by norm_num), eval_reify_v32,
    ← eval_virActPoly 5 (by norm_num) v32Ledger]
  rw [← eval_sortAPoly (virActPoly 5 v32Ledger)]
  rw [v32Ledger, v532Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v442 :
    evalAPoly (reifyVirWord [4, 4, 2]) = evalAPoly v442Ledger := by
  change evalAPoly (virActPoly 4 (reifyVirWord [4, 2])) = evalAPoly v442Ledger
  rw [eval_virActPoly 4 (by norm_num), eval_reify_v42,
    ← eval_virActPoly 4 (by norm_num) v42Ledger]
  rw [← eval_sortAPoly (virActPoly 4 v42Ledger)]
  rw [v42Ledger, v442Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v433 :
    evalAPoly (reifyVirWord [4, 3, 3]) = evalAPoly v433Ledger := by
  change evalAPoly (virActPoly 4 (reifyVirWord [3, 3])) = evalAPoly v433Ledger
  rw [eval_virActPoly 4 (by norm_num), eval_reify_v33,
    ← eval_virActPoly 4 (by norm_num) v33Ledger]
  rw [← eval_sortAPoly (virActPoly 4 v33Ledger)]
  rw [v33Ledger, v433Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v4222 :
    evalAPoly (reifyVirWord [4, 2, 2, 2]) = evalAPoly v4222Ledger := by
  change evalAPoly (virActPoly 4 (reifyVirWord [2, 2, 2])) = evalAPoly v4222Ledger
  rw [eval_virActPoly 4 (by norm_num), eval_reify_v222,
    ← eval_virActPoly 4 (by norm_num) v222Ledger]
  rw [← eval_sortAPoly (virActPoly 4 v222Ledger)]
  rw [v222Ledger, v4222Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

private theorem eval_reify_v3322 :
    evalAPoly (reifyVirWord [3, 3, 2, 2]) = evalAPoly v3322Ledger := by
  change evalAPoly (virActPoly 3 (reifyVirWord [3, 2, 2])) = evalAPoly v3322Ledger
  rw [eval_virActPoly 3 (by norm_num), eval_reify_v322,
    ← eval_virActPoly 3 (by norm_num) v322Ledger]
  rw [← eval_sortAPoly (virActPoly 3 v322Ledger)]
  rw [v322Ledger, v3322Ledger]
  simp [sortAPoly, sortWord, reifyVirWord, virActPoly, virActWord, virVacAPoly,
    scaleAPoly, prependA, evalAPoly, evalAWord, vacuumN]
  module

set_option maxRecDepth 5000 in
set_option maxHeartbeats 400000 in
-- The final check expands and compares the already certified finite weight-ten ledgers.
/-- The literal weight-ten polynomial comparison.  It is assembled only after each
Virasoro word and the screened Schur side have been collected independently. -/
theorem amTwo_polynomial_identity :
    (2 : ℂ) • (vSchur Ltwo alphaTwo 3 * vSchur Ltwo alphaTwo 7) +
        (-8 : ℂ) • (vSchur Ltwo alphaTwo 4 * vSchur Ltwo alphaTwo 6) +
          (6 : ℂ) • (vSchur Ltwo alphaTwo 5 * vSchur Ltwo alphaTwo 5) =
      (3 : ℂ) • evalAPoly hProductExpectedAssembly +
        (1024 / 1575 : ℂ) • evalAPoly (reifyVirWord [2, 2, 2, 2, 2]) +
          evalAPoly amTwoRemainderAPoly := by
  rw [screened_eq_ledger, eval_reify_v22222, amTwoRemainderAPoly]
  simp only [evalAPoly_append, eval_scaleAPoly]
  rw [eval_reify_v10, eval_reify_v82, eval_reify_v73, eval_reify_v64,
    eval_reify_v622, eval_reify_v55, eval_reify_v532, eval_reify_v442,
    eval_reify_v433, eval_reify_v4222, eval_reify_v3322]
  rw [screenedLedger, hProductExpectedAssembly, v22222Ledger, v10Ledger,
    v82Ledger, v73Ledger, v64Ledger, v622Ledger, v55Ledger, v532Ledger,
    v442Ledger, v433Ledger, v4222Ledger, v3322Ledger]
  simp [evalAPoly, evalAWord, vacuumN]
  module


end VOA.LatGen.WpTwoAMAssembly

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMAssembly.amTwo_polynomial_identity
end AxiomAudit

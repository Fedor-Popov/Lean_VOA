/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.LatticesAndCodes.Codes.Defs
import VOA.LatticesAndCodes.Codes.Enumerator
import VOA.LatticesAndCodes.Codes.Golay
import VOA.LatticesAndCodes.Codes.GolayEnumerator
import VOA.LatticesAndCodes.Codes.MacWilliams
import VOA.LatticesAndCodes.Construction.CodeToLattice
import VOA.LatticesAndCodes.ForMathlib.EuclideanTheta
import VOA.LatticesAndCodes.ForMathlib.ExpBound
import VOA.LatticesAndCodes.ForMathlib.PoissonShift
import VOA.LatticesAndCodes.ForMathlib.PoissonSummation
import VOA.LatticesAndCodes.ForMathlib.QuotientCoset
import VOA.LatticesAndCodes.Lattice.Defs
import VOA.LatticesAndCodes.Lattice.Euclidean
import VOA.LatticesAndCodes.Lattice.Index
import VOA.LatticesAndCodes.Lattice.Sublattice
import VOA.LatticesAndCodes.Leech.Defs
import VOA.LatticesAndCodes.Leech.RepCount
import VOA.LatticesAndCodes.Leech.RepCountHigher
import VOA.LatticesAndCodes.ModularForms.LevelOne
import VOA.LatticesAndCodes.Roots.RootLattice
import VOA.LatticesAndCodes.Theta.Counting
import VOA.LatticesAndCodes.Theta.Defs
import VOA.LatticesAndCodes.Theta.ModularForm
import VOA.LatticesAndCodes.Theta.QExpansion
import VOA.LatticesAndCodes.Theta.Transformation

/-!
# Vendored lattice and code theory (from *Lattices and Codes*)

These 25 files are copied verbatim from the companion formalization of Ebeling, *Lattices and
Codes* (repository `Fedor-Popov/LatticeAndCodes`, commit `da62b9e2f44a04888abf6f797a429aa8ecc1d6dd`),
so that this package depends on Mathlib alone.  The ONLY edit is the module prefix
`LatticesAndCodes.` → `VOA.LatticesAndCodes.` in `import` lines.  Declaration names and namespaces
are unchanged (`_root_.IntegralLattice`, `Leech`, `Code`, …); inside `namespace VOA` the bare name
`IntegralLattice` means `VOA.IntegralLattice`, so refer to the vendored one as
`_root_.IntegralLattice`.

The set is the import closure of what the Moonshine construction uses: `Leech.Defs` (the Leech
lattice from the Golay code: even, unimodular, positive definite, rank 24, rootless),
`Leech.RepCount` (`repCount_four = 196560`) and `Leech.RepCountHigher` (`repCount_six`).

To refresh from upstream: copy the same files from a newer commit, re-apply the prefix rewrite,
and update the commit hash above.
-/

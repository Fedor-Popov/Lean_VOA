/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockBoundC2
import VOA.Modularity.SuperAKFormalODE
import VOA.Modularity.SuperTorusRecursion
import VOA.Modularity.SuperTorusRecursionClose
import VOA.Modularity.SuperTwistedTrace
import VOA.Modularity.SuperWedderburnTrace
import VOA.Modularity.SuperSectorRationality
import VOA.Modules.SuperTwistedZhuFinite
import VOA.Modules.SuperRelativeEtingofFinite
import VOA.Modules.SuperRelativeTwistedZhuBridge

/-!
# Integral-weight super-VOA modularity foundations

This is the dependency-closed umbrella for the fully proved, integral-weight super-VOA
development.  It exposes:

* the square-bracket, analytic-block, super-Zhu, twisted-module, supertrace, and torus-recursion
  foundations, including the identity-sector ordinary supertrace as a formal super block;
* the super Arike--Nagatomo upper bound on the dimension of the abstract genus-one block space;
* the abstract Arakawa--Kawasetsu formal ODE under the super Etingof-finiteness hypothesis;
* relative Poisson-homology carriers and quotients from explicitly supplied descended action data;
* finite M/Q Wedderburn packages supplied as explicit product-decomposition data, whose pulled-back
  standard functionals separate the blocks and are linearly independent, and span the
  supersymmetric functionals only under the stated finrank upper bound;
* conditional finite `(g,h)` sector packages: when a `FiniteCompleteSectorTraceRealization` is
  supplied, its family of actual bottom-space M/Q functionals is finite and linearly independent,
  and spans the temporal `h`-supersymmetric functionals only under the explicit finrank upper
  bound.

The scope is deliberately narrower than a super modularity theorem.  In particular, this umbrella
does **not** claim modular invariance, convergence and spanning by pseudo-supertraces, a
super-Wedderburn classification, or construct the twisted modules, centralizer lifts,
bottom-space realizations, or equivariant finrank bound required by the conditional sector
package from strong rationality; nor does it prove a strongly-rational super Zhu modularity
theorem.  The odd trace has only its
bihomogeneous square-bracket-zero slice: no full odd, nonidentity-sector, or half-integral
recursion is claimed.  The relative Poisson-homology APIs require explicit `SuperRelativePoissonData` or
`SuperTwistedRelativePoissonData`; no theorem here constructs that descent data or establishes
relative finiteness for a twisted module from the current structural hypotheses.

-/

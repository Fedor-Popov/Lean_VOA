/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalSeries
import VOA.Foundations.FormalCalculus
import VOA.Foundations.Locality
import VOA.Foundations.Parity
import VOA.Foundations.Expansion
import VOA.Foundations.IotaZExpansion
import VOA.Foundations.IteratedLaurent
import VOA.Foundations.Substitution
import VOA.Foundations.DeltaJump
import VOA.Foundations.FormalDist3
import VOA.Foundations.FormalDist4
import VOA.Foundations.FormalDist4Delta
import VOA.Foundations.FormalDist4DeltaContract
import VOA.Foundations.FormalDist4DeltaSupport
import VOA.Foundations.Virasoro
import VOA.Foundations.VirasoroModule
import VOA.Foundations.Lattices
import VOA.Foundations.LatticeCocycle
import VOA.Foundations.LatticeAlgebraTwisted
import VOA.Foundations.LatticeFinite
import VOA.Foundations.LatticeOrthoFrame
import VOA.Foundations.AffineLie
import VOA.Foundations.PBWBasis
import VOA.Foundations.PBWTheorem.VacuumBasis
import VOA.Foundations.RootDatum

/-!
# Foundations

The analytic-algebraic substrate for VOAs, plus the algebraic structures the main
examples are built from. Corresponds to Gannon §5.1.2 (formal power series) and the
prerequisite Chapters 1–3.

* `FormalSeries`   — the space `𝒲⟦z^±⟧` of formal distributions and algebraic
  summability/products (Gannon §5.1.2).
* `FormalCalculus` — the formal delta `δ(z)`, residues `Res_z`, modes `a₍ₘ₎`, the
  binomial convention `(z₁+z₂)ⁿ`, and the expansion map `ι_z` (5.1.2–5.1.5).
* `Locality`       — Proposition 5.1.2, mutual locality, the OPE and normal-ordered
  product (5.1.6).
* `Parity`         — the `ℤ/2` parity grading and the Koszul sign `ε` (Axis B of the
  super generalization).
* `Expansion`      — the two expansions `ι₁₂/ι₂₁` of `(z₁-z₂)ⁿ` and the δ-jump (5.1.2).
* `IteratedLaurent`— the `(z₁-z₂)ᴺ` cancellation on lower-truncated distributions (5.1.2).
* `Substitution`   — the substitution `z₁↦z₀+z₂` and its multiplicativity
  `subst((z₁-z₂)·f)=z₀·subst(f)` (5.1.2; the general-`n` `ι_z` multiplicativity).
* `Virasoro`       — the Witt and Virasoro algebras (§3.1.1–3.1.2, eq. (3.1.5)).
* `Lattices`       — even / positive-definite integral lattices and their group
  algebras (§1.2.1).
* `AffineLie`      — affine Kac–Moody algebras `ĝ` and the Sugawara construction
  (§3.2).
* `RootDatum`      — finite root datum, highest root, and affine-node generators
  for affine Kac–Moody integrability (§3.2).
-/

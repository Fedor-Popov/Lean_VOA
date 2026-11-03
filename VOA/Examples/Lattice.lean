/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeA1
import VOA.Examples.Heisenberg
import VOA.Foundations.Lattices
import VOA.Examples.LatticeLocalityDiag
import VOA.Examples.LatticeHLLocality
import VOA.Examples.LatticeCrossLocality
import VOA.Examples.LatticeA1VOA

/-!
# Lattice VOAs `𝒱(L)` — the `A₁` root lattice  (Gannon §5.2.2, pp. 327–329)

A relatively simple but rich class of VOAs, attached to even positive-definite lattices.  For
`L = ℤα` with `⟨α,α⟩ = 2` (the `A₁` root lattice) the underlying space is
`𝒱(A₁) = 𝒱(h̄) ⊗ ℂ{A₁}`, the rank-1 Heisenberg VOA `𝒱(h̄)` (`Examples.Heisenberg`, here
`heisenbergVOA' 1`, central charge `1 = rank A₁`) tensored with the group algebra `ℂ{ℤα}`
(`Examples.LatticeA1`, `LatModule = FockN 1 ⊗ ℂ{ℤ}`).

## What is assembled here (all `sorry`-free, axiom-clean)

Re-exported from `Examples.LatticeA1`:

* `LatticeVOA.Yeα : FormalDist (End ℂ LatModule)` — a **`z⁰`-only placeholder**, *not* the
  lattice vertex operator `Y(1⊗eᵅ, z)` of Gannon p. 327: its only nonzero coefficient is
  `Yeα 0 = e^{α}` (`Yeα_creation_z0`).  The genuine operator is `LatExp.Yeα` (below).
* `LatticeVOA.OPEStructure m n` — a predicate that mentions **no operators**: it says only that
  `⟨mα,nα⟩ = N ≥ 0` and the scalar identity `(z₁-z₂)^N·ι₁₂((z₁-z₂)^{-N}) = 1`.
  `OPEStructure_of_nonneg` is therefore a tautology about formal series and proves **no**
  locality (certificate `OPEStructure_iff`, `Notes/Textbook/certificates/L05_Checks.lean`).
  Operator locality is `LatExp.Yemα_local` (below).
* `latticeA1_centralCharge` is the central charge `1` of the Heisenberg factor `heisenbergVOA' 1`;
  the central charge of the lattice VOA itself is `latticeVOA_A1_centralCharge`.

## The genuine vertex operator (`Examples.LatticeFields`)

The placeholder `LatticeVOA.Yeα` here is `z⁰`-only (`EminusOp := fun t => if t=0 then id else 0`).
The genuine vertex operator is the **boson-dressed `LatExp.Yeα`** (`Examples.LatticeFields`, built on
the `k=2` half-current core `Examples.LatticeExp`): the real `E⁻`/`E⁺` exponential fields, the
boson dressing `EE = E⁻E⁺`, the `z^{α₀}=z^{2n}` sector shift, and the genuine creation series
`cSchur N ⊗ eᵅ` (`LatExp.Yeα_vacuum`, `(eᵅ)₍₋₁₎Ω=eᵅ`), all `sorry`-free / axiom-clean.

## Operator-level mutual locality (the `VA4` data)

The diagonal `Local Yeα Yeα` (`LatExp.latticeA1_local`) is proved — the `(z₁-z₂)²`-contraction
`E⁺(α,z₁)E⁻(α,z₂) = (1-z₂/z₁)²·E⁻(α,z₂)E⁺(α,z₁)` (`LatExp.Eplus_comp_Eminus`) re-summed (`eeMaster`)
into the symmetric four-fold operator, so the even-`A₁` operators commute *exactly* (`ι_z`-free).
**All four charge-`±1` generator-pair localities are proved**, `pbw`-free and
axiom-clean:
* the diagonals `Local (Yemα 1)(Yemα 1)` and `Local (Yemα (-1))(Yemα (-1))`
  (`latticeA1_diag_*_local`) — even-lattice, *exact* commutation;
* the Heisenberg–lattice `Local α(z) (Yemα (-1))` (`latticeA1_HL_negOne_local`, bound `1`);
* the **cross pair** `Local (Yemα 1) (Yemα (-1))` (`latticeA1_cross_local`, bound `2`) — the
  genuine `ι_z` case: pole order `|⟨α,-α⟩| = 2`, proved via the cross operator OPE
  `E⁺(α,z₁)E⁻(-α,z₂) = (1-z₂/z₁)^{-2}·(…)` (the geometric kernel `(m+1)`,
  `LatExp.EplusC1_comp_EminusCm1`), whose `(z₁-z₂)²` second difference (the `[1,-2,1]` kernel
  convolution `= δ`) collapses both operator orders to the *same* normal-ordered four-fold
  `Wcross`, so the cross bracket is annihilated by `(z₁-z₂)²`.
These four generator localities (with the boson self-locality from the Heisenberg factor) are the
`VA4` data feeding the operator-first reconstruction (`Core.ReconstructionExistence`) toward the
full `VertexOperatorAlgebra (LatModule)` instance (the remaining translation `L₋₁`-covariance,
`VA1` grading and `VOA1`/`VOA2` Sugawara mirror the affine `affineSl2VOA` assembly).

## Dependencies
* `VOA.Examples.LatticeA1` (the vertex operator and OPE locality),
  `VOA.Examples.Heisenberg` (the rank-1 Heisenberg substrate),
  `VOA.Foundations.Lattices` (the even/positive-definite `A₁` lattice).

## Status
`LatExp.latticeVOA_A1 : VertexOperatorAlgebra LatModule` is a
complete instance on the genuine `LatModule = FockN 1 ⊗ ℂ{ℤ}`, central charge `1 = rank A₁`,
axiom-clean (`[propext, Classical.choice, Quot.sound]`, **`pbw`-free**).  Built by the operator-first
reconstruction (`Core.ReconstructionExistence.reconstruct`) over the boson-monomial × charge-lattice
generating family: the **general charge-pair mutual locality** `LatExp.Yemα_local`
(same-sign exact commutation via the `(1-x)^{2mm'}` four-fold resummation; opposite-sign the
`(z₁-z₂)^{-2mm'}` cross-contraction; charge-`0` the identity-spectator) feeds the Dong cascade, and
the charged-generator translation covariance `LatExp.Trec_Yemα_DCovariant` supplies the energy–momentum
datum.  The conformal vector is the rank-1 boson Sugawara `(½α₋₁²)|0⟩ ⊗ e^0`.

## References
* Gannon §5.2.2, eq. (5.3.6); Borcherds [68]; FHL [199]; FLM Ch. 8; Lepowsky–Li Ch. 6.
-/

namespace VOA

/-! ## Re-exported main facts -/

/-- The central charge of the rank-1 **Heisenberg** VOA `heisenbergVOA' 1` is `1`.  This is a
statement about the Heisenberg factor only, not about the lattice VOA; for the latter see
`latticeVOA_A1_centralCharge`. -/
theorem latticeA1_centralCharge : (heisenbergVOA' 1).centralCharge = 1 :=
  heisenbergVOA'_one_centralCharge

/-- **Tautology; no locality content.**  `LatticeVOA.OPEStructure m n` mentions no operators: it
asserts `⟨mα,nα⟩ = N` for some `N : ℕ` together with the scalar formal-series identity
`(z₁-z₂)^N·ι₁₂((z₁-z₂)^{-N}) = 1`, which holds for every `N`.  So this is just `0 ≤ latForm m n`
(certificate `OPEStructure_iff`, `Notes/Textbook/certificates/L05_Checks.lean`).  Operator locality
of the lattice fields is `LatExp.Yemα_local`. -/
theorem latticeA1_local_of_nonneg {m n : ℤ} (h : 0 ≤ LatticeVOA.latForm m n) :
    LatticeVOA.OPEStructure m n :=
  LatticeVOA.OPEStructure_of_nonneg h

/-! ## Operator-level generator mutual localities (the `VA4` data, `pbw`-free)

The genuine boson-dressed lattice vertex operators `Yemα m` (`Examples.LatticeChargeMFields`)
are mutually local for three of the four charge-`±1` generator pairs, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `pbw`).  The remaining cross pair
`Local (Yemα 1) (Yemα (-1))` (pole order `|⟨α,-α⟩| = 2`) needs the cross operator OPE
`E⁺(α,z₁)E⁻(-α,z₂) = (1-z₂/z₁)^{-2}·(…)` (the `ι_z` expansion, kernel `(i+1)`). -/

/-- **Diagonal self-locality, charge `1`**: `Local (Yeα,z₁)(Yeα,z₂)`, the even-`A₁` operators
commute exactly (`= Yemα 1`). -/
theorem latticeA1_diag_one_local : Local (LatExp.Yemα 1) (LatExp.Yemα 1) :=
  LatExp.Yemα_one_local

/-- **Diagonal self-locality, charge `-1`**: `Local (Y(e^{-α}),z₁)(Y(e^{-α}),z₂)` — the
charge-`(-1)` lattice operator commutes with itself (self-pairing `⟨-α,-α⟩ = 2`). -/
theorem latticeA1_diag_negOne_local : Local (LatExp.Yemα (-1)) (LatExp.Yemα (-1)) :=
  LatExp.Yemα_negOne_local

/-- **Heisenberg–lattice locality, charge `-1`**: `Local (α(z₁))(Y(e^{-α}),z₂)` — the boson
current is mutually local with the charge-`(-1)` lattice operator (bound `N = 1`). -/
theorem latticeA1_HL_negOne_local : Local LatExp.alphaLat (LatExp.Yemα (-1)) :=
  LatExp.latticeHL_neg1_local

/-- **Cross mutual locality** `Local (Yeα,z₁)(Y(e^{-α}),z₂)` (charges `+1, -1`, pairing `-2`):
the genuine `ι_z` pole-order-`2` case, bound `N = 2`.  The fourth and last charge-`±1`
generator-pair locality datum. -/
theorem latticeA1_cross_local : Local (LatExp.Yemα 1) (LatExp.Yemα (-1)) :=
  LatExp.Yemα_cross_local

/-! ## The closed lattice `A₁` vertex operator algebra -/

/-- **The general charge-pair mutual locality** `Local (Yemα m) (Yemα m')` for *all* `m, m' : ℤ`
(the full `VA4` datum): same-sign exact commutation, opposite-sign the `(z₁-z₂)^{-2mm'}`
cross-contraction, charge-`0` the identity spectator.  Axiom-clean, `pbw`-free. -/
theorem latticeA1_local (m m' : ℤ) : Local (LatExp.Yemα m) (LatExp.Yemα m') :=
  LatExp.Yemα_local m m'

/-- **The `A₁` lattice vertex operator algebra** `𝒱(A₁)` (Gannon §5.2.2) as a closed instance of
`VertexOperatorAlgebra LatModule`, central charge `1`, axiom-clean and `pbw`-free. -/
noncomputable def latticeVOA_A1 : VertexOperatorAlgebra LatticeVOA.LatModule :=
  LatExp.latticeVOA_A1

/-- **The central charge of the closed `A₁` lattice VOA is `1`** (`= rank A₁`). -/
theorem latticeVOA_A1_centralCharge : latticeVOA_A1.centralCharge = 1 :=
  LatExp.latticeVOA_A1_centralCharge

end VOA

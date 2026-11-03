/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeVOAInstance
import VOA.Examples.LatticeOppSignLocality

/-!
# The closed lattice `A₁` vertex operator algebra `latticeVOA_A1`

The lattice `A₁` VOA `𝒱(A₁)` (Gannon §5.2.2), assembled as a closed instance of
`VertexOperatorAlgebra LatModule` — no remaining hypotheses, `pbw`-free, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

This discharges the one hypothesis of `latticeVOA_A1_of_locality` (the general charge-pair mutual
locality `hYloc`) with the proved `Yemα_local`, the operator-first reconstruction over the
boson-monomial × charge-lattice generating family:

* the boson factor `FockN 1` is spanned by its free monomial basis (no PBW), and the lattice
  factor `ℂ{ℤ}` by `{e^{mα}}`, so `wordStateLat_span` is the tensor product of the two
  (`TensorProduct.span_tmul_eq_top`), NOT a `U(𝔫₋)`-cyclicity theorem;
* mutual locality of all charged generators `Yemα_local` (same-sign commute, opposite-sign the
  `(z₁-z₂)^{-2mm'}` cross-contraction) feeds the Dong cascade `YwordLat_local`;
* the energy–momentum covariance `Trec_Yemα_DCovariant` supplies `reconstruct`'s translation
  datum, yielding the all-states vertex map `Yfull`; the conformal vector `ω` is the rank-1 boson
  Sugawara `(½α₋₁²)|0⟩ ⊗ e^0`, giving central charge `c = 1 = rank A₁`.
-/

open VOA VOA.LatExp VOA.LatticeVOA

namespace VOA.LatExp

/-- **The lattice `A₁` vertex operator algebra** `𝒱(A₁)` (Gannon §5.2.2): a closed instance of
`VertexOperatorAlgebra LatModule`, with central charge `1 = rank A₁`.  The general charge-pair
locality gate of `latticeVOA_A1_of_locality` is discharged by the proven `Yemα_local`. -/
noncomputable def latticeVOA_A1 : VertexOperatorAlgebra LatModule :=
  latticeVOA_A1_of_locality Yemα_local

/-- **The central charge of `𝒱(A₁)` is `1`** (the rank of `A₁`). -/
theorem latticeVOA_A1_centralCharge : latticeVOA_A1.centralCharge = 1 := rfl

/-- The vertex map of `𝒱(A₁)` is the reconstructed all-states map `Yfull`. -/
theorem latticeVOA_A1_Y : latticeVOA_A1.Y = Yfull Yemα_local := rfl

end VOA.LatExp

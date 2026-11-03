/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Foundations.CartanLattices
import VOA.Examples.LatticeGenInstance
import VOA.Core.LieAlgebraV1

/-!
# Lattice VOAs of the simply-laced Deligne types and their weight-one Lie algebras

For each simply-laced Deligne type `A₂, D₄, E₆, E₇, E₈`, the root lattice of
`VOA.CartanLattices` is even and positive-definite, so `LatGen.latticeVOAGen` gives a genuine
`VertexOperatorAlgebra` of central charge the rank.  Its weight-one space carries the
`LieAlgebra ℂ` structure `[u, v] = u₍₀₎v` of `VOA.Core.LieAlgebraV1`, with Jacobi and
antisymmetry coming from the VOA axioms, so no structure-constant table is checked.

**Not proved here; proved downstream.**  Simplicity of each of these Lie algebras is proved in
`AffineGeneral/CartanLatticeSimple.lean` (the `LieAlgebra.IsSimple` instances for `a2Lie`, …,
`e8Lie`), and the dimensions `28, 78, 133, 248` in `AffineGeneral/RootCounts.lean`
(`finrank_d4Lie`, `finrank_e6Lie`, `finrank_e7Lie`, `finrank_e8Lie'`; also `E8Dim.finrank_e8Lie` in
`E8Dimension.lean`).
No `finrank a2Lie = 8` lemma is stated.  This file only supplies the objects.
-/

namespace VOA.DeligneLatticeLie

open VOA.CartanLattices VOA.LatGen

noncomputable section

/-- A Cartan lattice on `Fin n → ℤ` has rank `n`. -/
theorem rank_ofCartan {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm) :
    IntegralLattice.rank (ofCartan G hG) = n := by
  change Module.finrank ℤ (Fin n → ℤ) = n
  exact Module.finrank_fin_fun ℤ

/-- The lattice VOA `V_{A₂}`. -/
abbrev a2VOA : VertexOperatorAlgebra (LatModuleGen a2) :=
  latticeVOAGen a2 a2_even a2_posDef

/-- The weight-one Lie algebra of `V_{A₂}`. -/
abbrev a2Lie := a2VOA.grading 1

example : LieAlgebra ℂ a2Lie := inferInstance

theorem a2VOA_centralCharge : a2VOA.centralCharge = 2 := by
  rw [latticeVOAGen_centralCharge, a2, rank_ofCartan]
  norm_num

/-- The lattice VOA `V_{D₄}`. -/
abbrev d4VOA : VertexOperatorAlgebra (LatModuleGen d4) :=
  latticeVOAGen d4 d4_even d4_posDef

/-- The weight-one Lie algebra of `V_{D₄}`. -/
abbrev d4Lie := d4VOA.grading 1

example : LieAlgebra ℂ d4Lie := inferInstance

theorem d4VOA_centralCharge : d4VOA.centralCharge = 4 := by
  rw [latticeVOAGen_centralCharge, d4, rank_ofCartan]
  norm_num

/-- The lattice VOA `V_{E₆}`. -/
abbrev e6VOA : VertexOperatorAlgebra (LatModuleGen e6) :=
  latticeVOAGen e6 e6_even e6_posDef

/-- The weight-one Lie algebra of `V_{E₆}`. -/
abbrev e6Lie := e6VOA.grading 1

example : LieAlgebra ℂ e6Lie := inferInstance

theorem e6VOA_centralCharge : e6VOA.centralCharge = 6 := by
  rw [latticeVOAGen_centralCharge, e6, rank_ofCartan]
  norm_num

/-- The lattice VOA `V_{E₇}`. -/
abbrev e7VOA : VertexOperatorAlgebra (LatModuleGen e7) :=
  latticeVOAGen e7 e7_even e7_posDef

/-- The weight-one Lie algebra of `V_{E₇}`. -/
abbrev e7Lie := e7VOA.grading 1

example : LieAlgebra ℂ e7Lie := inferInstance

theorem e7VOA_centralCharge : e7VOA.centralCharge = 7 := by
  rw [latticeVOAGen_centralCharge, e7, rank_ofCartan]
  norm_num

/-- The lattice VOA `V_{E₈}`. -/
abbrev e8VOA : VertexOperatorAlgebra (LatModuleGen e8) :=
  latticeVOAGen e8 e8_even e8_posDef

/-- The weight-one Lie algebra of `V_{E₈}`. -/
abbrev e8Lie := e8VOA.grading 1

example : LieAlgebra ℂ e8Lie := inferInstance

theorem e8VOA_centralCharge : e8VOA.centralCharge = 8 := by
  rw [latticeVOAGen_centralCharge, e8, rank_ofCartan]
  norm_num

end

end VOA.DeligneLatticeLie

section AxiomAudit
open VOA.DeligneLatticeLie
#print axioms a2VOA_centralCharge
#print axioms d4VOA_centralCharge
#print axioms e6VOA_centralCharge
#print axioms e7VOA_centralCharge
#print axioms e8VOA_centralCharge
end AxiomAudit

/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMAssembly
import VOA.Examples.TripletWpTwoAMSparseBridge

/-!
# The unconditional `p = 2` Adamovic--Milas identity

This file is the state-level consumer of the independently audited screening, normal-product,
and Virasoro-coordinate evaluations.  The evaluator and assembly deliberately carry separate
copies of the collected 32-term ledger; their explicit comparison below is the final interface
between the sparse certificate and the Adamovic--Milas identity.
-/

namespace VOA.LatGen.WpTwoAMFinal

open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2
open VOA.LatGen.WpTwoAMClose
open VOA.LatGen.WpTwoAMAssembly
open VOA.LatGen.WpTwoAMSparseBridge
open VOA.LatGen.WpTwoVirasoroCoords

private noncomputable abbrev Ltwo : IntegralLattice := latP 2

/-- Reassemble the state identity from the collected normal-product ledger. -/
theorem amTwoCoordinateIdentity_of_hProductExpected (hp : 1 ≤ 2)
    (hH : (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2) =
      latStateGen Ltwo (evalAPoly hProductExpectedAssembly) 0) :
    AMTwoCoordinateIdentity hp := by
  rw [AMTwoCoordinateIdentity, Qwp_sq_neg_two_eq_schur hp, hH,
    virWordTwo_eq_reified hp [2, 2, 2, 2, 2] (by norm_num),
    amTwoRemainder_eq_reified hp]
  simp only [← latStateGen_smul_boson, ← latStateGen_add_boson]
  congr 1
  exact amTwo_polynomial_identity

/-- The evaluator and assembly copies of the 32-term ledger have the same evaluation.  This
comparison is kept explicit so neither side can be silently rewritten into the other upstream. -/
theorem eval_hProductExpected_eq_assembly :
    evalAPoly hProductExpected = evalAPoly hProductExpectedAssembly := by
  rfl

/-- The sparse certificate, transported across the independent assembly ledger. -/
theorem Htrip_neg_five_Htrip_eq_assembly (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2) =
      latStateGen Ltwo (evalAPoly hProductExpectedAssembly) 0 := by
  rw [Htrip_neg_five_Htrip_eq_expected hp, eval_hProductExpected_eq_assembly]

/-- Unconditional weight-ten coordinate identity for the lattice triplet at `p = 2`. -/
theorem amTwoCoordinateIdentity_two (hp : 1 ≤ 2) : AMTwoCoordinateIdentity hp :=
  amTwoCoordinateIdentity_of_hProductExpected hp (Htrip_neg_five_Htrip_eq_assembly hp)

/-- Unconditional Adamovic--Milas omega identity at `p = 2`, `m = 5`. -/
theorem amOmegaIdentity_two (hp : 1 ≤ 2) : AMOmegaIdentity 2 hp 5 :=
  amOmegaIdentity_two_of_coordinateIdentity hp (amTwoCoordinateIdentity_two hp)

end VOA.LatGen.WpTwoAMFinal

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMFinal.amTwoCoordinateIdentity_of_hProductExpected
#print axioms VOA.LatGen.WpTwoAMFinal.eval_hProductExpected_eq_assembly
#print axioms VOA.LatGen.WpTwoAMFinal.amTwoCoordinateIdentity_two
#print axioms VOA.LatGen.WpTwoAMFinal.amOmegaIdentity_two
end AxiomAudit

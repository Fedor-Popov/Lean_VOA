/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoMixedAssembly
import VOA.Examples.TripletWpTwoAMProof
import VOA.Examples.TripletWpTwoVirasoroCoords

/-!
# Closure of the remaining mixed `W(2)` coordinate at `p = 2`

This file proves the three neutral-coordinate formulas isolated by
`TripletWpTwoMixedAssembly`, and hence closes `ThreeCoordinateIdentitiesWp` for the lattice
object `tripletWVOA 2 hp`.  It does not identify that object with `SympFerm.tripletW2`.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open scoped TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open MvPolynomial

private theorem evalAWord_eq_vVar_prod :
    ∀ w : List ℕ, WpTwoVirasoroCoords.evalAWord w =
      (w.map fun i => vVar (latP 2) (alphaP 2) i).prod
  | [] => by simp [WpTwoVirasoroCoords.evalAWord, vacuumN]
  | i :: is => by
      rw [WpTwoVirasoroCoords.evalAWord, evalAWord_eq_vVar_prod is]
      rfl

private theorem eval_reify_two_two_eq_mixedLminusTwoOmegaFock :
    WpTwoVirasoroCoords.evalAPoly (WpTwoVirasoroCoords.reifyVirWord [2, 2]) =
      mixedLminusTwoOmegaFock := by
  simp [WpTwoVirasoroCoords.reifyVirWord, WpTwoVirasoroCoords.virActPoly,
    WpTwoVirasoroCoords.virActWord, WpTwoVirasoroCoords.virVacAPoly,
    WpTwoVirasoroCoords.scaleAPoly, WpTwoVirasoroCoords.prependA,
    WpTwoVirasoroCoords.evalAPoly, evalAWord_eq_vVar_prod,
    mixedLminusTwoOmegaFock]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring_nf
  simp only [mul_two_fock', MvPolynomial.smul_eq_C_mul]
  ring_nf
  have hquarter :
      MvPolynomial.C (2 : ℂ) * MvPolynomial.C (1 / 8 : ℂ) =
        (MvPolynomial.C (1 / 4 : ℂ) : FockN (rank (latP 2))) := by
    rw [← map_mul]
    norm_num
  have hsixteenth :
      MvPolynomial.C (2 : ℂ) * MvPolynomial.C (1 / 32 : ℂ) =
        (MvPolynomial.C (1 / 16 : ℂ) : FockN (rank (latP 2))) := by
    rw [← map_mul]
    norm_num
  linear_combination
    vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2 * hquarter +
      vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1 * hsixteenth

/-- The neutral coordinate of `L_{-2} omega` used by the middle mixed identity. -/
theorem LminusTwo_omegaTrip_two_eq_mixed (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (omegaTrip 2) =
      latStateGen (latP 2) mixedLminusTwoOmegaFock 0 := by
  rw [smul_omegaTrip_eq_L]
  have h := WpTwoVirasoroCoords.virWordTwo_eq_reified hp [2, 2] (by norm_num)
  simp only [virWordTwo_cons, virWordTwo_nil] at h
  have homega :
      (tripletLatticeVOA 2 hp).L (-2) (latVacuumGen (latP 2)) = omegaTrip 2 := by
    change (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1)
      (tripletLatticeVOA 2 hp).vacuum = omegaTrip 2
    exact (tripletLatticeVOA 2 hp).toPreVertexAlgebra.smul_vacuum_neg_one (omegaTrip 2)
  norm_num only [Nat.cast_ofNat, neg_neg, Int.reduceNeg] at h
  rw [homega, eval_reify_two_two_eq_mixedLminusTwoOmegaFock] at h
  exact h

private theorem eval_reify_one_one_two_eq_mixedTSqOmegaFock :
    WpTwoVirasoroCoords.evalAPoly (WpTwoVirasoroCoords.reifyVirWord [1, 1, 2]) =
      mixedTSqOmegaFock := by
  simp [WpTwoVirasoroCoords.reifyVirWord, WpTwoVirasoroCoords.virActPoly,
    WpTwoVirasoroCoords.virActWord, WpTwoVirasoroCoords.virVacAPoly,
    WpTwoVirasoroCoords.scaleAPoly, WpTwoVirasoroCoords.prependA,
    WpTwoVirasoroCoords.evalAPoly, evalAWord_eq_vVar_prod,
    mixedTSqOmegaFock]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring_nf
  simp only [mul_two_fock', MvPolynomial.smul_eq_C_mul]
  ring_nf
  have hhalf :
      MvPolynomial.C (2 : ℂ) * MvPolynomial.C (1 / 4 : ℂ) =
        (MvPolynomial.C (1 / 2 : ℂ) : FockN (rank (latP 2))) := by
    rw [← map_mul]
    norm_num
  have hquarter :
      MvPolynomial.C (2 : ℂ) * MvPolynomial.C (1 / 8 : ℂ) =
        (MvPolynomial.C (1 / 4 : ℂ) : FockN (rank (latP 2))) := by
    rw [← map_mul]
    norm_num
  linear_combination
    vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2 * hhalf +
      vVar (latP 2) (alphaP 2) 1 ^ 2 * hquarter

/-- The neutral coordinate of `T^2 omega` used by the middle mixed identity. -/
theorem T_sq_omegaTrip_two_eq_mixed (hp : 1 ≤ 2) :
    ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (omegaTrip 2) =
      latStateGen (latP 2) mixedTSqOmegaFock 0 := by
  have h := WpTwoVirasoroCoords.virWordTwo_eq_reified hp [1, 1, 2] (by norm_num)
  simp only [virWordTwo_cons, virWordTwo_nil] at h
  have homega :
      (tripletLatticeVOA 2 hp).L (-2) (latVacuumGen (latP 2)) = omegaTrip 2 := by
    change (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1)
      (tripletLatticeVOA 2 hp).vacuum = omegaTrip 2
    exact (tripletLatticeVOA 2 hp).toPreVertexAlgebra.smul_vacuum_neg_one (omegaTrip 2)
  norm_num only [Nat.cast_ofNat, neg_neg, Int.reduceNeg] at h
  rw [homega, eval_reify_one_one_two_eq_mixedTSqOmegaFock] at h
  rw [VertexOperatorAlgebra.T_eq_Lneg1, pow_two, Module.End.mul_apply]
  exact h

private theorem LSecBg_neg_mul_vVar (n : ℕ) (hn : 1 ≤ n) (i : ℕ)
    (q : FockN (rank (latP 2))) :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-(n : ℤ))
        (vVar (latP 2) (alphaP 2) i * q) =
      vVar (latP 2) (alphaP 2) i *
          BgA.LSecBg (latP 2) (lamP 2) 0 (-(n : ℤ)) q +
        ((i : ℂ) + 1) • (vVar (latP 2) (alphaP 2) (i + n) * q) := by
  simpa using WpTwoAMProof.LSecBg_neg_mul_ATwo n hn i q

private theorem LSecBg_neg_one_mul_vVar (i : ℕ) (q : FockN (rank (latP 2))) :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1)
        (vVar (latP 2) (alphaP 2) i * q) =
      vVar (latP 2) (alphaP 2) i *
          BgA.LSecBg (latP 2) (lamP 2) 0 (-1) q +
        ((i : ℂ) + 1) • (vVar (latP 2) (alphaP 2) (i + 1) * q) := by
  simpa using LSecBg_neg_mul_vVar 1 (by norm_num) i q

private theorem LSecBg_neg_one_vVar (i : ℕ) :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1) (vVar (latP 2) (alphaP 2) i) =
      ((i : ℂ) + 1) • vVar (latP 2) (alphaP 2) (i + 1) := by
  rw [show vVar (latP 2) (alphaP 2) i =
      vVar (latP 2) (alphaP 2) i * vacuumN (rank (latP 2)) by simp [vacuumN],
    LSecBg_neg_one_mul_vVar i,
    WpTwoAMProof.LSecBg_neg_one_vacuum]
  simp [vacuumN]

private theorem LSecBg_neg_one_vVar_zero_sq :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1)
        (vVar (latP 2) (alphaP 2) 0 ^ 2) =
      (2 : ℂ) •
        (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 1) := by
  rw [pow_two, LSecBg_neg_one_mul_vVar 0,
    LSecBg_neg_one_vVar]
  norm_num
  rw [mul_comm (vVar (latP 2) (alphaP 2) 1) (vVar (latP 2) (alphaP 2) 0)]
  module

private theorem LSecBg_neg_one_vVar_zero_cube :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1)
        (vVar (latP 2) (alphaP 2) 0 ^ 3) =
      (3 : ℂ) •
        (vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1) := by
  rw [show vVar (latP 2) (alphaP 2) 0 ^ 3 =
      vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 0 ^ 2 by ring,
    LSecBg_neg_one_mul_vVar 0,
    LSecBg_neg_one_vVar_zero_sq]
  norm_num
  have hleft :
      vVar (latP 2) (alphaP 2) 0 *
          (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 1) =
        vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1 := by ring
  have hright :
      vVar (latP 2) (alphaP 2) 1 * vVar (latP 2) (alphaP 2) 0 ^ 2 =
        vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1 := by ring
  rw [hleft, hright]
  module

private theorem LSecBg_neg_one_vVar_zero_mul_one :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1)
        (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 1) =
      vVar (latP 2) (alphaP 2) 1 ^ 2 +
        (2 : ℂ) •
          (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2) := by
  rw [LSecBg_neg_one_mul_vVar 0,
    LSecBg_neg_one_vVar]
  norm_num
  ring

private theorem LSecBg_neg_one_vSchur_three_eq_mixedTHFock :
    BgA.LSecBg (latP 2) (lamP 2) 0 (-1)
        (vSchur (latP 2) (alphaP 2) 3) = mixedTHFock := by
  rw [vSchur_three']
  simp only [map_add, map_smul, LSecBg_neg_one_vVar_zero_cube,
    LSecBg_neg_one_vVar_zero_mul_one, LSecBg_neg_one_vVar]
  norm_num
  module

/-- The neutral coordinate of `T H`; the cocycle orientation
`epsilon(alpha,-alpha) = tripletTwoC` is kept explicit. -/
theorem T_Htrip_two_eq_mixed (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T (Htrip 2) =
      tripletTwoC • latStateGen (latP 2) mixedTHFock 0 := by
  rw [Htrip, Screen.Hscr_eq (latP 2) (alphaP 2) 2 hp (latP_form_alpha 2), map_smul]
  rw [show latStateGen (latP 2) (vSchur (latP 2) (alphaP 2) (2 * 2 - 1)) 0 =
      mkEα (latP 2) 0 (vSchur (latP 2) (alphaP 2) 3) by rfl]
  rw [← pow_one (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T,
    WpTwoAMProof.T_pow_mkE_zero hp 1 (vSchur (latP 2) (alphaP 2) 3),
    pow_one, LSecBg_neg_one_vSchur_three_eq_mixedTHFock]
  rfl

/-- Unconditional closure of the three finite mixed coordinates for the lattice triplet at
`p = 2`. -/
theorem threeCoordinateIdentitiesWp_two (hp : 1 ≤ 2) :
    ThreeCoordinateIdentitiesWp hp :=
  threeCoordinateIdentitiesWp_two_of_coordinates hp
    (LminusTwo_omegaTrip_two_eq_mixed hp)
    (T_sq_omegaTrip_two_eq_mixed hp)
    (T_Htrip_two_eq_mixed hp)

/-- All seven mixed screening pairs close in the triplet-generated span at `p = 2`. -/
theorem mixedPairsWp_two (hp : 1 ≤ 2) : MixedPairsWp 2 hp :=
  mixedPairsWp_of_loweringPairs 2 hp
    (loweringPairsWp_two_of_three_coordinate_identities hp
      (threeCoordinateIdentitiesWp_two hp))

end VOA.LatGen.WpC2

section AxiomAudit
#print axioms VOA.LatGen.WpC2.threeCoordinateIdentitiesWp_two
#print axioms VOA.LatGen.WpC2.mixedPairsWp_two
end AxiomAudit

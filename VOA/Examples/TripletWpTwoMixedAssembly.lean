/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoMixed
import VOA.Examples.TripletWpTwoAMCoords

/-!
# Reassembly of the three mixed `W(2)` coordinates

This file transports the finite Fock calculations in `TripletWpTwoMixed` through available
invariant Virasoro coordinates.  It proves the `F_(0)H` and `F_(3)E` identities unconditionally.
The `F_(1)E` identity, and hence the combined `ThreeCoordinateIdentitiesWp` certificate, remain
conditional on three explicit neutral-sector coordinate hypotheses `hL`, `hT`, and `hH`.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open scoped TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open MvPolynomial

noncomputable abbrev mixedLminusTwoOmegaFock : FockN (rank (latP 2)) :=
  (1 / 64 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 4 +
    (1 / 16 : ℂ) •
      (vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1) +
      (1 / 4 : ℂ) •
        (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2) +
        (1 / 16 : ℂ) • vVar (latP 2) (alphaP 2) 1 ^ 2 +
          (1 / 2 : ℂ) • vVar (latP 2) (alphaP 2) 3

noncomputable abbrev mixedTSqOmegaFock : FockN (rank (latP 2)) :=
  (1 / 2 : ℂ) •
      (vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2) +
    (1 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1 ^ 2 +
      (3 / 2 : ℂ) • vVar (latP 2) (alphaP 2) 3

noncomputable abbrev mixedTHFock : FockN (rank (latP 2)) :=
  (1 / 2 : ℂ) •
      (vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1) +
    vVar (latP 2) (alphaP 2) 0 * vVar (latP 2) (alphaP 2) 2 +
      (1 / 2 : ℂ) • vVar (latP 2) (alphaP 2) 1 ^ 2 +
        vVar (latP 2) (alphaP 2) 3

theorem Ftrip_zero_Htrip_two_explicit (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 0 (Htrip 2) =
      ((48 : ℂ) / 5 * tripletTwoC) •
          (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (Ftrip 2) +
        ((4 : ℂ) / 5 * tripletTwoC) •
          ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (Ftrip 2) := by
  rw [smul_Ftrip_Htrip_eq_fock 2 hp 0]
  norm_num only [neg_zero, zero_sub]
  rw [EEVec_neg_alpha_neg_one_S3, smul_omegaTrip_eq_L]
  norm_num only [Int.reduceSub]
  rw [
    WpTwoAMCoords.LminusTwo_Ftrip_two_eq_vVar,
    WpTwoAMCoords.T_sq_Ftrip_two_eq_vVar]
  rw [← latStateGen_smul_boson, ← latStateGen_smul_boson,
    ← latStateGen_smul_boson, ← latStateGen_add_boson]
  congr 1
  module

theorem Ftrip_three_Etrip_two_explicit (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 3 (Etrip 2) =
      (-48 * (tripletTwoC * tripletTwoD)) • omegaTrip 2 := by
  rw [smul_Ftrip_Etrip_eq_fock 2 hp 3]
  norm_num only [Int.ofNat_eq_natCast, Int.reduceMul, Int.reduceSub]
  rw [EEVec_neg_alpha_zero_inner, WpTwoAMCoords.omegaTrip_two_eq_vVar_state]
  rw [← latStateGen_smul_boson, ← latStateGen_smul_boson,
    ← latStateGen_smul_boson]
  congr 1
  module

/-- Coordinate-independent reassembly of the middle mixed identity.  The three explicit hypotheses
are precisely the still-required invariant neutral-sector formulas; isolating them here records the
conditional boundary and makes the cocycle orientation in the final comparison explicit. -/
theorem Ftrip_one_Etrip_two_explicit_of_coordinates (hp : 1 ≤ 2)
    (hL : (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (omegaTrip 2) =
      latStateGen (latP 2) mixedLminusTwoOmegaFock 0)
    (hT : ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (omegaTrip 2) =
      latStateGen (latP 2) mixedTSqOmegaFock 0)
    (hH : (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T (Htrip 2) =
      tripletTwoC • latStateGen (latP 2) mixedTHFock 0) :
    (tripletLatticeVOA 2 hp).smul (Ftrip 2) 1 (Etrip 2) =
      (-64 * (tripletTwoC * tripletTwoD)) •
          (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (omegaTrip 2) +
        (12 * (tripletTwoC * tripletTwoD)) •
          ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (omegaTrip 2) +
          (10 * tripletTwoD) •
            (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T (Htrip 2) := by
  rw [smul_Ftrip_Etrip_eq_fock 2 hp 1]
  norm_num only [Int.ofNat_eq_natCast, Int.reduceMul, Int.reduceSub]
  rw [EEVec_neg_alpha_two_inner, hL, hT, hH]
  simp only [← latStateGen_smul_boson, ← latStateGen_add_boson, smul_smul]
  congr 1
  module

theorem threeExplicitMixedIdentitiesWp_two_of_coordinates (hp : 1 ≤ 2)
    (hL : (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (omegaTrip 2) =
      latStateGen (latP 2) mixedLminusTwoOmegaFock 0)
    (hT : ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (omegaTrip 2) =
      latStateGen (latP 2) mixedTSqOmegaFock 0)
    (hH : (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T (Htrip 2) =
      tripletTwoC • latStateGen (latP 2) mixedTHFock 0) :
    ThreeExplicitMixedIdentitiesWp hp := by
  refine ⟨Ftrip_zero_Htrip_two_explicit hp,
    Ftrip_one_Etrip_two_explicit_of_coordinates hp hL hT hH,
    Ftrip_three_Etrip_two_explicit hp⟩

theorem threeCoordinateIdentitiesWp_two_of_coordinates (hp : 1 ≤ 2)
    (hL : (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (-1) (omegaTrip 2) =
      latStateGen (latP 2) mixedLminusTwoOmegaFock 0)
    (hT : ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (omegaTrip 2) =
      latStateGen (latP 2) mixedTSqOmegaFock 0)
    (hH : (tripletLatticeVOA 2 hp).toPreVertexAlgebra.T (Htrip 2) =
      tripletTwoC • latStateGen (latP 2) mixedTHFock 0) :
    ThreeCoordinateIdentitiesWp hp :=
  threeCoordinateIdentitiesWp_of_explicit hp
    (threeExplicitMixedIdentitiesWp_two_of_coordinates hp hL hT hH)

end VOA.LatGen.WpC2

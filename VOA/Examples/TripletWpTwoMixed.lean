/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpPairClosure

/-!
# The three mixed-screening coordinates for the lattice triplet `W(2)`

This file is about the lattice-screening object `tripletWVOA 2 hp`.  It does not use, or identify
that object with, the separate symplectic-fermion even part `SympFerm.tripletW2`.

The three coordinates left by `loweringPairsWp_two_of_three` have the following normalizations.
Put `c = epsilon(alpha,-alpha)` and `d = epsilon(-alpha,alpha)`.  Direct rank-one Fock expansion
gives

* `F_(0)H = (48c/5) L_{-2}F + (4c/5) T^2 F`;
* `F_(1)E = -64cd L_{-2}omega + 12cd T^2 omega + 10d T H`;
* `F_(3)E = -48cd omega`.

The theorem at the end packages those three identities into the exact downstream interface
`ThreeCoordinateIdentitiesWp`.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpC2

open scoped TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open MvPolynomial

/-- The cocycle orientation in `H = c S_3(alpha)` and in the left action of `F`. -/
noncomputable abbrev tripletTwoC : ℂ :=
  latticeCocycle (latP 2) (alphaP 2) (-alphaP 2)

/-- The opposite cocycle orientation introduced by the inner charge shift in `F_(j)E`. -/
noncomputable abbrev tripletTwoD : ℂ :=
  latticeCocycle (latP 2) (-alphaP 2) (alphaP 2)

/-! ## A bounded charge-dressing expansion -/

/-- On a bosonic Fock vector of weight `w`, the convolution defining `EE(alpha)_s` is the finite
interval `max 0 s <= m <= w+s`. -/
theorem EEVec_eq_weight_bounded_sum' (L : IntegralLattice) (alpha : L.carrier) (s : ℤ)
    {w : ℕ} {x : FockN (rank L)} (hx : x ∈ gradingWN (rank L) w) :
    EEVec L alpha s x = ∑ m ∈ Finset.Icc (max 0 s) ((w : ℤ) + s),
      vSchur L alpha m.toNat * aExpVec L alpha (m - s).toNat x := by
  rw [EEVec_apply_conv L alpha s x]
  let f : ℤ → FockN (rank L) := fun m =>
    EminusVecField L alpha m (EplusVecField L alpha (s - m) x)
  have hsupp : Function.support f ⊆ Finset.Icc (max 0 s) ((w : ℤ) + s) := by
    intro m hm
    rw [Function.mem_support] at hm
    have hm0 : 0 ≤ m := by
      by_contra h
      rw [show f m = EminusVecField L alpha m (EplusVecField L alpha (s - m) x) from rfl,
        EminusVecField_neg L alpha (by omega), LinearMap.zero_apply] at hm
      exact hm rfl
    have hsm : s ≤ m := by
      by_contra h
      rw [show f m = EminusVecField L alpha m (EplusVecField L alpha (s - m) x) from rfl,
        EplusVecField_apply, if_neg (by omega), LinearMap.zero_apply, map_zero] at hm
      exact hm rfl
    have hmws : m ≤ (w : ℤ) + s := by
      by_contra h
      have hgrade := aExpVec_mem_gradingZN L alpha (m - s).toNat hx
      have hneg : (w : ℤ) - ((m - s).toNat : ℤ) < 0 := by omega
      rw [gradingZN_of_neg hneg, Submodule.mem_bot] at hgrade
      rw [show f m = EminusVecField L alpha m (EplusVecField L alpha (s - m) x) from rfl,
        EplusVecField_nonpos L alpha (by omega),
        show (-(s - m)).toNat = (m - s).toNat by ring, hgrade, map_zero] at hm
      exact hm rfl
    exact Finset.mem_Icc.mpr ⟨by omega, hmws⟩
  rw [show (fun m : ℤ => EminusVecField L alpha m (EplusVecField L alpha (s - m) x)) = f from rfl,
    finsum_eq_sum_of_support_subset f hsupp]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hmlo, _hmhi⟩ := Finset.mem_Icc.mp hm
  have hm0 : 0 ≤ m := le_trans (le_max_left 0 s) hmlo
  have hsm : s ≤ m := le_trans (le_max_right 0 s) hmlo
  rw [show f m = EminusVecField L alpha m (EplusVecField L alpha (s - m) x) from rfl,
    EminusVecField_apply, if_pos hm0, EplusVecField_nonpos L alpha (by omega),
    show (-(s - m)).toNat = (m - s).toNat by ring,
    EminusVec, LinearMap.mulLeft_apply]

/-! ## Low Schur and annihilation calculations -/

theorem chargeCoord_neg' (L : IntegralLattice) (alpha : L.carrier) (a : Fin (rank L)) :
    chargeCoord L (-alpha) a = -chargeCoord L alpha a := by
  have h := chargeCoord_add L alpha (-alpha) a
  rw [add_neg_cancel, chargeCoord_zero] at h
  linear_combination -h

theorem vVar_neg' (L : IntegralLattice) (alpha : L.carrier) (m : ℕ) :
    vVar L (-alpha) m = -vVar L alpha m := by
  rw [vVar, vVar, Finset.sum_congr rfl (fun a _ => by
    rw [chargeCoord_neg', neg_smul])]
  rw [Finset.sum_neg_distrib]

theorem vSchur_one' (L : IntegralLattice) (alpha : L.carrier) :
    vSchur L alpha 1 = vVar L alpha 0 := by
  rw [show 1 = 0 + 1 by omega, vSchur_succ, Finset.sum_range_one, vSchur_zero]
  norm_num

theorem vSchur_two' (L : IntegralLattice) (alpha : L.carrier) :
    vSchur L alpha 2 = (2 : ℂ)⁻¹ • vVar L alpha 0 ^ 2 +
      (2 : ℂ)⁻¹ • vVar L alpha 1 := by
  rw [show 2 = 1 + 1 by omega, vSchur_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_ofNat,
    Finset.sum_range_zero, zero_add, Nat.reduceSubDiff, vSchur_one', vSchur_zero,
    pow_two, mul_one]
  module

/-- A polynomial numeral on the right is the corresponding complex scalar action.  `ring_nf`
uses the former presentation, while `module` needs the latter. -/
theorem mul_natCast_fock' (r : ℕ) (p : FockN r) (n : ℕ) :
    p * (n : FockN r) = (n : ℂ) • p := by
  rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ]

theorem mul_two_fock' (r : ℕ) (p : FockN r) : p * 2 = (2 : ℂ) • p :=
  mul_natCast_fock' r p 2

theorem mul_four_fock' (r : ℕ) (p : FockN r) : p * 4 = (4 : ℂ) • p :=
  mul_natCast_fock' r p 4

theorem mul_six_fock' (r : ℕ) (p : FockN r) : p * 6 = (6 : ℂ) • p :=
  mul_natCast_fock' r p 6

theorem mul_eight_fock' (r : ℕ) (p : FockN r) : p * 8 = (8 : ℂ) • p :=
  mul_natCast_fock' r p 8

theorem mul_ten_fock' (r : ℕ) (p : FockN r) : p * 10 = (10 : ℂ) • p :=
  mul_natCast_fock' r p 10

theorem mul_twelve_fock' (r : ℕ) (p : FockN r) : p * 12 = (12 : ℂ) • p :=
  mul_natCast_fock' r p 12

theorem mul_fourteen_fock' (r : ℕ) (p : FockN r) : p * 14 = (14 : ℂ) • p :=
  mul_natCast_fock' r p 14

theorem mul_sixteen_fock' (r : ℕ) (p : FockN r) : p * 16 = (16 : ℂ) • p :=
  mul_natCast_fock' r p 16

theorem mul_twentyFour_fock' (r : ℕ) (p : FockN r) : p * 24 = (24 : ℂ) • p :=
  mul_natCast_fock' r p 24

theorem vSchur_three' (L : IntegralLattice) (alpha : L.carrier) :
    vSchur L alpha 3 = (1 / 6 : ℂ) • vVar L alpha 0 ^ 3 +
      (1 / 2 : ℂ) • (vVar L alpha 0 * vVar L alpha 1) +
        (1 / 3 : ℂ) • vVar L alpha 2 := by
  rw [show 3 = 2 + 1 by omega, vSchur_succ]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only [zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, vSchur_two',
    vSchur_one', vSchur_zero, mul_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

theorem vSchur_four' (L : IntegralLattice) (alpha : L.carrier) :
    vSchur L alpha 4 = (1 / 24 : ℂ) • vVar L alpha 0 ^ 4 +
      (1 / 4 : ℂ) • (vVar L alpha 0 ^ 2 * vVar L alpha 1) +
        (1 / 3 : ℂ) • (vVar L alpha 0 * vVar L alpha 2) +
          (1 / 8 : ℂ) • vVar L alpha 1 ^ 2 +
            (1 / 4 : ℂ) • vVar L alpha 3 := by
  rw [show 4 = 3 + 1 by omega, vSchur_succ]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, vSchur_three',
    vSchur_two', vSchur_one', vSchur_zero, mul_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

/-- Every positive charge oscillator is a derivation of the polynomial Fock product. -/
theorem chargeOsc_mul' (L : IntegralLattice) (beta : L.carrier) {n : ℤ} (hn : 0 < n)
    (x y : FockN (rank L)) :
    chargeOsc L beta n (x * y) = chargeOsc L beta n x * y + x * chargeOsc L beta n y := by
  simp only [chargeOsc, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    HeisenbergN.oscN_apply_pos (rank L) 1 _ hn, one_smul, pderiv_mul, smul_add,
    MvPolynomial.smul_eq_C_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

theorem aExpVec_one_vSchur_three (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    aExpVec L beta 1 (vSchur L alpha 3) =
      -((L.form alpha beta : ℤ) : ℂ) • vSchur L alpha 2 := by
  rw [show 1 = 0 + 1 by omega, aExpVec_succ, Finset.sum_range_one,
    aExpVec_zero, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.neg_apply]
  norm_num only [Nat.cast_zero, zero_add, inv_one, one_smul]
  change (-(chargeOsc L beta 1 (vSchur L alpha 3) : FockN (rank L))) = _
  have h := chargeOsc_vSchur L hPos alpha beta 1 3 (by omega)
  norm_num at h
  rw [h]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

theorem aExpVec_two_vSchur_three (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    aExpVec L beta 2 (vSchur L alpha 3) =
      (((L.form alpha beta : ℤ) : ℂ) *
        (((L.form alpha beta : ℤ) : ℂ) - 1) / 2) • vSchur L alpha 1 := by
  rw [show 2 = 1 + 1 by omega, aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 2 : ℂ) •
      (-(chargeOsc L beta 1 (aExpVec L beta 1 (vSchur L alpha 3))) +
        -(chargeOsc L beta 2 (vSchur L alpha 3))) = _
  rw [aExpVec_one_vSchur_three L hPos alpha beta, map_smul]
  have h1 := chargeOsc_vSchur L hPos alpha beta 1 2 (by omega)
  have h2 := chargeOsc_vSchur L hPos alpha beta 2 3 (by omega)
  norm_num at h1 h2
  rw [h1, h2]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

theorem aExpVec_three_vSchur_three (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    aExpVec L beta 3 (vSchur L alpha 3) =
      (-((L.form alpha beta : ℤ) : ℂ) *
        (((L.form alpha beta : ℤ) : ℂ) - 1) *
          (((L.form alpha beta : ℤ) : ℂ) - 2) / 6) • vSchur L alpha 0 := by
  rw [show 3 = 2 + 1 by omega, aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 3 : ℂ) •
      (-(chargeOsc L beta 1 (aExpVec L beta 2 (vSchur L alpha 3))) +
          -(chargeOsc L beta 2 (aExpVec L beta 1 (vSchur L alpha 3))) +
        -(chargeOsc L beta 3 (vSchur L alpha 3))) = _
  rw [aExpVec_two_vSchur_three L hPos alpha beta,
    aExpVec_one_vSchur_three L hPos alpha beta, map_smul, map_smul]
  have h1 := chargeOsc_vSchur L hPos alpha beta 1 1 (by omega)
  have h2 := chargeOsc_vSchur L hPos alpha beta 2 2 (by omega)
  have h3 := chargeOsc_vSchur L hPos alpha beta 3 3 (by omega)
  norm_num at h1 h2 h3
  rw [h1, h2, h3]
  module

theorem sum_Icc_zero_two {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (0 : ℤ) 2, f m = f 0 + f 1 + f 2 := by
  have h : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

theorem sum_Icc_two_four {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (2 : ℤ) 4, f m = f 2 + f 3 + f 4 := by
  have h : Finset.Icc (2 : ℤ) 4 = {2, 3, 4} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

/-- The full `s = -1` charge dressing of `S_3(alpha)`, reduced to three Schur products. -/
theorem EEVec_neg_one_vSchur_three (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    EEVec L beta (-1) (vSchur L alpha 3) =
      -((L.form alpha beta : ℤ) : ℂ) • vSchur L alpha 2 +
        (((L.form alpha beta : ℤ) : ℂ) *
          (((L.form alpha beta : ℤ) : ℂ) - 1) / 2) •
            (vSchur L beta 1 * vSchur L alpha 1) +
        (-((L.form alpha beta : ℤ) : ℂ) *
          (((L.form alpha beta : ℤ) : ℂ) - 1) *
            (((L.form alpha beta : ℤ) : ℂ) - 2) / 6) • vSchur L beta 2 := by
  rw [EEVec_eq_weight_bounded_sum' L beta (-1)
    (Screen.vSchur_mem_gradingWN L alpha 3)]
  rw [show max (0 : ℤ) (-1) = 0 by norm_num,
    show ((3 : ℕ) : ℤ) + (-1) = 2 by norm_num, sum_Icc_zero_two]
  have hto0 : (0 : ℤ).toNat = 0 := rfl
  have hto1 : (1 : ℤ).toNat = 1 := rfl
  have hto2 : (2 : ℤ).toNat = 2 := rfl
  have h01 : ((0 : ℤ) - (-1)).toNat = 1 := rfl
  have h11 : ((1 : ℤ) - (-1)).toNat = 2 := rfl
  have h21 : ((2 : ℤ) - (-1)).toNat = 3 := rfl
  rw [hto0, hto1, hto2, h01, h11, h21]
  norm_num only [Int.toNat_zero, Int.reduceNeg, Int.reduceSub,
    vSchur_zero, one_mul, aExpVec_one_vSchur_three L hPos alpha beta,
    aExpVec_two_vSchur_three L hPos alpha beta,
    aExpVec_three_vSchur_three L hPos alpha beta]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf

/-- The `F_(0)H` Fock polynomial before its cocycle scalar is restored. -/
theorem EEVec_neg_alpha_neg_one_S3 :
    EEVec (latP 2) (-alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3) =
      (2 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2 -
        (8 : ℂ) • vVar (latP 2) (alphaP 2) 1 := by
  rw [EEVec_neg_one_vSchur_three (latP 2) (latP_posDef 2 (by omega))
    (alphaP 2) (-alphaP 2)]
  have hform : (latP 2).form (alphaP 2) (-alphaP 2) = -4 := by
    rw [map_neg, latP_form_alpha]
    norm_num
  rw [hform]
  norm_num only [Int.cast_negSucc, Int.cast_ofNat, vSchur_one', vSchur_two', vVar_neg']
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

/-- The inner screening polynomial in `E = QH`. -/
theorem EEVec_alpha_neg_one_S3 :
    EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3) =
      (2 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2 -
        (4 : ℂ) • vVar (latP 2) (alphaP 2) 1 := by
  rw [EEVec_neg_one_vSchur_three (latP 2) (latP_posDef 2 (by omega))
    (alphaP 2) (alphaP 2), latP_form_alpha]
  norm_num only [Int.cast_ofNat, vSchur_one', vSchur_two']
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

theorem chargeOsc_one_vVar_zero (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    chargeOsc L beta 1 (vVar L alpha 0) =
      ((L.form alpha beta : ℤ) : ℂ) • (1 : FockN (rank L)) := by
  rw [← vSchur_one']
  have h := chargeOsc_vSchur L hPos alpha beta 1 1 (by omega)
  norm_num [vSchur_zero] at h
  exact h

theorem chargeOsc_two_vVar_zero (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    chargeOsc L beta 2 (vVar L alpha 0) = 0 := by
  rw [← vSchur_one']
  have h := chargeOsc_vSchur L hPos alpha beta 2 1 (by omega)
  norm_num at h
  exact h

theorem chargeOsc_one_vVar_one (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    chargeOsc L beta 1 (vVar L alpha 1) = 0 := by
  have h := congrArg (chargeOsc L beta 1) (vSchur_two' L alpha)
  rw [map_add, map_smul, map_smul, pow_two, chargeOsc_mul' L beta (by omega),
    chargeOsc_one_vVar_zero L hPos alpha beta] at h
  have hv := chargeOsc_vSchur L hPos alpha beta 1 2 (by omega)
  rw [if_pos (by omega)] at hv
  change chargeOsc L beta 1 (vSchur L alpha 2) =
    ((L.form alpha beta : ℤ) : ℂ) • vSchur L alpha 1 at hv
  rw [vSchur_one'] at hv
  rw [hv] at h
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul] at h
  have hdouble : (2 : ℂ)⁻¹ •
      (((L.form alpha beta : ℤ) : ℂ) • vVar L alpha 0 +
        ((L.form alpha beta : ℤ) : ℂ) • vVar L alpha 0) =
      ((L.form alpha beta : ℤ) : ℂ) • vVar L alpha 0 := by
    module
  rw [hdouble] at h
  have hhalf : (2 : ℂ)⁻¹ • chargeOsc L beta 1 (vVar L alpha 1) = 0 := by
    apply add_left_cancel (a := ((L.form alpha beta : ℤ) : ℂ) • vVar L alpha 0)
    simpa only [add_zero] using h.symm
  calc
    chargeOsc L beta 1 (vVar L alpha 1) =
        (2 : ℂ) • ((2 : ℂ)⁻¹ • chargeOsc L beta 1 (vVar L alpha 1)) := by module
    _ = 0 := by rw [hhalf, smul_zero]

theorem chargeOsc_two_vVar_one (L : IntegralLattice) (hPos : L.PosDef)
    (alpha beta : L.carrier) :
    chargeOsc L beta 2 (vVar L alpha 1) =
      (2 * ((L.form alpha beta : ℤ) : ℂ)) • (1 : FockN (rank L)) := by
  have h := congrArg (chargeOsc L beta 2) (vSchur_two' L alpha)
  rw [map_add, map_smul, map_smul, pow_two, chargeOsc_mul' L beta (by omega),
    chargeOsc_two_vVar_zero L hPos alpha beta] at h
  have hv := chargeOsc_vSchur L hPos alpha beta 2 2 (by omega)
  rw [if_pos (by omega)] at hv
  change chargeOsc L beta 2 (vSchur L alpha 2) =
    ((L.form alpha beta : ℤ) : ℂ) • vSchur L alpha 0 at hv
  rw [vSchur_zero] at hv
  rw [hv] at h
  simp only [zero_mul, mul_zero, zero_add, zero_smul, smul_zero] at h
  calc
    chargeOsc L beta 2 (vVar L alpha 1) =
        (2 : ℂ) • ((2 : ℂ)⁻¹ • chargeOsc L beta 2 (vVar L alpha 1)) := by module
    _ = (2 : ℂ) • (((L.form alpha beta : ℤ) : ℂ) •
        (1 : FockN (rank L))) := by rw [← h]
    _ = (2 * ((L.form alpha beta : ℤ) : ℂ)) •
        (1 : FockN (rank L)) := by rw [smul_smul]

theorem aExpVec_neg_alpha_one_inner :
    aExpVec (latP 2) (-alphaP 2) 1
      (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)) =
        (16 : ℂ) • vVar (latP 2) (alphaP 2) 0 := by
  have hPos2 : (latP 2).PosDef := latP_posDef 2 (by omega)
  rw [show 1 = 0 + 1 by omega, aExpVec_succ, Finset.sum_range_one,
    aExpVec_zero, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.neg_apply]
  norm_num only [Nat.cast_zero, zero_add, inv_one, one_smul]
  change -(chargeOsc (latP 2) (-alphaP 2) 1
    (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3))) = _
  rw [EEVec_alpha_neg_one_S3, map_sub, map_smul, map_smul,
    pow_two,
    chargeOsc_mul' (latP 2) (-alphaP 2) (by omega),
    chargeOsc_one_vVar_zero (latP 2) hPos2
      (alphaP 2) (-alphaP 2),
    chargeOsc_one_vVar_one (latP 2) hPos2
      (alphaP 2) (-alphaP 2)]
  rw [show (latP 2).form (alphaP 2) (-alphaP 2) = -4 by
    rw [map_neg, latP_form_alpha]; norm_num]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

theorem aExpVec_neg_alpha_two_inner :
    aExpVec (latP 2) (-alphaP 2) 2
      (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)) =
        (16 : ℂ) • (1 : FockN (rank (latP 2))) := by
  have hPos2 : (latP 2).PosDef := latP_posDef 2 (by omega)
  rw [show 2 = 1 + 1 by omega, aExpVec_succ]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat, Nat.reduceSubDiff, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, aExpVec_zero,
    LinearMap.id_apply]
  change (1 / 2 : ℂ) •
    (-(chargeOsc (latP 2) (-alphaP 2) 1
        (aExpVec (latP 2) (-alphaP 2) 1
          (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)))) +
      -(chargeOsc (latP 2) (-alphaP 2) 2
        (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)))) = _
  rw [aExpVec_neg_alpha_one_inner, map_smul, EEVec_alpha_neg_one_S3,
    map_sub, map_smul, map_smul, pow_two,
    chargeOsc_mul' (latP 2) (-alphaP 2) (by omega),
    chargeOsc_two_vVar_zero (latP 2) hPos2
      (alphaP 2) (-alphaP 2),
    chargeOsc_two_vVar_one (latP 2) hPos2
      (alphaP 2) (-alphaP 2),
    chargeOsc_one_vVar_zero (latP 2) hPos2
      (alphaP 2) (-alphaP 2)]
  rw [show (latP 2).form (alphaP 2) (-alphaP 2) = -4 by
    rw [map_neg, latP_form_alpha]; norm_num]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  have h8 : (8 : FockN (rank (latP 2))) =
      (8 : ℂ) • (1 : FockN (rank (latP 2))) := by
    calc
      (8 : FockN (rank (latP 2))) = (1 : FockN (rank (latP 2))) * 8 := by rw [one_mul]
      _ = (8 : ℂ) • (1 : FockN (rank (latP 2))) :=
        mul_eight_fock' (rank (latP 2)) 1
  have h16 : (16 : FockN (rank (latP 2))) =
      (16 : ℂ) • (1 : FockN (rank (latP 2))) := by
    calc
      (16 : FockN (rank (latP 2))) = (1 : FockN (rank (latP 2))) * 16 := by rw [one_mul]
      _ = (16 : ℂ) • (1 : FockN (rank (latP 2))) :=
        mul_sixteen_fock' (rank (latP 2)) 1
  simp only [h8, h16]
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

/-- The charge-zero Fock polynomial of `F_(3)E`, before the two cocycle scalars. -/
theorem EEVec_neg_alpha_zero_inner :
    EEVec (latP 2) (-alphaP 2) 0
      (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)) =
        (-6 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2 -
          (12 : ℂ) • vVar (latP 2) (alphaP 2) 1 := by
  have hxZ := Screen.EEVec_mem_gradingZN_of_gradingWN (latP 2) (alphaP 2) (-1)
    (Screen.vSchur_mem_gradingWN (latP 2) (alphaP 2) 3)
  have hx : EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)
      ∈ gradingWN (rank (latP 2)) 2 := by
    rw [show ((3 : ℕ) : ℤ) + (-1) = 2 by norm_num,
      gradingZN_of_nonneg (by norm_num)] at hxZ
    norm_num at hxZ
    exact hxZ
  rw [EEVec_eq_weight_bounded_sum' (latP 2) (-alphaP 2) 0 hx]
  rw [show max (0 : ℤ) 0 = 0 by norm_num,
    show ((2 : ℕ) : ℤ) + 0 = 2 by norm_num, sum_Icc_zero_two]
  have hto0 : (0 : ℤ).toNat = 0 := rfl
  have hto1 : (1 : ℤ).toNat = 1 := rfl
  have hto2 : (2 : ℤ).toNat = 2 := rfl
  have h00 : ((0 : ℤ) - 0).toNat = 0 := rfl
  have h10 : ((1 : ℤ) - 0).toNat = 1 := rfl
  have h20 : ((2 : ℤ) - 0).toNat = 2 := rfl
  rw [hto0, hto1, hto2, h00, h10, h20,
    aExpVec_neg_alpha_one_inner, aExpVec_neg_alpha_two_inner,
    EEVec_alpha_neg_one_S3]
  norm_num [vSchur_zero,
    one_mul, aExpVec_zero, LinearMap.id_apply, aExpVec_neg_alpha_one_inner,
    aExpVec_neg_alpha_two_inner, vSchur_one', vSchur_two', vVar_neg',
    EEVec_alpha_neg_one_S3]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

/-- The charge-zero Fock polynomial of `F_(1)E`, before the two cocycle scalars. -/
theorem EEVec_neg_alpha_two_inner :
    EEVec (latP 2) (-alphaP 2) 2
      (EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)) =
        -(vVar (latP 2) (alphaP 2) 0 ^ 4) +
          vVar (latP 2) (alphaP 2) 0 ^ 2 * vVar (latP 2) (alphaP 2) 1 +
            (4 : ℂ) • vVar (latP 2) (alphaP 2) 1 ^ 2 -
              (4 : ℂ) • vVar (latP 2) (alphaP 2) 3 := by
  have hxZ := Screen.EEVec_mem_gradingZN_of_gradingWN (latP 2) (alphaP 2) (-1)
    (Screen.vSchur_mem_gradingWN (latP 2) (alphaP 2) 3)
  have hx : EEVec (latP 2) (alphaP 2) (-1) (vSchur (latP 2) (alphaP 2) 3)
      ∈ gradingWN (rank (latP 2)) 2 := by
    rw [show ((3 : ℕ) : ℤ) + (-1) = 2 by norm_num,
      gradingZN_of_nonneg (by norm_num)] at hxZ
    norm_num at hxZ
    exact hxZ
  rw [EEVec_eq_weight_bounded_sum' (latP 2) (-alphaP 2) 2 hx]
  rw [show max (0 : ℤ) 2 = 2 by norm_num,
    show ((2 : ℕ) : ℤ) + 2 = 4 by norm_num, sum_Icc_two_four]
  have hto2 : (2 : ℤ).toNat = 2 := rfl
  have hto3 : (3 : ℤ).toNat = 3 := rfl
  have hto4 : (4 : ℤ).toNat = 4 := rfl
  have h22 : ((2 : ℤ) - 2).toNat = 0 := rfl
  have h32 : ((3 : ℤ) - 2).toNat = 1 := rfl
  have h42 : ((4 : ℤ) - 2).toNat = 2 := rfl
  rw [hto2, hto3, hto4, h22, h32, h42, aExpVec_neg_alpha_one_inner,
    aExpVec_neg_alpha_two_inner, EEVec_alpha_neg_one_S3]
  norm_num [aExpVec_zero, LinearMap.id_apply,
    aExpVec_neg_alpha_one_inner, aExpVec_neg_alpha_two_inner, vSchur_two',
    vSchur_three', vSchur_four', vVar_neg', EEVec_alpha_neg_one_S3]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_inv₀, map_div₀, map_one,
    map_neg, map_ofNat]
  ring_nf
  simp only [MvPolynomial.C_eq_smul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_pow, one_pow, mul_two_fock', mul_four_fock',
    mul_six_fock', mul_eight_fock', mul_ten_fock', mul_twelve_fock',
    mul_fourteen_fock', mul_sixteen_fock', mul_twentyFour_fock']
  module

/-- The three exact vector identities, with their cocycle orientations exposed. -/
def ThreeExplicitMixedIdentitiesWp (hp : 1 ≤ 2) : Prop :=
  let W := tripletLatticeVOA 2 hp
  W.smul (Ftrip 2) 0 (Htrip 2) =
      ((48 : ℂ) / 5 * tripletTwoC) • W.smul (omegaTrip 2) (-1) (Ftrip 2) +
        ((4 : ℂ) / 5 * tripletTwoC) • (W.toPreVertexAlgebra.T ^ 2) (Ftrip 2) ∧
  W.smul (Ftrip 2) 1 (Etrip 2) =
      (-64 * (tripletTwoC * tripletTwoD)) • W.smul (omegaTrip 2) (-1) (omegaTrip 2) +
        (12 * (tripletTwoC * tripletTwoD)) • (W.toPreVertexAlgebra.T ^ 2) (omegaTrip 2) +
          (10 * tripletTwoD) • W.toPreVertexAlgebra.T (Htrip 2) ∧
  W.smul (Ftrip 2) 3 (Etrip 2) =
      (-48 * (tripletTwoC * tripletTwoD)) • omegaTrip 2

/-- The exact normalized identities inhabit the coordinate-facing residual expected by the
pair-closure argument. -/
theorem threeCoordinateIdentitiesWp_of_explicit (hp : 1 ≤ 2)
    (h : ThreeExplicitMixedIdentitiesWp hp) : ThreeCoordinateIdentitiesWp hp := by
  refine ⟨(48 : ℂ) / 5 * tripletTwoC, (4 : ℂ) / 5 * tripletTwoC,
    -64 * (tripletTwoC * tripletTwoD), 12 * (tripletTwoC * tripletTwoD),
    10 * tripletTwoD, -48 * (tripletTwoC * tripletTwoD), ?_⟩
  simpa only [ThreeExplicitMixedIdentitiesWp] using h

end VOA.LatGen.WpC2

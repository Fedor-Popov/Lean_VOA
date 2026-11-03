/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAM
import VOA.Examples.TripletWpTwoAMCoords
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The finite `W(2)` Adamovic--Milas Virasoro-coordinate evaluator

This file builds the evaluator for the Virasoro side of the literal coordinate certificate
isolated in `TripletWpTwoAM`.  The calculation is performed in invariant rank-one Fock
coordinates

`A_i = (alphaP 2)(-i-1)|0>`.

The first layer below supplies the polynomial recursion for negative background-charge Virasoro
modes.  It avoids unfolding the infinite Sugawara sum: its only input is the already-proved
Heisenberg commutator.

It does not evaluate the screened state `Q^2 e^{-2 alpha}` or `H_{(-5)}H`, and it does not prove
the final comparison `AMTwoCoordinateIdentity hp`.
-/

set_option maxHeartbeats 100000

namespace VOA.LatGen.WpTwoAMProof

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private abbrev alphaTwo : Ltwo.carrier := alphaP 2
private noncomputable abbrev ATwo (i : ℕ) : FockN (rank Ltwo) := vVar Ltwo alphaTwo i

/-- Abstract invariant coordinates.  Keeping the family index out of this polynomial ring makes
the remaining finite calculation independent of a choice of orthonormal frame. -/
private abbrev InvFock := MvPolynomial ℕ ℂ

/-- Evaluation of the abstract coordinate `X i` as the invariant current state `A_i`. -/
noncomputable def invEval : InvFock →ₐ[ℂ] FockN (rank Ltwo) :=
  MvPolynomial.aeval ATwo

@[simp] theorem invEval_X (i : ℕ) : invEval (MvPolynomial.X i) = ATwo i := by
  rw [invEval, MvPolynomial.aeval_def, MvPolynomial.eval₂_X]

@[simp] theorem invEval_add (P Q : InvFock) :
    invEval (P + Q) = invEval P + invEval Q := invEval.map_add P Q

@[simp] theorem invEval_mul (P Q : InvFock) :
    invEval (P * Q) = invEval P * invEval Q := invEval.map_mul P Q

@[simp] theorem invEval_smul (c : ℂ) (P : InvFock) :
    invEval (c • P) = c • invEval P := invEval.toLinearMap.map_smul c P

@[simp] theorem invEval_C_smul (c : ℂ) :
    invEval (MvPolynomial.C c) = c • vacuumN (rank Ltwo) := by
  rw [show MvPolynomial.C c = c • (1 : InvFock) by
    rw [MvPolynomial.smul_eq_C_mul, mul_one], invEval_smul]
  simp [vacuumN]

@[simp] theorem invEval_X_mul (i : ℕ) (P : InvFock) :
    invEval (MvPolynomial.X i * P) = ATwo i * invEval P := by
  rw [invEval_mul, invEval_X]

@[simp] theorem invEval_smul_X_mul (c : ℂ) (i : ℕ) (P : InvFock) :
    invEval ((c • MvPolynomial.X i) * P) = (c • ATwo i) * invEval P := by
  rw [invEval_mul, invEval_smul, invEval_X]

/-- The derivation induced by `[L_{-n},A_i]=(i+1)A_{i+n}`. -/
noncomputable def invShift (n : ℕ) : Derivation ℂ InvFock InvFock :=
  MvPolynomial.mkDerivation ℂ fun i => ((i : ℂ) + 1) • MvPolynomial.X (i + n)

@[simp] theorem invShift_X (n i : ℕ) :
    invShift n (MvPolynomial.X i) = ((i : ℂ) + 1) • MvPolynomial.X (i + n) := by
  rw [invShift, MvPolynomial.mkDerivation_X]

/-- The canonical FLM cocycle is identically one in rank one: the strictly lower-triangular
exponent defining it has no entries. -/
theorem latticeCocycle_latP_two (a b : Ltwo.carrier) :
    latticeCocycle Ltwo a b = 1 := by
  rw [latticeCocycle, cocycle]
  have hr : IntegralLattice.latRank Ltwo = 1 := by
    rw [← rank_eq_latRank, rank_latP]
  have hexp : cocExp Ltwo (latticeBasis Ltwo) a b = 0 := by
    rw [cocExp]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hi : i.val = 0 := by
      have := i.isLt
      change i.val < IntegralLattice.latRank Ltwo at this
      rw [hr] at this
      omega
    have hj : j.val = 0 := by
      have := j.isLt
      change j.val < IntegralLattice.latRank Ltwo at this
      rw [hr] at this
      omega
    have hji : ¬ j < i := by
      intro h
      have : j.val < i.val := h
      omega
    simp [hji]
  rw [hexp, zpow_zero]

/-! ## Explicit finite normal-product bounds -/

/-- A normal product of weight-`Da` and weight-`Db` fields, applied to a weight-`w` state, has
an exact finite coefficient range.  The negative half is cut off by positivity after the left
field acts first; the nonnegative half is cut off by positivity after the right field acts first.
-/
theorem nprod_apply_grading_bounded {r : ℕ}
    {F G : FormalDist (End ℂ (FockN r))} (hF : IsField F) (hG : IsField G)
    (Da Db : ℕ) (hgF : GradedFieldN r F (Da : ℤ))
    (hgG : GradedFieldN r G (Db : ℤ)) (s : ℤ) {w : ℕ} {q : FockN r}
    (hq : q ∈ gradingWN r w) :
    nprod hF hG s q =
      ∑ m ∈ Finset.Icc (-((Da + w : ℕ) : ℤ))
          (max (-1) ((Db + w : ℕ) + s)), normalOrdered F G m (s - m) q := by
  rw [nprod_apply]
  let f : ℤ → FockN r := fun m => normalOrdered F G m (s - m) q
  have hqZ : q ∈ gradingZN r (w : ℤ) := mem_gradingZN_of_gradingWN hq
  have hsupp : Function.support f ⊆
      Finset.Icc (-((Da + w : ℕ) : ℤ)) (max (-1) ((Db + w : ℕ) + s)) := by
    intro m hm
    rw [Function.mem_support] at hm
    have hlo : -((Da + w : ℕ) : ℤ) ≤ m := by
      by_contra h
      have hmneg : m < 0 := by omega
      have ha := hgF.mem_gradingZN m (w : ℤ) hqZ
      have hgrade : (Da : ℤ) + (w : ℤ) + m < 0 := by
        omega
      rw [gradingZN_of_neg hgrade, Submodule.mem_bot] at ha
      rw [show f m = normalOrdered F G m (s - m) q from rfl,
        normalOrdered_apply, if_neg (by omega), Module.End.mul_apply, ha, map_zero] at hm
      exact hm rfl
    have hhi : m ≤ max (-1) ((Db + w : ℕ) + s) := by
      by_contra h
      have hmnonneg : 0 ≤ m := by omega
      have hb := hgG.mem_gradingZN (s - m) (w : ℤ) hqZ
      have hgrade : (Db : ℤ) + (w : ℤ) + (s - m) < 0 := by
        omega
      rw [gradingZN_of_neg hgrade, Submodule.mem_bot] at hb
      rw [show f m = normalOrdered F G m (s - m) q from rfl,
        normalOrdered_apply, if_pos hmnonneg, Module.End.mul_apply, hb, map_zero] at hm
      exact hm rfl
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  rw [show (fun m : ℤ => normalOrdered F G m (s - m) q) = f from rfl,
    finsum_eq_sum_of_support_subset f hsupp]

/-- On the neutral sector, the background-charge Virasoro operator is the Sugawara operator
minus the background oscillator. -/
theorem LSecBg_zero_eq (m : ℤ) :
    BgA.LSecBg Ltwo (lamP 2) 0 m =
      LvirN (rank Ltwo) 1 m - ((m : ℂ) + 1) • BgA.bgOsc Ltwo (lamP 2) m := by
  have hcharge : chargeOsc Ltwo (0 : Ltwo.carrier) m = 0 := by
    rw [chargeOsc_eq_sum]
    exact Finset.sum_eq_zero fun a _ => by rw [chargeCoord_zero, zero_smul]
  simp [BgA.LSecBg, BgA.OpSec, BgA.BetaSec, BgA.scWt, BgA.scMom,
    BgA.bgPair, BgA.bgForm, hcharge, chargeCoord_zero]

/-- Negative background modes have the usual Virasoro--Heisenberg commutator on a negative
charge oscillator.  The deformation term contributes no bracket because both modes are negative.
-/
theorem LSecBg_zero_comm_chargeOsc_neg (m n : ℤ) (hm : m < 0) (hn : n < 0) :
    BgA.LSecBg Ltwo (lamP 2) 0 m * chargeOsc Ltwo alphaTwo n
        - chargeOsc Ltwo alphaTwo n * BgA.LSecBg Ltwo (lamP 2) 0 m
      = (-(n : ℂ)) • chargeOsc Ltwo alphaTwo (m + n) := by
  rw [LSecBg_zero_eq]
  have hL := BgA.LvirN_comm_bgOsc Ltwo (chargeCoord Ltwo alphaTwo) m n
  simp only [← BgA.chargeOsc_eq_bgOsc] at hL
  have hB := BgA.bgOsc_comm Ltwo (lamP 2) (chargeCoord Ltwo alphaTwo) m n
  rw [← BgA.chargeOsc_eq_bgOsc] at hB
  rw [if_neg (by omega)] at hB
  simp only [zero_smul] at hB
  calc
    (LvirN (rank Ltwo) 1 m - ((m : ℂ) + 1) • BgA.bgOsc Ltwo (lamP 2) m)
          * chargeOsc Ltwo alphaTwo n
        - chargeOsc Ltwo alphaTwo n
          * (LvirN (rank Ltwo) 1 m - ((m : ℂ) + 1) • BgA.bgOsc Ltwo (lamP 2) m) =
      (LvirN (rank Ltwo) 1 m * chargeOsc Ltwo alphaTwo n
          - chargeOsc Ltwo alphaTwo n * LvirN (rank Ltwo) 1 m)
        - ((m : ℂ) + 1) •
          (BgA.bgOsc Ltwo (lamP 2) m * chargeOsc Ltwo alphaTwo n
            - chargeOsc Ltwo alphaTwo n * BgA.bgOsc Ltwo (lamP 2) m) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
    _ = (-(n : ℂ)) • chargeOsc Ltwo alphaTwo (m + n) := by
      rw [hL, hB, smul_zero, sub_zero]

/-- Polynomial recursion for a negative Virasoro mode.  This is the workhorse which turns every
printed Virasoro word in the AM certificate into a finite polynomial calculation. -/
theorem LSecBg_neg_mul_ATwo (n : ℕ) (hn : 1 ≤ n) (i : ℕ)
    (q : FockN (rank Ltwo)) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (ATwo i * q) =
      ATwo i * BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) q
        + ((i : ℂ) + 1) • (ATwo (i + n) * q) := by
  have hcomm := congrArg (fun T : End ℂ (FockN (rank Ltwo)) => T q)
    (LSecBg_zero_comm_chargeOsc_neg (-(n : ℤ)) (-((i : ℤ) + 1))
      (by omega) (by omega))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hcomm
  simp only [chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply] at hcomm
  have hindex : -((n : ℤ)) + -((i : ℤ) + 1) = -(((i + n : ℕ) : ℤ) + 1) := by
    push_cast
    ring
  rw [hindex] at hcomm
  rw [chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply] at hcomm
  push_cast at hcomm
  rw [show - -((i : ℂ) + 1) = (i : ℂ) + 1 by ring] at hcomm
  linear_combination hcomm

/-- Once the vacuum value of `L_{-n}` is known, its action on every invariant polynomial is the
sum of multiplication by that vacuum value and the shift derivation. -/
theorem LSecBg_neg_invEval_of_vac (n : ℕ) (hn : 1 ≤ n) (V : InvFock)
    (hV : BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (vacuumN (rank Ltwo)) = invEval V)
    (P : InvFock) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (invEval P) =
      invEval (P * V + invShift n P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [invEval_C_smul, map_smul, hV]
      simp
      rw [MvPolynomial.smul_eq_C_mul]
  | add P Q hP hQ =>
      rw [invEval_add,
        (BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ))).map_add, hP, hQ]
      simp only [add_mul, (invShift n).map_add, invEval_add]
      ring
  | mul_X P i hP =>
      have hsource :
          P * MvPolynomial.X i * V + invShift n (P * MvPolynomial.X i) =
            MvPolynomial.X i * (P * V + invShift n P)
              + (((i : ℂ) + 1) • MvPolynomial.X (i + n)) * P := by
        rw [Derivation.leibniz, invShift_X]
        ring
      have heval :
          invEval (MvPolynomial.X i * (P * V + invShift n P)
            + (((i : ℂ) + 1) • MvPolynomial.X (i + n)) * P) =
            ATwo i * (invEval P * invEval V + invEval (invShift n P))
              + (((i : ℂ) + 1) • ATwo (i + n)) * invEval P := by
        rw [invEval_add, invEval_X_mul, invEval_smul_X_mul, invEval_add, invEval_mul]
      rw [invEval_mul, invEval_X, mul_comm, LSecBg_neg_mul_ATwo n hn i, hP]
      rw [hsource, heval]
      rw [invEval_add, invEval_mul]
      simp only [smul_mul_assoc]

private noncomputable abbrev omegaTwoFock : FockN (rank Ltwo) :=
  (1 / 8 : ℂ) • ATwo 0 ^ 2 + (1 / 4 : ℂ) • ATwo 1

private noncomputable def omegaInv : InvFock :=
  (1 / 8 : ℂ) • MvPolynomial.X 0 ^ 2 + (1 / 4 : ℂ) • MvPolynomial.X 1

@[simp] theorem invEval_omegaInv : invEval omegaInv = omegaTwoFock := by
  simp only [omegaInv, omegaTwoFock, map_add, map_smul, map_pow, invEval_X]

theorem LSecBg_neg_one_vacuum :
    BgA.LSecBg Ltwo (lamP 2) 0 (-1) (vacuumN (rank Ltwo)) = 0 := by
  rw [LSecBg_zero_eq]
  norm_num
  exact LvirN_vacuum (rank Ltwo) 1 (by norm_num : (-1 : ℤ) ≤ -1)

/-- Translation of an invariant polynomial is the shift derivation `A_i ↦ (i+1)A_{i+1}`. -/
theorem LSecBg_neg_one_invEval (P : InvFock) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-1) (invEval P) = invEval (invShift 1 P) := by
  have h := LSecBg_neg_invEval_of_vac 1 (by norm_num) 0
    (by simpa using LSecBg_neg_one_vacuum) P
  simpa using h

private noncomputable def invTranslate (k : ℕ) (P : InvFock) : InvFock :=
  ((invShift 1).toLinearMap ^ k) P

theorem LSecBg_neg_one_pow_invEval (k : ℕ) (P : InvFock) :
    (BgA.LSecBg Ltwo (lamP 2) 0 (-1) ^ k) (invEval P) =
      invEval (invTranslate k P) := by
  induction k with
  | zero => simp [invTranslate]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LSecBg_neg_one_invEval]
      simp only [invTranslate, pow_succ', Module.End.mul_apply]
      rfl

/-- Powers of translation preserve the neutral lattice sector and are computed by powers of the
neutral Fock translation operator. -/
theorem T_pow_mkE_zero (hp : 1 ≤ 2) (k : ℕ) (q : FockN (rank Ltwo)) :
    ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ k) (mkEα Ltwo 0 q) =
      mkEα Ltwo 0 ((BgA.LSecBg Ltwo (lamP 2) 0 (-1) ^ k) q) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, VertexOperatorAlgebra.T_eq_Lneg1,
        tripletLatticeVOA_L, BgA.LBg_mkEα Ltwo (latP_posDef 2 hp), pow_succ',
        Module.End.mul_apply]

/-- The negative Virasoro mode on the neutral vacuum is a finite translation descendant of the
explicit conformal polynomial. -/
theorem LSecBg_neg_vacuum (hp : 1 ≤ 2) (n : ℕ) (hn : 2 ≤ n) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (vacuumN (rank Ltwo)) =
      (((n - 2).factorial : ℂ)⁻¹) •
        ((BgA.LSecBg Ltwo (lamP 2) 0 (-1) ^ (n - 2)) omegaTwoFock) := by
  have hcreate := VertexOperatorAlgebra.creation_pow (tripletLatticeVOA 2 hp)
    (omegaTrip 2) (n - 2)
  have hmode : -(↑(n - 2) : ℤ) - 1 = -(n : ℤ) + 1 := by omega
  rw [hmode] at hcreate
  change (tripletLatticeVOA 2 hp).L (-(n : ℤ))
      (latVacuumGen Ltwo) = _ at hcreate
  rw [tripletLatticeVOA_L, latVacuumGen_eq_mkEα,
    BgA.LBg_mkEα Ltwo (latP_posDef 2 hp),
    VOA.LatGen.WpTwoAMCoords.omegaTrip_two_eq_vVar_state] at hcreate
  rw [show latStateGen (latP 2)
      ((1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2
        + (1 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1) 0 =
      mkEα Ltwo 0 omegaTwoFock from rfl, T_pow_mkE_zero] at hcreate
  have hcoord := congrArg (coordEα Ltwo 0) hcreate
  simpa only [mkEα_apply, coordEα_apply, if_pos, map_smul] using hcoord

private noncomputable def invVirVac (n : ℕ) : InvFock :=
  (((n - 2).factorial : ℂ)⁻¹) • invTranslate (n - 2) omegaInv

theorem LSecBg_neg_vacuum_invEval (hp : 1 ≤ 2) (n : ℕ) (hn : 2 ≤ n) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (vacuumN (rank Ltwo)) =
      invEval (invVirVac n) := by
  rw [LSecBg_neg_vacuum hp n hn, invVirVac, map_smul,
    ← LSecBg_neg_one_pow_invEval, invEval_omegaInv]

private noncomputable def invVirMode (n : ℕ) (P : InvFock) : InvFock :=
  P * invVirVac n + invShift n P

theorem LSecBg_neg_invEval (hp : 1 ≤ 2) (n : ℕ) (hn : 2 ≤ n) (P : InvFock) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (invEval P) =
      invEval (invVirMode n P) := by
  exact LSecBg_neg_invEval_of_vac n (by omega) (invVirVac n)
    (LSecBg_neg_vacuum_invEval hp n hn) P

private noncomputable def invVirWord : List ℕ → InvFock
  | [] => 1
  | n :: ns => invVirMode n (invVirWord ns)

/-- Every Virasoro word occurring in the printed certificate evaluates to the corresponding
explicit invariant-coordinate recursion. -/
theorem virWordTwo_eq_invEval (hp : 1 ≤ 2) (ns : List ℕ)
    (hns : ∀ n ∈ ns, 2 ≤ n) :
    virWordTwo hp ns = mkEα Ltwo 0 (invEval (invVirWord ns)) := by
  induction ns with
  | nil =>
      simp [virWordTwo, invVirWord, latVacuumGen_eq_mkEα, vacuumN]
  | cons n ns ih =>
      rw [virWordTwo_cons, ih (fun m hm => hns m (List.mem_cons_of_mem n hm)),
        tripletLatticeVOA_L,
        BgA.LBg_mkEα Ltwo (latP_posDef 2 hp), invVirWord,
        LSecBg_neg_invEval hp n (hns n (List.mem_cons_self))]

end VOA.LatGen.WpTwoAMProof

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMProof.latticeCocycle_latP_two
#print axioms VOA.LatGen.WpTwoAMProof.nprod_apply_grading_bounded
#print axioms VOA.LatGen.WpTwoAMProof.virWordTwo_eq_invEval
end AxiomAudit

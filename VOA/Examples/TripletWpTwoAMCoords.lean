/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoSector

set_option maxHeartbeats 50000

/-!
# Neutral-sector coordinate evaluation for the `W(2)` AM identity

This file is a consumer of `TripletWpTwoSector` and `TripletWpTwoAM`.  Its first task is to make
the neutral lattice sector computational: charge-zero lattice fields restrict to the rank-one
Heisenberg Fock vertex operator.  This is the missing simplification bridge needed to compare the
forty-two weight-ten coordinates.
-/

namespace VOA.LatGen.WpTwoAMCoords

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2

variable {L : IntegralLattice}

/-- A lattice field is the charge-zero tensor lift of a bosonic Fock field. -/
def NeutralFieldLift (F : FormalDist (End ℂ (LatModuleGen L)))
    (f : FormalDist (End ℂ (FockN (rank L)))) : Prop :=
  ∀ (j : ℤ) (q : FockN (rank L)),
    F j (mkEα L 0 q) = mkEα L 0 (f j q)

/-- The lattice current restricts on charge zero to the ordinary Heisenberg current. -/
theorem alphaLatGen_neutralFieldLift (a : Fin (rank L)) :
    NeutralFieldLift (alphaLatGen L a) (currentN (rank L) 1 a) := by
  intro j q
  rw [show mkEα L 0 q = latStateGen L q 0 from rfl, alphaLatGen_tmul]
  rw [chargeCoord_zero]
  split_ifs <;> simp <;> rfl

/-- Every scaled derivative generator restricts on charge zero to its Heisenberg counterpart. -/
theorem genFieldLatGen_neutralFieldLift (a : Fin (rank L)) (i : ℕ) :
    NeutralFieldLift (genFieldLatGen L a i) (genFieldN (rank L) 1 a i) := by
  intro j q
  rw [genFieldLatGen, genFieldN, dcurrentN]
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a)) j)
      (mkEα L 0 q) =
    mkEα L 0 (((i.factorial : ℂ)⁻¹ •
      (VOA.deriv^[i] (currentN (rank L) 1 a)) j) q)
  rw [VertexOperatorAlgebra.deriv_pow_apply, VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ]
  simp only [LinearMap.smul_apply]
  rw [alphaLatGen_neutralFieldLift]
  simp only [map_smul]

/-- Normal ordering commutes with restriction to the neutral lattice sector, term by term. -/
theorem normalOrdered_neutral_apply {F G : FormalDist (End ℂ (LatModuleGen L))}
    {f g : FormalDist (End ℂ (FockN (rank L)))}
    (hF : NeutralFieldLift F f) (hG : NeutralFieldLift G g)
    (m n : ℤ) (q : FockN (rank L)) :
    normalOrdered F G m n (mkEα L 0 q) =
      mkEα L 0 (normalOrdered f g m n q) := by
  simp only [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply, if_pos hm, Module.End.mul_apply,
      hG n q, hF m (g n q)]
  · rw [if_neg hm, Module.End.mul_apply, if_neg hm, Module.End.mul_apply,
      hF m q, hG n (f m q)]

/-- The neutral-lift relation is stable under normal ordering. -/
theorem NeutralFieldLift.nprod {F G : FormalDist (End ℂ (LatModuleGen L))}
    {f g : FormalDist (End ℂ (FockN (rank L)))}
    (hF : NeutralFieldLift F f) (hG : NeutralFieldLift G g)
    (hFfield : IsField F) (hGfield : IsField G)
    (hffield : IsField f) (hgfield : IsField g) :
    NeutralFieldLift (VOA.nprod hFfield hGfield)
      (VOA.nprod hffield hgfield) := by
  intro s q
  rw [nprod_apply, nprod_apply,
    finsum_congr (fun m => normalOrdered_neutral_apply hF hG m (s - m) q),
    ← map_finsum (mkEα L 0) (normalOrdered_diag_support_finite hffield hgfield s q)]

/-- A neutral lattice word field is the tensor lift of the corresponding Heisenberg word field. -/
theorem YwordLatGen_zero_neutralFieldLift :
    ∀ l : List (ℕ × Fin (rank L)),
      NeutralFieldLift (YwordLatGen L l 0) (YwordN (rank L) 1 l)
  | [] => by
      rw [YwordLatGen_nil, YwordN_nil]
      intro j q
      rw [Yeαvec_zero_apply, idFieldN_apply]
      split_ifs <;> simp
  | ia :: rest => by
      rw [YwordLatGen_cons, YwordN_cons]
      exact (genFieldLatGen_neutralFieldLift ia.2 ia.1).nprod
        (YwordLatGen_zero_neutralFieldLift rest)
        (genFieldLatGen_isField L ia.2 ia.1) (YwordLatGen_isField L rest 0)
        (genFieldN_isField (rank L) 1 ia.2 ia.1) (YwordN_isField (rank L) 1 rest)

theorem NeutralFieldLift.add {F G : FormalDist (End ℂ (LatModuleGen L))}
    {f g : FormalDist (End ℂ (FockN (rank L)))}
    (hF : NeutralFieldLift F f) (hG : NeutralFieldLift G g) :
    NeutralFieldLift (F + G) (f + g) := by
  intro j q
  change (F j + G j) (mkEα L 0 q) = mkEα L 0 ((f j + g j) q)
  rw [LinearMap.add_apply, LinearMap.add_apply, hF, hG, map_add]

theorem NeutralFieldLift.smul (c : ℂ) {F : FormalDist (End ℂ (LatModuleGen L))}
    {f : FormalDist (End ℂ (FockN (rank L)))} (hF : NeutralFieldLift F f) :
    NeutralFieldLift (c • F) (c • f) := by
  intro j q
  change (c • F j) (mkEα L 0 q) = mkEα L 0 ((c • f j) q)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hF, map_smul]

theorem NeutralFieldLift.zero : NeutralFieldLift (L := L) 0 0 := by
  intro j q
  change (0 : LatModuleGen L) = mkEα L 0 (0 : FockN (rank L))
  rw [map_zero]

theorem NeutralFieldLift.finsetSum {S : Type*} (s : Finset S)
    {F : S → FormalDist (End ℂ (LatModuleGen L))}
    {f : S → FormalDist (End ℂ (FockN (rank L)))}
    (h : ∀ a ∈ s, NeutralFieldLift (F a) (f a)) :
    NeutralFieldLift (∑ a ∈ s, F a) (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (NeutralFieldLift.zero (L := L))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- Monomial neutral states have the Heisenberg monomial vertex operator. -/
theorem YfullGen_monomial_neutralFieldLift (hEven : L.Even) (hPos : L.PosDef)
    (a : (ℕ × Fin (rank L)) →₀ ℕ) (c : ℂ) :
    NeutralFieldLift
      (YfullGen L hEven hPos (mkEα L 0 (MvPolynomial.monomial a c)))
      (YN (rank L) 1 (MvPolynomial.monomial a c)) := by
  have hstate : mkEα L 0 (MvPolynomial.monomial a c) =
      c • wordStateLatGen L (monoWordN a) 0 := by
    rw [wordStateLatGen_eq, wordStateN_monoWordN, mkEα_apply,
      show MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : ℂ) from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      TensorProduct.smul_tmul']
  rw [hstate, map_smul, YN_monomial, YfullGen_word, YmonN]
  exact (YwordLatGen_zero_neutralFieldLift (L := L) (monoWordN a)).smul c

/-- The reconstructed lattice vertex operator of any neutral Fock state restricts to the
ordinary Heisenberg vertex operator on the neutral sector. -/
theorem YfullGen_neutralFieldLift (hEven : L.Even) (hPos : L.PosDef)
    (p : FockN (rank L)) :
    NeutralFieldLift (YfullGen L hEven hPos (mkEα L 0 p)) (YN (rank L) 1 p) := by
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [map_sum]
  exact NeutralFieldLift.finsetSum p.support
    (fun a _ => YfullGen_monomial_neutralFieldLift hEven hPos a (MvPolynomial.coeff a p))

/-! ## Explicit rank-one conformal coordinates -/

theorem chargeOsc_neg_vacuum_eq_vVar (L : IntegralLattice) (beta : L.carrier) (m : ℕ) :
    chargeOsc L beta (-((m : ℤ) + 1)) (vacuumN (rank L)) = vVar L beta m := by
  rw [chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply, vacuumN, mul_one]

theorem vVar_neg (L : IntegralLattice) (alpha : L.carrier) (m : ℕ) :
    vVar L (-alpha) m = -vVar L alpha m := by
  have hcoord : ∀ a : Fin (rank L), chargeCoord L (-alpha) a = -chargeCoord L alpha a := by
    intro a
    have h := chargeCoord_add L alpha (-alpha) a
    rw [add_neg_cancel, chargeCoord_zero] at h
    linear_combination -h
  rw [vVar, vVar, Finset.sum_congr rfl (fun a _ => by rw [hcoord a, neg_smul]),
    Finset.sum_neg_distrib]

theorem bgOsc_latBg_apply (L : IntegralLattice) (c : ℂ) (alpha : L.carrier)
    (m : ℤ) (q : FockN (rank L)) :
    BgA.bgOsc L (BgA.latBg L c alpha) m q = c • chargeOsc L alpha m q := by
  rw [BgA.bgOsc_apply, chargeOsc, LinearMap.coe_sum, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    simp only [BgA.latBg, LinearMap.smul_apply, smul_smul]
    congr 1

theorem LvirN_neg_two_vacuum_eq_omegaN (r : ℕ) :
    LvirN r 1 (-2) (vacuumN r) = ωN r 1 := by
  rw [LvirN_eq_mode_YN_omega]
  norm_num
  exact mode_YN_creation_neg_one r 1 (ωN r 1)

/-- In rank one the Sugawara quadratic is the square of the lattice-direction current divided
by the norm `4` and by the Sugawara factor `2`. -/
theorem omegaN_latP_two_eq_vVar_sq :
    ωN (rank (latP 2)) 1 =
      (1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2 := by
  have hc := sum_chargeCoord (latP 2) (latP_posDef 2 (by norm_num))
    (alphaP 2) (alphaP 2)
  letI : Unique (Fin (rank (latP 2))) :=
    { default := ⟨0, by rw [rank_latP]; norm_num⟩
      uniq := fun a => Fin.ext (by
        have ha : a.val < 1 := by
          rw [← rank_latP 2]
          exact a.isLt
        change a.val = 0
        omega) }
  rw [Fintype.sum_unique, latP_form_alpha] at hc
  norm_num at hc
  have hc' : chargeCoord (latP 2) (alphaP 2) default ^ 2 = 4 := by
    simpa [pow_two] using hc
  rw [ωN, Fintype.sum_unique, vVar, Fintype.sum_unique, ωNa,
    oscN_apply_neg (rank (latP 2)) 1 default (by norm_num : (-1 : ℤ) < 0),
    oscN_apply_neg (rank (latP 2)) 1 default (by norm_num : (-1 : ℤ) < 0), vacuumN]
  norm_num
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [mul_pow, ← map_pow, hc']
  norm_num
  have hC : (MvPolynomial.C (1 / 2 : ℂ) : FockN (rank (latP 2))) =
      MvPolynomial.C (1 / 8 : ℂ) * MvPolynomial.C (4 : ℂ) := by
    rw [← map_mul]
    norm_num
  rw [hC]
  ring

/-- The `p = 2` background-charge conformal vector in invariant rank-one coordinates.  Writing
it using `vVar alpha` avoids any choice of sign for the orthonormal frame coordinate. -/
theorem omegaTrip_two_eq_vVar :
    omegaTrip 2 = mkEα (latP 2) 0
      ((1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2
        + (1 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1) := by
  rw [omegaTrip, BgA.omegaBg, omegaLatGen, ← map_add]
  congr 1
  rw [omegaN_latP_two_eq_vVar_sq, lamP, bgOsc_latBg_apply,
    show (-2 : ℤ) = -(((1 : ℕ) : ℤ) + 1) by norm_num,
    chargeOsc_neg_vacuum_eq_vVar, cP]
  norm_num

theorem omegaTrip_two_eq_vVar_state :
    omegaTrip 2 = latStateGen (latP 2)
      ((1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2
        + (1 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1) 0 :=
  omegaTrip_two_eq_vVar

/-- The charged primary `F=e^{-alpha}` after one `L_{-2}` action, in the same invariant
rank-one coordinates used by the mixed-pair certificates. -/
theorem LSecBg_neg_two_F_fock :
    BgA.LSecBg (latP 2) (lamP 2) (-alphaP 2) (-2)
        (vacuumN (rank (latP 2))) =
      (1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2
        - (3 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1 := by
  rw [BgA.LSecBg, LinearMap.sub_apply, LinearMap.smul_apply,
    BgA.OpSec_apply, BgA.BetaSec_apply]
  norm_num [BgA.scMom]
  rw [LvirN_neg_two_vacuum_eq_omegaN, omegaN_latP_two_eq_vVar_sq,
    show (-2 : ℤ) = -(((1 : ℕ) : ℤ) + 1) by norm_num,
    chargeOsc_neg_vacuum_eq_vVar, vVar_neg, lamP, bgOsc_latBg_apply,
    chargeOsc_neg_vacuum_eq_vVar, cP]
  norm_num
  module

theorem LminusTwo_Ftrip_two_eq_vVar (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).L (-2) (Ftrip 2) =
      latStateGen (latP 2)
        ((1 / 8 : ℂ) • vVar (latP 2) (alphaP 2) 0 ^ 2
          - (3 / 4 : ℂ) • vVar (latP 2) (alphaP 2) 1)
        (-alphaP 2) := by
  rw [tripletLatticeVOA_L, Ftrip, Screen.Fscr, latChargeGen]
  change BgA.LBg (latP 2) (lamP 2) (-2)
      (mkEα (latP 2) (-alphaP 2) (vacuumN (rank (latP 2)))) = _
  rw [
    BgA.LBg_mkEα (latP 2) (latP_posDef 2 hp), LSecBg_neg_two_F_fock]
  rfl

theorem LvirN_neg_one_vVar_zero (L : IntegralLattice) (beta : L.carrier) :
    LvirN (rank L) 1 (-1) (vVar L beta 0) = vVar L beta 1 := by
  have h := congrArg (fun T : End ℂ (FockN (rank L)) => T (vacuumN (rank L)))
    (LvirN_comm_chargeOsc L beta (-1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [LvirN_vacuum (rank L) 1 (by norm_num : (-1 : ℤ) ≤ -1), map_zero, sub_zero] at h
  norm_num at h
  rw [show chargeOsc L beta (-1) (vacuumN (rank L)) = vVar L beta 0 from
      chargeOsc_neg_vacuum_eq_vVar L beta 0,
    show chargeOsc L beta (-2) (vacuumN (rank L)) = vVar L beta 1 from
      chargeOsc_neg_vacuum_eq_vVar L beta 1] at h
  exact h

theorem LSecBg_neg_one_F_vacuum :
    BgA.LSecBg (latP 2) (lamP 2) (-alphaP 2) (-1)
        (vacuumN (rank (latP 2))) = -vVar (latP 2) (alphaP 2) 0 := by
  rw [BgA.LSecBg, LinearMap.sub_apply, LinearMap.smul_apply,
    BgA.OpSec_apply, BgA.BetaSec_apply]
  norm_num [BgA.scMom]
  rw [LvirN_vacuum (rank (latP 2)) 1 (by norm_num : (-1 : ℤ) ≤ -1),
    show (-1 : ℤ) = -(((0 : ℕ) : ℤ) + 1) by norm_num,
    chargeOsc_neg_vacuum_eq_vVar, vVar_neg]
  module

theorem LSecBg_neg_one_F_once :
    BgA.LSecBg (latP 2) (lamP 2) (-alphaP 2) (-1)
        (-vVar (latP 2) (alphaP 2) 0) =
      vVar (latP 2) (alphaP 2) 0 ^ 2 - vVar (latP 2) (alphaP 2) 1 := by
  rw [BgA.LSecBg, LinearMap.sub_apply, LinearMap.smul_apply,
    BgA.OpSec_apply, BgA.BetaSec_apply]
  norm_num [BgA.scMom]
  rw [LvirN_neg_one_vVar_zero, show (-1 : ℤ) = -(((0 : ℕ) : ℤ) + 1) by
      norm_num, chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply, vVar_neg]
  ring

theorem T_sq_Ftrip_two_eq_vVar (hp : 1 ≤ 2) :
    ((tripletLatticeVOA 2 hp).toPreVertexAlgebra.T ^ 2) (Ftrip 2) =
      latStateGen (latP 2)
        (vVar (latP 2) (alphaP 2) 0 ^ 2 - vVar (latP 2) (alphaP 2) 1)
        (-alphaP 2) := by
  rw [VertexOperatorAlgebra.T_eq_Lneg1, pow_two, Module.End.mul_apply,
    tripletLatticeVOA_L, Ftrip, Screen.Fscr, latChargeGen]
  change BgA.LBg (latP 2) (lamP 2) (-1)
      (BgA.LBg (latP 2) (lamP 2) (-1)
        (mkEα (latP 2) (-alphaP 2) (vacuumN (rank (latP 2))))) = _
  rw [
    BgA.LBg_mkEα (latP 2) (latP_posDef 2 hp), LSecBg_neg_one_F_vacuum,
    BgA.LBg_mkEα (latP 2) (latP_posDef 2 hp), LSecBg_neg_one_F_once]
  rfl

end VOA.LatGen.WpTwoAMCoords

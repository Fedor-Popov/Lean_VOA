/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpSimplicity
import VOA.Examples.TripletWpTwoZhuSparseCompute
import VOA.Examples.TripletWpTwoZhuSparseSemantics
import VOA.Core.BorcherdsIdentity
import VOA.Core.JacobiLocal

/-!
# The finite Zhu certificate for lattice W(2)

This file is the intrinsic assembly layer for the exact sparse coordinate certificate.  Its
37 circle terms are literal depth-zero Frenkel--Zhu residues, and the remaining screened state
belongs to Zhu's `O` by the independent higher-pole argument in `TripletWpZhuScreening`.
-/

namespace VOA.LatGen.WpTwoZhuCertificate

open scoped BigOperators
open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.IntegralLattice
open VOA.LatGen.Wp VOA.LatGen.WpC2
open VOA.SparseRational HeisenbergN
open VOA.LatGen.WpTwoAMCoords
open VOA.LatGen.WpTwoAMClose
open VOA.LatGen.WpTwoAMSparseBridge
open VOA.LatGen.WpTwoVirasoroCoords
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseSemantics

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private noncomputable abbrev W0 : VertexOperatorAlgebra (FockN (rank Ltwo)) :=
  heisenbergNVOA (rank Ltwo) 1 one_ne_zero

private theorem evalAWord_eq_vVar_prod :
    ∀ w : List ℕ, evalAWord w =
      (w.map fun i => vVar Ltwo (alphaP 2) i).prod
  | [] => by simp [evalAWord, vacuumN]
  | i :: is => by
      rw [evalAWord, evalAWord_eq_vVar_prod is]
      rfl

private theorem cbz_two_one : cbz (2 : ℤ) 1 = 2 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num),
    show ((1 : ℤ)).toNat = 1 from rfl, gBinom]
  norm_num [Finset.prod_range_one]

private theorem cbz_two_two : cbz (2 : ℤ) 2 = 1 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num),
    show ((2 : ℤ)).toNat = 2 from rfl, gBinom]
  norm_num [Finset.prod_range_succ, Finset.prod_range_one]

private theorem sum_range_three {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ Finset.range 3, f m = f 0 + f 1 + f 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

private theorem zhuMul_conformal_three_modes {V : Type*} [AddCommGroup V]
    [Module ℂ V] (W : VertexOperatorAlgebra V) (v : V) :
    zhuMul W W.conformalVector v =
      W.smul W.conformalVector (-1) v +
        (2 : ℂ) • W.smul W.conformalVector 0 v +
          W.smul W.conformalVector 1 v := by
  rw [zhuMul_homogeneous' W W.conformal_mem]
  rw [show ((2 : ℤ).toNat + 1) = 3 from rfl, sum_range_three]
  have e0 : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  have e2 : ((2 : ℕ) : ℤ) - 1 = 1 := by norm_num
  have b0 : cbz (2 : ℤ) ((0 : ℕ) : ℤ) = 1 := by
    rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) by norm_num]
    exact cbz_zero 2
  have b1 : cbz (2 : ℤ) ((1 : ℕ) : ℤ) = 2 := by
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) by norm_num]
    exact cbz_two_one
  have b2 : cbz (2 : ℤ) ((2 : ℕ) : ℤ) = 1 := by
    rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
    exact cbz_two_two
  rw [e0, e1, e2, b0, b1, b2, one_smul, one_smul]

/-! ## Mixed-weight semantics of the iterated Zhu powers -/

theorem evalZhuSparseQ_omegaSparseQ :
    evalZhuSparseQ omegaSparseQ =
      (1 / 8 : ℂ) • vVar Ltwo (alphaP 2) 0 ^ 2 +
        (1 / 4 : ℂ) • vVar Ltwo (alphaP 2) 1 := by
  rw [evalZhuSparseQ, omegaSparseQ, evalSparse_normalizeQ]
  simp only [evalRaw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, evalWord_ATwo', algebraMap_rat_mul_fock]
  rw [evalAWord_eq_vVar_prod, evalAWord_eq_vVar_prod]
  simp [pow_two]

theorem conformalVector_coe_eq_eval_omegaSparseQ (hp : 1 ≤ 2) :
    (((tripletWVOA 2 hp).conformalVector : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ omegaSparseQ) 0 := by
  rw [tripletWVOA_conformalVector_coe, omegaTrip_two_eq_vVar_state,
    evalZhuSparseQ_omegaSparseQ]

theorem evalZhuSparseQ_omegaSparseQ_mem_grading :
    evalZhuSparseQ omegaSparseQ ∈ gradingWN (rank Ltwo) 2 := by
  rw [evalZhuSparseQ_omegaSparseQ]
  have h00 : vVar Ltwo (alphaP 2) 0 ^ 2 ∈ gradingWN Ltwo.rank 2 := by
    simpa [evalAWord, aWordWeight, pow_two, vacuumN] using
      (evalAWord_mem_grading [0, 0])
  have h1 : vVar Ltwo (alphaP 2) 1 ∈ gradingWN Ltwo.rank 2 := by
    simpa [evalAWord, aWordWeight, vacuumN] using
      (evalAWord_mem_grading [1])
  exact (gradingWN Ltwo.rank 2).add_mem
    ((gradingWN Ltwo.rank 2).smul_mem _ h00)
    ((gradingWN Ltwo.rank 2).smul_mem _ h1)

/-! ## Trusted normal-product semantics for the `L(-2)^2 1` ledger entries -/

private theorem omega_mem_W0 :
    evalZhuSparseQ omegaSparseQ ∈ W0.grading 2 := by
  exact mem_gradingZN_of_gradingWN evalZhuSparseQ_omegaSparseQ_mem_grading

private theorem eval_virModeSparseQ (m : ℤ) (h : ℕ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h) :
    evalZhuSparseQ (virModeSparseQ m h Q) =
      W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1) (evalZhuSparseQ Q) := by
  rw [virModeSparseQ, eval_voaModeActSparseQ omegaSparseQ (m + 1) h Q hQ]
  rfl

private theorem W0_smul_omega_eq_LSecBg (hp : 1 ≤ 2) (m : ℤ)
    (Q : FockN (rank Ltwo)) :
    W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1) Q =
      BgA.LSecBg Ltwo (lamP 2) 0 m Q := by
  have hL := DFunLike.congr_fun (tripletLatticeVOA_L 2 hp m)
    (latStateGen Ltwo Q 0)
  change (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (m + 1)
      (latStateGen Ltwo Q 0) =
    BgA.LBg Ltwo (lamP 2) m (latStateGen Ltwo Q 0) at hL
  rw [omegaTrip_two_eq_vVar_state, ← evalZhuSparseQ_omegaSparseQ,
    tripletLatticeVOA_smul_neutral,
    show BgA.LBg Ltwo (lamP 2) m (latStateGen Ltwo Q 0) =
      latStateGen Ltwo (BgA.LSecBg Ltwo (lamP 2) 0 m Q) 0 by
        exact BgA.LBg_mkEα Ltwo (latP_posDef 2 hp) (lamP 2) m Q 0] at hL
  have hc := congrArg (coordEα Ltwo 0) hL
  change mode (YN (rank Ltwo) 1 (evalZhuSparseQ omegaSparseQ)) (m + 1) Q = _
  simpa only [latStateGen, coordEα_apply, if_pos rfl] using hc

private theorem eval_reifyVir22_eq_normal (hp : 1 ≤ 2) :
    evalZhuSparseQ (reifyVirWordSparseQ [2, 2]) =
      W0.smul (evalZhuSparseQ omegaSparseQ) (-1)
        (evalZhuSparseQ omegaSparseQ) := by
  rw [evalZhuSparseQ_reifyVirWordSparseQ [2, 2] (by norm_num)]
  simp only [virWordFockTwo]
  change BgA.LSecBg Ltwo (lamP 2) 0 (-2)
      (BgA.LSecBg Ltwo (lamP 2) 0 (-2) (vacuumN (rank Ltwo))) = _
  rw [← W0_smul_omega_eq_LSecBg hp (-2),
    ← W0_smul_omega_eq_LSecBg hp (-2)]
  norm_num
  change W0.smul (evalZhuSparseQ omegaSparseQ) (-1)
      (W0.smul (evalZhuSparseQ omegaSparseQ) (-1) W0.vacuum) = _
  rw [PreVertexAlgebra.smul_vacuum_neg_one]

private theorem eval_virModeSparseQ_mem_grading (m : ℤ) (h : ℕ)
    (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h)
    (hm : m ≤ h) :
    evalZhuSparseQ (virModeSparseQ m h Q) ∈
      gradingWN (rank Ltwo) ((h : ℤ) - m).toNat := by
  rw [eval_virModeSparseQ m h Q hQ]
  have ht := W0.smul_mem_grading omega_mem_W0
    (mem_gradingZN_of_gradingWN hQ) (m + 1)
  have hnonneg : 0 ≤ (h : ℤ) - m := by omega
  rw [show (2 : ℤ) + h - (m + 1) - 1 = (h : ℤ) - m by ring] at ht
  change W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1)
      (evalZhuSparseQ Q) ∈ gradingZN (rank Ltwo) ((h : ℤ) - m) at ht
  rw [gradingZN_of_nonneg hnonneg] at ht
  exact ht

private theorem eval_nested_virModeSparseQ (a b : ℤ) (h : ℕ)
    (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h)
    (hb : b ≤ h) :
    evalZhuSparseQ
        (virModeSparseQ a (((h : ℤ) - b).toNat) (virModeSparseQ b h Q)) =
      W0.smul (evalZhuSparseQ omegaSparseQ) (a + 1)
        (W0.smul (evalZhuSparseQ omegaSparseQ) (b + 1)
          (evalZhuSparseQ Q)) := by
  rw [eval_virModeSparseQ a _ _
      (eval_virModeSparseQ_mem_grading b h Q hQ hb),
    eval_virModeSparseQ b h Q hQ]

private theorem evalZhuSparseQ_sum_intIcc (lo hi : ℤ)
    (f : ℤ → SparseRational.Poly ℕ) :
    evalZhuSparseQ (sumQ
      ((WpTwoAMSparseCompute.intIccListQ lo hi).map f)) =
      ∑ m ∈ Finset.Icc lo hi, evalZhuSparseQ (f m) := by
  rw [evalZhuSparseQ_sumQ, List.map_map, intIccListQ_eq_intIccList]
  have h := List.sum_toFinset (fun m => evalZhuSparseQ (f m))
    (intIccList_nodup lo hi)
  rw [intIccList_toFinset] at h
  exact h.symm

private theorem evalZhuSparseQ_sum_range (R : ℕ)
    (f : ℕ → SparseRational.Poly ℕ) :
    evalZhuSparseQ (sumQ ((List.range R).map f)) =
      ∑ i ∈ Finset.range R, evalZhuSparseQ (f i) := by
  rw [evalZhuSparseQ_sumQ, List.map_map]
  have h := List.sum_toFinset (fun i => evalZhuSparseQ (f i))
    (List.nodup_range : (List.range R).Nodup)
  rw [List.toFinset_range] at h
  exact h.symm

private theorem eval_vir22ModeSparseQ_formula (n : ℤ) (h : ℕ)
    (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h) :
    evalZhuSparseQ (vir22ModeSparseQ n h Q) =
      (∑ m ∈ Finset.Icc (n - 3 - (h : ℤ)) (-2),
        W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1)
          (W0.smul (evalZhuSparseQ omegaSparseQ) (n - 2 - m)
            (evalZhuSparseQ Q))) +
      (∑ m ∈ Finset.Icc (-1) (h : ℤ),
        W0.smul (evalZhuSparseQ omegaSparseQ) (n - 2 - m)
          (W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1)
            (evalZhuSparseQ Q))) := by
  rw [vir22ModeSparseQ, evalZhuSparseQ_addQ,
    evalZhuSparseQ_sum_intIcc, evalZhuSparseQ_sum_intIcc]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [eval_nested_virModeSparseQ m (n - 3 - m) h Q hQ (by omega)]
    ring_nf
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [eval_nested_virModeSparseQ (n - 3 - m) m h Q hQ (by omega)]
    ring_nf

private theorem iterate22_eq_sum9 (h : ℕ) (n : ℤ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h)
    (hh : h ≤ 5) (hnlo : -2 ≤ n) (hnhi : n ≤ 2) :
    W0.smul (W0.smul (evalZhuSparseQ omegaSparseQ) (-1)
        (evalZhuSparseQ omegaSparseQ)) n (evalZhuSparseQ Q) =
      ∑ i ∈ Finset.range 9,
        (W0.smul (evalZhuSparseQ omegaSparseQ) (-1 - (i : ℤ))
            (W0.smul (evalZhuSparseQ omegaSparseQ) (n + i)
              (evalZhuSparseQ Q)) +
          W0.smul (evalZhuSparseQ omegaSparseQ) (-1 + n - i)
            (W0.smul (evalZhuSparseQ omegaSparseQ) i (evalZhuSparseQ Q))) := by
  have hx : evalZhuSparseQ Q ∈ W0.grading (h : ℤ) :=
    mem_gradingZN_of_gradingWN hQ
  have hiterate := VertexOperatorAlgebra.mode_iterate_neg W0
    (evalZhuSparseQ omegaSparseQ) (evalZhuSparseQ omegaSparseQ) 0 n
    (evalZhuSparseQ Q)
  norm_num at hiterate
  rw [hiterate]
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range 9) (by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hirange
    have hirange' : 9 ≤ i := by
      simpa only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_range, not_lt] using hirange
    have hz1 : W0.smul (evalZhuSparseQ omegaSparseQ) (n + i)
        (evalZhuSparseQ Q) = 0 := by
      exact Deform.smul_eq_zero_of_grading_lt W0
        omega_mem_W0 hx (by omega)
    have hz2 : W0.smul (evalZhuSparseQ omegaSparseQ) (i : ℤ)
        (evalZhuSparseQ Q) = 0 := by
      exact Deform.smul_eq_zero_of_grading_lt W0
        omega_mem_W0 hx (by omega)
    apply hi
    rw [hz1, hz2]
    simp)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Int.reduceNeg, gBinom_neg_one]
  rw [show ((-1 : ℂ) ^ i * (-1 : ℂ) ^ i) = 1 by
    rw [← mul_pow]
    norm_num]
  norm_num

private theorem icc_neg10_neg2 :
    Finset.Icc (-10 : ℤ) (-2) = {-10, -9, -8, -7, -6, -5, -4, -3, -2} := by
  decide
private theorem icc_neg9_neg2 :
    Finset.Icc (-9 : ℤ) (-2) = {-9, -8, -7, -6, -5, -4, -3, -2} := by
  decide
private theorem icc_neg8_neg2 :
    Finset.Icc (-8 : ℤ) (-2) = {-8, -7, -6, -5, -4, -3, -2} := by
  decide
private theorem icc_neg7_neg2 :
    Finset.Icc (-7 : ℤ) (-2) = {-7, -6, -5, -4, -3, -2} := by
  decide
private theorem icc_neg6_neg2 :
    Finset.Icc (-6 : ℤ) (-2) = {-6, -5, -4, -3, -2} := by
  decide
private theorem icc_neg5_neg2 :
    Finset.Icc (-5 : ℤ) (-2) = {-5, -4, -3, -2} := by
  decide
private theorem icc_neg4_neg2 :
    Finset.Icc (-4 : ℤ) (-2) = {-4, -3, -2} := by
  decide
private theorem icc_neg1_3 :
    Finset.Icc (-1 : ℤ) 3 = {-1, 0, 1, 2, 3} := by
  decide
private theorem icc_neg1_5 :
    Finset.Icc (-1 : ℤ) 5 = {-1, 0, 1, 2, 3, 4, 5} := by
  decide

private theorem eval_vir22ModeSparseQ_eq_normal (hp : 1 ≤ 2)
    (h : ℕ) (n : ℤ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h)
    (hh : h = 3 ∨ h = 5) (hnlo : -2 ≤ n) (hnhi : n ≤ 2) :
    evalZhuSparseQ (vir22ModeSparseQ n h Q) =
      mode (YN (rank Ltwo) 1
        (evalZhuSparseQ (reifyVirWordSparseQ [2, 2]))) n
        (evalZhuSparseQ Q) := by
  rw [eval_reifyVir22_eq_normal hp]
  change evalZhuSparseQ (vir22ModeSparseQ n h Q) =
    W0.smul (W0.smul (evalZhuSparseQ omegaSparseQ) (-1)
      (evalZhuSparseQ omegaSparseQ)) n (evalZhuSparseQ Q)
  rw [eval_vir22ModeSparseQ_formula n h Q hQ,
    iterate22_eq_sum9 h n Q hQ (by omega) hnlo hnhi]
  rcases hh with rfl | rfl
  · have hx : evalZhuSparseQ Q ∈ W0.grading (3 : ℤ) :=
      mem_gradingZN_of_gradingWN hQ
    have hz5 : W0.smul (evalZhuSparseQ omegaSparseQ) 5
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz6 : W0.smul (evalZhuSparseQ omegaSparseQ) 6
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz7 : W0.smul (evalZhuSparseQ omegaSparseQ) 7
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz8 : W0.smul (evalZhuSparseQ omegaSparseQ) 8
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz9 : W0.smul (evalZhuSparseQ omegaSparseQ) 9
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz10 : W0.smul (evalZhuSparseQ omegaSparseQ) 10
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    interval_cases n
    all_goals norm_num
    all_goals first
      | rw [icc_neg8_neg2, icc_neg1_3]
      | rw [icc_neg7_neg2, icc_neg1_3]
      | rw [icc_neg6_neg2, icc_neg1_3]
      | rw [icc_neg5_neg2, icc_neg1_3]
      | rw [icc_neg4_neg2, icc_neg1_3]
    all_goals simp [Finset.sum_range_succ, hz5, hz6, hz7, hz8, hz9, hz10]
    all_goals module
  · have hx : evalZhuSparseQ Q ∈ W0.grading (5 : ℤ) :=
      mem_gradingZN_of_gradingWN hQ
    have hz7 : W0.smul (evalZhuSparseQ omegaSparseQ) 7
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz8 : W0.smul (evalZhuSparseQ omegaSparseQ) 8
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz9 : W0.smul (evalZhuSparseQ omegaSparseQ) 9
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    have hz10 : W0.smul (evalZhuSparseQ omegaSparseQ) 10
        (evalZhuSparseQ Q) = 0 :=
      Deform.smul_eq_zero_of_grading_lt W0 omega_mem_W0 hx (by norm_num)
    interval_cases n
    all_goals norm_num
    all_goals first
      | rw [icc_neg10_neg2, icc_neg1_5]
      | rw [icc_neg9_neg2, icc_neg1_5]
      | rw [icc_neg8_neg2, icc_neg1_5]
      | rw [icc_neg7_neg2, icc_neg1_5]
      | rw [icc_neg6_neg2, icc_neg1_5]
    all_goals simp [Finset.sum_range_succ, hz7, hz8, hz9, hz10]
    all_goals module

private theorem eval_vir22CircleSparseQ_eq_circle (hp : 1 ≤ 2)
    (h : ℕ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h)
    (hh : h = 3 ∨ h = 5) :
    evalZhuSparseQ (vir22CircleSparseQ h Q) =
      evalZhuSparseQ
        (circleSparseQ 4 (reifyVirWordSparseQ [2, 2]) h Q) := by
  rw [vir22CircleSparseQ, evalZhuSparseQ_sum_range]
  rw [eval_circleSparseQ 4 (reifyVirWordSparseQ [2, 2]) h Q hQ]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evalZhuSparseQ_scaleQ]
  congr 1
  exact eval_vir22ModeSparseQ_eq_normal hp h ((i : ℤ) - 2) Q hQ hh
    (by rw [Finset.mem_range] at hi; omega)
    (by rw [Finset.mem_range] at hi; omega)

theorem certificateL22_eval_bridge (hp : 1 ≤ 2) :
    evalZhuSparseQ (evalCircleLedger certificateL22Ledger) =
      evalZhuSparseQ (evalVir22Ledger certificateL22Ledger) := by
  simp only [evalCircleLedger, evalVir22Ledger, certificateL22Ledger,
    ZhuCircleDesc.eval, evalZhuSparseQ_sumQ, evalZhuSparseQ_scaleQ,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  norm_num [ZhuStateDesc.weight]
  rw [eval_vir22CircleSparseQ_eq_circle hp 3
      ((.vir [3] : ZhuStateDesc).eval)
      ((.vir [3] : ZhuStateDesc).eval_mem_gradingWN hp (by
        simp [ZhuStateDesc.Valid])) (Or.inl rfl),
    eval_vir22CircleSparseQ_eq_circle hp 5
      ((.vir [3, 2] : ZhuStateDesc).eval)
      ((.vir [3, 2] : ZhuStateDesc).eval_mem_gradingWN hp (by
        simp [ZhuStateDesc.Valid])) (Or.inr rfl)]
  rfl

/-! ## Trusted translation semantics for the single Virasoro-vacuum ledgers -/

private theorem eval_reifyVirSingle_eq_creation (hp : 1 ≤ 2) (r : ℕ)
    (hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) :
    evalZhuSparseQ (reifyVirWordSparseQ [r]) =
      (((r - 2).factorial : ℂ)⁻¹) •
        ((W0.toPreVertexAlgebra.T ^ (r - 2)) (evalZhuSparseQ omegaSparseQ)) := by
  rw [evalZhuSparseQ_reifyVirWordSparseQ [r] (by
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num)]
  simp only [virWordFockTwo]
  change BgA.LSecBg Ltwo (lamP 2) 0 (-(r : ℤ)) W0.vacuum = _
  rw [← W0_smul_omega_eq_LSecBg hp (-(r : ℤ))]
  have hc := VertexOperatorAlgebra.creation_pow W0
    (evalZhuSparseQ omegaSparseQ) (r - 2)
  convert hc using 1 <;>
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num

private theorem eval_virVacModeSparseQ (hp : 1 ≤ 2) (r : ℕ) (n : ℤ)
    (h : ℕ) (Q : SparseRational.Poly ℕ)
    (hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h) :
    evalZhuSparseQ (virVacModeSparseQ r n h Q) =
      W0.smul (evalZhuSparseQ (reifyVirWordSparseQ [r])) n
        (evalZhuSparseQ Q) := by
  rw [virVacModeSparseQ, evalZhuSparseQ_scaleQ,
    eval_voaModeActSparseQ omegaSparseQ (n - (r - 2 : ℕ)) h Q hQ]
  change ((virVacModeCoefficientQ r n : ℚ) : ℂ) •
      W0.smul (evalZhuSparseQ omegaSparseQ) (n - (r - 2 : ℕ))
        (evalZhuSparseQ Q) = _
  rw [eval_reifyVirSingle_eq_creation hp r hr,
    PreVertexAlgebra.smul_smul_left,
    VertexOperatorAlgebra.smul_Tpow,
    ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [virVacModeCoefficientQ, Nat.reduceSub, Nat.factorial,
      Nat.cast_ofNat, Finset.prod_range_succ, Finset.prod_range_zero] <;>
    push_cast <;> ring

private theorem eval_virVacCircleSparseQ_eq_circle (hp : 1 ≤ 2) (r h : ℕ)
    (Q : SparseRational.Poly ℕ)
    (hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) h) :
    evalZhuSparseQ (virVacCircleSparseQ r h Q) =
      evalZhuSparseQ (circleSparseQ r (reifyVirWordSparseQ [r]) h Q) := by
  rw [virVacCircleSparseQ, evalZhuSparseQ_sum_range,
    eval_circleSparseQ r (reifyVirWordSparseQ [r]) h Q hQ]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evalZhuSparseQ_scaleQ,
    eval_virVacModeSparseQ hp r ((i : ℤ) - 2) h Q hr hQ]
  rfl

private def VirVacValid (d : ZhuCircleDesc) : Prop :=
  ∃ r, d.left = .vir [r] ∧
    (r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) ∧ d.right.Valid

private theorem evalVirVacLedger_eq_evalCircleLedger (hp : 1 ≤ 2)
    (ledger : List ZhuCircleDesc)
    (hvalid : ∀ d ∈ ledger, VirVacValid d) :
    evalZhuSparseQ (evalVirVacLedger ledger) =
      evalZhuSparseQ (evalCircleLedger ledger) := by
  induction ledger with
  | nil =>
      simp [evalVirVacLedger, evalCircleLedger, evalZhuSparseQ_sumQ]
  | cons d ledger ih =>
      rcases hvalid d (by simp) with ⟨r, hleft, hr, hright⟩
      have htail : ∀ e ∈ ledger, VirVacValid e := by
        intro e he
        exact hvalid e (by simp [he])
      have hgrade := d.right.eval_mem_gradingWN hp hright
      simp only [evalVirVacLedger, evalCircleLedger, List.map_cons,
        evalZhuSparseQ_sumQ, List.sum_cons]
      apply congrArg₂ (fun x y => x + y)
      · simp only [ZhuCircleDesc.eval]
        rw [hleft]
        simp only [ZhuStateDesc.weight, ZhuStateDesc.eval]
        change evalZhuSparseQ
            (scaleQ d.coefficient
              (virVacCircleSparseQ r d.right.weight d.right.eval)) =
          evalZhuSparseQ
            (scaleQ d.coefficient
              (circleSparseQ r (reifyVirWordSparseQ [r])
                d.right.weight d.right.eval))
        rw [evalZhuSparseQ_scaleQ, evalZhuSparseQ_scaleQ,
          eval_virVacCircleSparseQ_eq_circle hp r d.right.weight d.right.eval hr hgrade]
      · simpa only [evalVirVacLedger, evalCircleLedger,
          evalZhuSparseQ_sumQ] using ih htail

theorem certificateL2_eval_bridge (hp : 1 ≤ 2) :
    evalZhuSparseQ (evalCircleLedger certificateL2Ledger) =
      evalZhuSparseQ (evalVirVacLedger certificateL2Ledger) := by
  symm
  apply evalVirVacLedger_eq_evalCircleLedger hp
  simp [certificateL2Ledger, VirVacValid, ZhuStateDesc.Valid]

theorem certificateL3_eval_bridge (hp : 1 ≤ 2) :
    evalZhuSparseQ (evalCircleLedger certificateL3Ledger) =
      evalZhuSparseQ (evalVirVacLedger certificateL3Ledger) := by
  symm
  apply evalVirVacLedger_eq_evalCircleLedger hp
  simp [certificateL3Ledger, VirVacValid, ZhuStateDesc.Valid]

theorem certificateL4_eval_bridge (hp : 1 ≤ 2) :
    evalZhuSparseQ (evalCircleLedger certificateL4Ledger) =
      evalZhuSparseQ (evalVirVacLedger certificateL4Ledger) := by
  symm
  apply evalVirVacLedger_eq_evalCircleLedger hp
  simp [certificateL4Ledger, VirVacValid, ZhuStateDesc.Valid]

theorem certificateL5_eval_bridge (hp : 1 ≤ 2) :
    evalZhuSparseQ (evalCircleLedger certificateL5Ledger) =
      evalZhuSparseQ (evalVirVacLedger certificateL5Ledger) := by
  symm
  apply evalVirVacLedger_eq_evalCircleLedger hp
  simp [certificateL5Ledger, VirVacValid, ZhuStateDesc.Valid]

private noncomputable def zhuOmegaPartIntrinsic (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier) :
    List (ℕ × (tripletW 2 hp).carrier) :=
  [(x.1 + 2, (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector (-1) x.2),
   (x.1 + 1, (2 : ℂ) •
      (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector 0 x.2),
   (x.1, (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector 1 x.2)]

private noncomputable def zhuOmegaPartsIntrinsic (hp : 1 ≤ 2) :
    ℕ → List (ℕ × (tripletW 2 hp).carrier)
  | 0 => [(0, (tripletWVOA 2 hp).vacuum)]
  | n + 1 => (zhuOmegaPartsIntrinsic hp n).flatMap (zhuOmegaPartIntrinsic hp)

private noncomputable def flattenGradedIntrinsic (hp : 1 ≤ 2)
    (xs : List (ℕ × (tripletW 2 hp).carrier)) : (tripletW 2 hp).carrier :=
  (xs.map Prod.snd).sum

private theorem flatten_zhuOmegaPartIntrinsic (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier) :
    flattenGradedIntrinsic hp (zhuOmegaPartIntrinsic hp x) =
      zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector x.2 := by
  rw [zhuMul_conformal_three_modes]
  simp [flattenGradedIntrinsic, zhuOmegaPartIntrinsic]
  module

private theorem flatten_flatMap_zhuOmegaPartIntrinsic (hp : 1 ≤ 2) :
    ∀ xs : List (ℕ × (tripletW 2 hp).carrier),
      flattenGradedIntrinsic hp (xs.flatMap (zhuOmegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
          (flattenGradedIntrinsic hp xs)
  | [] => by simp [flattenGradedIntrinsic]
  | x :: xs => by
      rw [List.flatMap_cons]
      change flattenGradedIntrinsic hp
          (zhuOmegaPartIntrinsic hp x ++
            xs.flatMap (zhuOmegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
          (x.2 + flattenGradedIntrinsic hp xs)
      rw [zhuMul_add_right]
      rw [show flattenGradedIntrinsic hp
          (zhuOmegaPartIntrinsic hp x ++ xs.flatMap (zhuOmegaPartIntrinsic hp)) =
            flattenGradedIntrinsic hp (zhuOmegaPartIntrinsic hp x) +
              flattenGradedIntrinsic hp (xs.flatMap (zhuOmegaPartIntrinsic hp)) by
        simp [flattenGradedIntrinsic]]
      change flattenGradedIntrinsic hp (zhuOmegaPartIntrinsic hp x) +
          flattenGradedIntrinsic hp (xs.flatMap (zhuOmegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector x.2 +
          zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
            (flattenGradedIntrinsic hp xs)
      rw [flatten_zhuOmegaPartIntrinsic, flatten_flatMap_zhuOmegaPartIntrinsic]

private theorem flatten_zhuOmegaPartsIntrinsic_eq (hp : 1 ≤ 2) : ∀ n : ℕ,
    flattenGradedIntrinsic hp (zhuOmegaPartsIntrinsic hp n) =
      zhuOmegaPow (tripletWVOA 2 hp) n
  | 0 => by simp [flattenGradedIntrinsic, zhuOmegaPartsIntrinsic, zhuOmegaPow]
  | n + 1 => by
      rw [zhuOmegaPartsIntrinsic, flatten_flatMap_zhuOmegaPartIntrinsic,
        flatten_zhuOmegaPartsIntrinsic_eq, zhuOmegaPow]

private def OmegaPartRel (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier)
    (P : ℕ × SparseRational.Poly ℕ) : Prop :=
  x.1 = P.1 ∧
    x.2 ∈ (tripletWVOA 2 hp).grading (x.1 : ℤ) ∧
    ((x.2 : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ P.2) 0 ∧
    evalZhuSparseQ P.2 ∈ gradingWN (rank Ltwo) P.1

private theorem eval_voaMode_omega_mem_grading (n : ℤ) (rightWeight target : ℕ)
    (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight)
    (hindex : (2 : ℤ) + rightWeight - n - 1 = target) :
    evalZhuSparseQ (voaModeActSparseQ omegaSparseQ n rightWeight Q) ∈
      gradingWN (rank Ltwo) target := by
  rw [eval_voaModeActSparseQ omegaSparseQ n rightWeight Q hQ]
  change (YN (rank Ltwo) 1 (evalZhuSparseQ omegaSparseQ)) (-n - 1)
      (evalZhuSparseQ Q) ∈ gradingWN (rank Ltwo) target
  have h := YN_gradedField_of_mem (rank Ltwo) 1
    evalZhuSparseQ_omegaSparseQ_mem_grading (-n - 1) rightWeight
      (evalZhuSparseQ Q) hQ
  have hindex' : (2 : ℤ) + rightWeight + (-n - 1) = target := by
    omega
  have ht :
      (YN Ltwo.rank 1 (evalZhuSparseQ omegaSparseQ)) (-n - 1)
          (evalZhuSparseQ Q) ∈ gradingZN Ltwo.rank (target : ℤ) := by
    rw [← hindex']
    exact h
  rw [gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at ht
  exact ht

private theorem coe_omega_mode_eq_eval (hp : 1 ≤ 2) (n : ℤ)
    (rightWeight : ℕ) (Q : SparseRational.Poly ℕ)
    (x : (tripletW 2 hp).carrier)
    (hx : (x : LatModuleGen Ltwo) = latStateGen Ltwo (evalZhuSparseQ Q) 0)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight) :
    (((tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector n x :
        (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo
        (evalZhuSparseQ (voaModeActSparseQ omegaSparseQ n rightWeight Q)) 0 := by
  rw [smul_coe, conformalVector_coe_eq_eval_omegaSparseQ hp, hx,
    tripletLatticeVOA_smul_neutral,
    eval_voaModeActSparseQ omegaSparseQ n rightWeight Q hQ]

private theorem zhuOmegaPart_rel (hp : 1 ≤ 2)
    {x : ℕ × (tripletW 2 hp).carrier}
    {P : ℕ × SparseRational.Poly ℕ} (h : OmegaPartRel hp x P) :
    List.Forall₂ (OmegaPartRel hp) (zhuOmegaPartIntrinsic hp x)
      (zhuOmegaPartSparseQ P) := by
  rcases x with ⟨w, x⟩
  rcases P with ⟨wP, P⟩
  rcases h with ⟨hweight, hxgrade, hx, hPgrade⟩
  simp only at hweight
  subst wP
  have hneg1grade := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade (-1)
  have hzerograde := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade 0
  have honegrade := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade 1
  have hneg1fock := eval_voaMode_omega_mem_grading (-1) w (w + 2) P hPgrade (by
    push_cast
    ring)
  have hzerofock := eval_voaMode_omega_mem_grading 0 w (w + 1) P hPgrade (by
    push_cast
    ring)
  have honefock := eval_voaMode_omega_mem_grading 1 w w P hPgrade (by
    push_cast
    ring)
  simp only [zhuOmegaPartIntrinsic, zhuOmegaPartSparseQ]
  constructor
  · refine ⟨rfl, ?_, coe_omega_mode_eq_eval hp (-1) w P x hx hPgrade, hneg1fock⟩
    convert hneg1grade using 1 <;> simp <;> push_cast <;> ring
  constructor
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · exact (tripletWVOA 2 hp).grading (↑(w + 1)) |>.smul_mem _ (by
        convert hzerograde using 1 <;> simp <;> push_cast <;> ring)
    · simp only [Submodule.coe_smul]
      rw [coe_omega_mode_eq_eval hp 0 w P x hx hPgrade,
        evalZhuSparseQ_scaleQ, latStateGen_smul_boson]
      norm_num
    · rw [evalZhuSparseQ_scaleQ]
      exact (gradingWN (rank Ltwo) (w + 1)).smul_mem _ hzerofock
  constructor
  · refine ⟨rfl, ?_, coe_omega_mode_eq_eval hp 1 w P x hx hPgrade, honefock⟩
    convert honegrade using 1 <;> simp <;> push_cast <;> ring
  exact List.Forall₂.nil

private theorem zhuOmegaParts_rel (hp : 1 ≤ 2) : ∀ n : ℕ,
    List.Forall₂ (OmegaPartRel hp) (zhuOmegaPartsIntrinsic hp n)
      (zhuOmegaPartsSparseQ n)
  | 0 => by
      simp only [zhuOmegaPartsIntrinsic, zhuOmegaPartsSparseQ]
      constructor
      · refine ⟨rfl, (tripletWVOA 2 hp).vacuum_mem, ?_, ?_⟩
        · rw [tripletWVOA_vacuum_coe, evalZhuSparseQ_vacuumSparseQ]
          rfl
        · rw [evalZhuSparseQ_vacuumSparseQ]
          exact vacuumN_mem_gradingWN (rank Ltwo)
      exact List.Forall₂.nil
  | n + 1 => by
      rw [zhuOmegaPartsIntrinsic, zhuOmegaPartsSparseQ]
      exact List.rel_flatMap (zhuOmegaParts_rel hp n)
        (fun _ _ h => zhuOmegaPart_rel hp h)

private theorem flatten_rel_coe (hp : 1 ≤ 2)
    {xs : List (ℕ × (tripletW 2 hp).carrier)}
    {Ps : List (ℕ × SparseRational.Poly ℕ)}
    (h : List.Forall₂ (OmegaPartRel hp) xs Ps) :
    ((flattenGradedIntrinsic hp xs : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ (flattenGradedSparseQ Ps)) 0 := by
  induction h with
  | nil =>
      change (0 : LatModuleGen Ltwo) =
        latStateGen Ltwo (evalZhuSparseQ (sumQ [])) 0
      rw [evalZhuSparseQ_sumQ]
      simp [latStateGen]
  | @cons x P xs Ps hrel hrest ih =>
      rcases hrel with ⟨_, _, hx, _⟩
      change (x.2 : LatModuleGen Ltwo) +
          (flattenGradedIntrinsic hp xs : LatModuleGen Ltwo) =
        latStateGen Ltwo
          (evalZhuSparseQ (sumQ (P.2 :: Ps.map Prod.snd))) 0
      rw [evalZhuSparseQ_sumQ]
      simp only [List.map_cons, List.sum_cons, List.map_map,
        Function.comp_apply]
      rw [← List.map_map]
      rw [← evalZhuSparseQ_sumQ (Ps.map Prod.snd)]
      rw [hx, ih, latStateGen_add_boson]
      simp [flattenGradedSparseQ]

theorem zhuOmegaPow_coe_eq_eval_sparse (hp : 1 ≤ 2) (n : ℕ) :
    ((zhuOmegaPow (tripletWVOA 2 hp) n : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo
        (evalZhuSparseQ (flattenGradedSparseQ (zhuOmegaPartsSparseQ n))) 0 := by
  rw [← flatten_zhuOmegaPartsIntrinsic_eq hp n]
  exact flatten_rel_coe hp (zhuOmegaParts_rel hp n)

theorem fTwoZhuRepresentative_coe_eq_eval_sparse (hp : 1 ≤ 2) :
    ((fTwoZhuRepresentative (tripletWVOA 2 hp) : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ fTwoSparseQ) 0 := by
  simp only [fTwoZhuRepresentative, fTwoSparseQ, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_smul, evalZhuSparseQ_sumQ,
    evalZhuSparseQ_scaleQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [zhuOmegaPow_coe_eq_eval_sparse hp 5,
    zhuOmegaPow_coe_eq_eval_sparse hp 4,
    zhuOmegaPow_coe_eq_eval_sparse hp 3,
    zhuOmegaPow_coe_eq_eval_sparse hp 2]
  repeat' rw [latStateGen_add_boson]
  repeat' rw [latStateGen_smul_boson]
  norm_num
  rw [sub_eq_add_neg, ← neg_smul]
  abel

/-! ## The 37 circle residues -/

noncomputable def circleIntrinsic (hp : 1 ≤ 2) (d : ZhuCircleDesc) :
    (tripletW 2 hp).carrier :=
  (d.coefficient : ℂ) •
    Pres (tripletWVOA 2 hp) d.left.weight (d.left.intrinsic hp)
      (d.right.intrinsic hp) 0

theorem circleIntrinsic_mem_O (hp : 1 ≤ 2) (d : ZhuCircleDesc) :
    circleIntrinsic hp d ∈ O (tripletWVOA 2 hp) := by
  exact (O (tripletWVOA 2 hp)).smul_mem _
    (Pres_mem_O (tripletWVOA 2 hp) (d.left.intrinsic_mem_grading hp)
      (d.right.intrinsic hp) 0)

private def CircleValid (d : ZhuCircleDesc) : Prop :=
  d.left.Valid ∧ d.right.Valid

private theorem circleIntrinsic_coe_eq_eval (hp : 1 ≤ 2)
    (d : ZhuCircleDesc) (hd : CircleValid d) :
    ((circleIntrinsic hp d : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ d.eval) 0 := by
  have hpres := coe_Pres_eq_eval_zhuCircleSparseQ hp
    d.left.weight d.right.weight d.left.eval d.right.eval
    (d.left.intrinsic hp) (d.right.intrinsic hp)
    (d.left.intrinsic_coe_eq_eval hp hd.1)
    (d.right.intrinsic_coe_eq_eval hp hd.2)
    (d.right.eval_mem_gradingWN hp hd.2)
  simp only [circleIntrinsic, ZhuCircleDesc.eval, Submodule.coe_smul]
  rw [hpres, evalZhuSparseQ_scaleQ, latStateGen_smul_boson]

private theorem certificateL2Ledger_valid :
    ∀ d ∈ certificateL2Ledger, CircleValid d := by
  simp [certificateL2Ledger, CircleValid, ZhuStateDesc.Valid]

private theorem certificateL3Ledger_valid :
    ∀ d ∈ certificateL3Ledger, CircleValid d := by
  simp [certificateL3Ledger, CircleValid, ZhuStateDesc.Valid]

private theorem certificateL4Ledger_valid :
    ∀ d ∈ certificateL4Ledger, CircleValid d := by
  simp [certificateL4Ledger, CircleValid, ZhuStateDesc.Valid]

private theorem certificateL22Ledger_valid :
    ∀ d ∈ certificateL22Ledger, CircleValid d := by
  simp [certificateL22Ledger, CircleValid, ZhuStateDesc.Valid]

private theorem certificateL5Ledger_valid :
    ∀ d ∈ certificateL5Ledger, CircleValid d := by
  simp [certificateL5Ledger, CircleValid, ZhuStateDesc.Valid]

private theorem certificateHLedger_valid :
    ∀ d ∈ certificateHLedger, CircleValid d := by
  simp [certificateHLedger, CircleValid, ZhuStateDesc.Valid]

noncomputable def intrinsicCircleLedger (hp : 1 ≤ 2)
    (ledger : List ZhuCircleDesc) : (tripletW 2 hp).carrier :=
  (ledger.map (circleIntrinsic hp)).sum

theorem intrinsicCircleLedger_mem_O (hp : 1 ≤ 2) (ledger : List ZhuCircleDesc) :
    intrinsicCircleLedger hp ledger ∈ O (tripletWVOA 2 hp) := by
  induction ledger with
  | nil => exact (O (tripletWVOA 2 hp)).zero_mem
  | cons d ledger ih =>
      simpa [intrinsicCircleLedger] using
        (O (tripletWVOA 2 hp)).add_mem (circleIntrinsic_mem_O hp d) ih

private theorem intrinsicCircleLedger_coe_eq_eval (hp : 1 ≤ 2)
    (ledger : List ZhuCircleDesc) (hvalid : ∀ d ∈ ledger, CircleValid d) :
    ((intrinsicCircleLedger hp ledger : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ (evalCircleLedger ledger)) 0 := by
  induction ledger with
  | nil =>
      simp [intrinsicCircleLedger, evalCircleLedger, evalZhuSparseQ_sumQ,
        latStateGen]
  | cons d ledger ih =>
      have hd : CircleValid d := hvalid d (by simp)
      have htail : ∀ e ∈ ledger, CircleValid e := by
        intro e he
        exact hvalid e (by simp [he])
      change (circleIntrinsic hp d : LatModuleGen Ltwo) +
          (intrinsicCircleLedger hp ledger : LatModuleGen Ltwo) =
        latStateGen Ltwo
          (evalZhuSparseQ (sumQ (d.eval :: ledger.map ZhuCircleDesc.eval))) 0
      rw [evalZhuSparseQ_sumQ]
      simp only [List.map_cons, List.sum_cons]
      rw [← evalZhuSparseQ_sumQ (ledger.map ZhuCircleDesc.eval)]
      have htailEq :
          ((intrinsicCircleLedger hp ledger : (tripletW 2 hp).carrier) :
              LatModuleGen Ltwo) =
            latStateGen Ltwo
              (evalZhuSparseQ (sumQ (ledger.map ZhuCircleDesc.eval))) 0 := by
        simpa [evalCircleLedger] using ih htail
      rw [circleIntrinsic_coe_eq_eval hp d hd, htailEq,
        latStateGen_add_boson]

/-! ## The whole intrinsic right-hand side -/

noncomputable def intrinsicCertificateRhs (hp : 1 ≤ 2) :
    (tripletW 2 hp).carrier :=
  ([(1575 / 1024 : ℂ) • qwpSqNegTwoAlphaTriplet 2 hp,
    intrinsicCircleLedger hp certificateL2Ledger,
    intrinsicCircleLedger hp certificateL3Ledger,
    intrinsicCircleLedger hp certificateL4Ledger,
    intrinsicCircleLedger hp certificateL22Ledger,
    intrinsicCircleLedger hp certificateL5Ledger,
    intrinsicCircleLedger hp certificateHLedger]).sum

theorem intrinsicCertificateRhs_mem_O (hp : 1 ≤ 2) :
    intrinsicCertificateRhs hp ∈ O (tripletWVOA 2 hp) := by
  simp only [intrinsicCertificateRhs, List.sum_cons, List.sum_nil, add_zero]
  exact (O (tripletWVOA 2 hp)).add_mem
    ((O (tripletWVOA 2 hp)).smul_mem _ (Qwp_sq_latChargeGen_mem_O 2 hp))
    ((O (tripletWVOA 2 hp)).add_mem
      (intrinsicCircleLedger_mem_O hp certificateL2Ledger)
      ((O (tripletWVOA 2 hp)).add_mem
        (intrinsicCircleLedger_mem_O hp certificateL3Ledger)
        ((O (tripletWVOA 2 hp)).add_mem
          (intrinsicCircleLedger_mem_O hp certificateL4Ledger)
          ((O (tripletWVOA 2 hp)).add_mem
            (intrinsicCircleLedger_mem_O hp certificateL22Ledger)
            ((O (tripletWVOA 2 hp)).add_mem
              (intrinsicCircleLedger_mem_O hp certificateL5Ledger)
              (intrinsicCircleLedger_mem_O hp certificateHLedger))))))

theorem intrinsicCertificateRhs_coe_eq_eval_sparse (hp : 1 ≤ 2) :
    ((intrinsicCertificateRhs hp : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ certificateRhsSparseQ) 0 := by
  have hq :
      (((1575 / 1024 : ℂ) • qwpSqNegTwoAlphaTriplet 2 hp :
          (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
        latStateGen Ltwo (evalZhuSparseQ certificateQPartSparseQ) 0 := by
    simp only [Submodule.coe_smul, certificateQPartSparseQ]
    rw [qwpSqNegTwoAlphaTriplet_coe_eq_eval_qTwoSparseQ hp,
      evalZhuSparseQ_scaleQ, latStateGen_smul_boson]
    norm_num
  have hL2 := intrinsicCircleLedger_coe_eq_eval hp certificateL2Ledger
    certificateL2Ledger_valid
  rw [certificateL2_eval_bridge hp] at hL2
  have hL3 := intrinsicCircleLedger_coe_eq_eval hp certificateL3Ledger
    certificateL3Ledger_valid
  rw [certificateL3_eval_bridge hp] at hL3
  have hL4 := intrinsicCircleLedger_coe_eq_eval hp certificateL4Ledger
    certificateL4Ledger_valid
  rw [certificateL4_eval_bridge hp] at hL4
  have hL22 := intrinsicCircleLedger_coe_eq_eval hp certificateL22Ledger
    certificateL22Ledger_valid
  rw [certificateL22_eval_bridge hp] at hL22
  have hL5 := intrinsicCircleLedger_coe_eq_eval hp certificateL5Ledger
    certificateL5Ledger_valid
  rw [certificateL5_eval_bridge hp] at hL5
  have hH := intrinsicCircleLedger_coe_eq_eval hp certificateHLedger
    certificateHLedger_valid
  simp only [intrinsicCertificateRhs, certificateRhsSparseQ, List.sum_cons,
    List.sum_nil, add_zero, Submodule.coe_add, evalZhuSparseQ_sumQ,
    List.map_cons, List.map_nil]
  rw [hq, hL2, hL3, hL4, hL22, hL5, hH]
  repeat' rw [latStateGen_add_boson]

theorem fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_sparse
    (hp : 1 ≤ 2)
    (hrhs : ((intrinsicCertificateRhs hp : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ certificateRhsSparseQ) 0)
    (hcoord : fTwoSparseQ = certificateRhsSparseQ) :
    fTwoZhuRepresentative (tripletWVOA 2 hp) = intrinsicCertificateRhs hp := by
  apply Subtype.ext
  rw [fTwoZhuRepresentative_coe_eq_eval_sparse hp, hrhs, hcoord]

end VOA.LatGen.WpTwoZhuCertificate

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuCertificate.zhuOmegaPow_coe_eq_eval_sparse
#print axioms VOA.LatGen.WpTwoZhuCertificate.fTwoZhuRepresentative_coe_eq_eval_sparse
#print axioms VOA.LatGen.WpTwoZhuCertificate.circleIntrinsic_mem_O
#print axioms VOA.LatGen.WpTwoZhuCertificate.intrinsicCertificateRhs_mem_O
end AxiomAudit

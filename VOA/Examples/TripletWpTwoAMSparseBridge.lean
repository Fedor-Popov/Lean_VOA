/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMSparseCollect
import VOA.Examples.TripletWpTwoAMExpectedSparse

/-!
# Semantic bridge for the sparse `W(2)` normal-product certificate

The executable current recurrence and the handwritten 32-term target live in independent
files.  This file first compares their canonical sparse outputs and then transports the checked
rational polynomial identity to the complex Fock-space evaluator.
-/

namespace VOA.LatGen.WpTwoAMSparseBridge

open VOA VOA.IntegralLattice HeisenbergN
open VOA.SparseRational
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2 VOA.LatGen.WpTwoVirasoroCoords
open VOA.LatGen.WpTwoAMClose
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoAMExpectedSparse

/-- Public rank-one lattice used by the executable sparse semantics. -/
noncomputable abbrev sparseLatticeTwo : IntegralLattice := latP 2

/-- Public distinguished lattice direction at `p=2`. -/
abbrev sparseAlphaTwo : sparseLatticeTwo.carrier := alphaP 2

/-- Public evaluator variables for invariant-coordinate sparse polynomials.  This was originally
private, which prevented downstream certificate semantics from reusing the proved evaluator. -/
noncomputable abbrev sparseATwo (i : ℕ) : FockN (rank sparseLatticeTwo) :=
  vVar sparseLatticeTwo sparseAlphaTwo i

local notation "Ltwo" => sparseLatticeTwo
local notation "alphaTwo" => sparseAlphaTwo
local notation "ATwo'" => sparseATwo

/-- Independent source and target computations agree as canonical sparse polynomials. -/
theorem hProductSparseQ_eq_expected :
    hProductSparseQ = hProductExpectedSparse := by
  rw [hProductSparseQ, hPartZeroZeroZeroSparseQ_eq,
    hPartZeroOneSparseQ_eq, hPartTwoSparseQ_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hPartZeroZeroZeroExpectedQ, hPartZeroOneExpectedQ, hPartTwoExpectedQ,
    hProductExpectedSparse, hProductExpectedRawQ, addQ, normalizeQ, insertQ,
    sortWord, insertVar, insertSorted, compareWord]

theorem evalWord_ATwo' (w : List ℕ) :
    evalWord ATwo' w = evalAWord w := by
  rw [evalAWord_eq_map_prod]
  simp [evalWord, vacuumN]

theorem algebraMap_rat_mul_fock (q : ℚ) (x : FockN (rank Ltwo)) :
    algebraMap ℚ (FockN (rank Ltwo)) q * x = (q : ℂ) • x := by
  rw [IsScalarTower.algebraMap_apply ℚ ℂ (FockN (rank Ltwo)) q,
    MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_smul_one,
    smul_mul_assoc, one_mul]
  rfl

noncomputable def complexifyRawQ (P : RawPoly ℕ) : APolyTwo :=
  P.map fun t => ((t.1 : ℂ), t.2)

theorem evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ (P : RawPoly ℕ) :
    evalRaw ATwo' P = evalAPoly (complexifyRawQ P) := by
  induction P with
  | nil => simp [evalRaw, complexifyRawQ, evalAPoly]
  | cons t P ih =>
      rcases t with ⟨q, w⟩
      change algebraMap ℚ (FockN (rank Ltwo)) q * evalWord ATwo' w +
          evalRaw ATwo' P =
        evalAPoly (((q : ℂ), w) :: complexifyRawQ P)
      rw [evalWord_ATwo', ih]
      simp only [evalAPoly, List.map_cons, List.sum_cons]
      rw [algebraMap_rat_mul_fock]

theorem complexifyRawQ_append (P Q : RawPoly ℕ) :
    complexifyRawQ (P ++ Q) = complexifyRawQ P ++ complexifyRawQ Q := by
  simp [complexifyRawQ, List.map_append]

theorem complexifyRawQ_prependRawQ (i : ℕ) (P : RawPoly ℕ) :
    complexifyRawQ (prependRawQ i P) = prependA i (complexifyRawQ P) := by
  simp [complexifyRawQ, prependRawQ, prependA, List.map_map,
    Function.comp_def]

theorem complexifyRawQ_scaleRawQ (q : ℚ) (P : RawPoly ℕ) :
    complexifyRawQ (scaleRawQ q P) =
      scaleAPoly (q : ℂ) (complexifyRawQ P) := by
  simp [complexifyRawQ, scaleRawQ, scaleAPoly, List.map_map,
    Function.comp_def]

theorem complexifyRawQ_annihilateRawQ (n : ℕ) : ∀ w : List ℕ,
    complexifyRawQ (annihilateRawQ n w) = annihilateAWord n w
  | [] => by simp [annihilateRawQ, annihilateAWord, complexifyRawQ]
  | i :: is => by
      rw [annihilateRawQ, annihilateAWord]
      rw [complexifyRawQ_append]
      rw [complexifyRawQ_prependRawQ, complexifyRawQ_annihilateRawQ n is]
      by_cases hni : n = i + 1
      · simp [hni, complexifyRawQ]
      · simp [hni, complexifyRawQ]

theorem aFieldCoeffQ_cast (i : ℕ) (s : ℤ) :
    (aFieldCoeffQ i s : ℂ) = aFieldCoeff i s := by
  simp only [aFieldCoeffQ, aFieldCoeff]
  push_cast
  rfl

theorem evalSparse_aFieldActMonomialQ (i : ℕ) (s : ℤ) (w : List ℕ) :
    evalSparse ATwo' (aFieldActMonomialQ i s w) =
      AFieldTwo i s (evalWord ATwo' w) := by
  rw [evalWord_ATwo', ← eval_aFieldActWord]
  rw [aFieldActMonomialQ, aFieldActWord]
  rw [show aFieldMode i s = aFieldModeQ i s by rfl]
  by_cases hneg : aFieldModeQ i s < 0
  · rw [if_pos hneg, if_pos hneg, evalSparse_normalizeQ,
      evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ]
    congr 1
    simp [complexifyRawQ, scaleAPoly, prependA, aFieldCoeffQ_cast, aFieldModeQ]
  · rw [if_neg hneg, if_neg hneg]
    by_cases hzero : aFieldModeQ i s = 0
    · rw [if_pos hzero, if_pos hzero]
      rfl
    · rw [if_neg hzero, if_neg hzero, evalSparse_normalizeQ,
        evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ,
        complexifyRawQ_scaleRawQ, complexifyRawQ_annihilateRawQ,
        aFieldCoeffQ_cast]

theorem evalSparse_aFieldActSparseQ (i : ℕ) (s : ℤ) :
    ∀ P : SparseRational.Poly ℕ,
      evalSparse ATwo' (aFieldActSparseQ i s P) =
        AFieldTwo i s (evalSparse ATwo' P)
  | [] => by simp [aFieldActSparseQ, bindQ, sumQ, evalSparse]
  | (w, q) :: P => by
      have ih := evalSparse_aFieldActSparseQ i s P
      rw [aFieldActSparseQ, evalSparse_bindQ] at ih
      rw [aFieldActSparseQ, evalSparse_bindQ]
      simp only [List.map_cons, List.sum_cons]
      rw [evalSparse_scaleQ, evalSparse_aFieldActMonomialQ, ih]
      change algebraMap ℚ (FockN (rank Ltwo)) q * AFieldTwo i s (evalWord ATwo' w) +
          AFieldTwo i s (evalSparse ATwo' P) =
        AFieldTwo i s
          (algebraMap ℚ (FockN (rank Ltwo)) q * evalWord ATwo' w +
            evalSparse ATwo' P)
      rw [algebraMap_rat_mul_fock, algebraMap_rat_mul_fock, map_add, map_smul]

theorem natRangeQ_eq_range : ∀ n : ℕ, natRangeQ n = List.range n
  | 0 => rfl
  | n + 1 => by rw [natRangeQ, natRangeQ_eq_range n, List.range_succ]

theorem intIccListQ_eq_intIccList (lo hi : ℤ) :
    intIccListQ lo hi = intIccList lo hi := by
  rw [intIccListQ, intIccList, natRangeQ_eq_range]
  by_cases h : lo ≤ hi
  · rw [if_pos h]
    rw [bind_pure_comp]
    change List.map (fun n : ℤ => lo + n)
        (List.map (fun n : ℕ => (n : ℤ)) (List.range (hi - lo + 1).toNat)) = _
    rw [List.map_map]
    rfl
  · rw [if_neg h]
    have hz : (hi - lo + 1).toNat = 0 := by omega
    rw [hz]
    rfl

theorem evalSparse_sumSparseIcc (lo hi : ℤ)
    (f : ℤ → SparseRational.Poly ℕ) :
    evalSparse ATwo' (sumSparseIcc lo hi f) =
      ∑ m ∈ Finset.Icc lo hi, evalSparse ATwo' (f m) := by
  rw [sumSparseIcc, evalSparse_sumQ, List.map_map,
    intIccListQ_eq_intIccList]
  have h := List.sum_toFinset (fun m => evalSparse ATwo' (f m))
    (intIccList_nodup lo hi)
  rw [intIccList_toFinset] at h
  exact h.symm

theorem aWordWeightQ_eq_aWordWeight : ∀ is : List ℕ,
    aWordWeightQ is = aWordWeight is
  | [] => rfl
  | i :: is => by
      rw [aWordWeightQ, aWordWeight, aWordWeightQ_eq_aWordWeight is]

theorem evalSparse_aWordActSparseQ :
    ∀ (is : List ℕ) (s : ℤ) (w : ℕ) (P : SparseRational.Poly ℕ),
      evalSparse ATwo' P ∈ gradingWN (rank Ltwo) w →
        evalSparse ATwo' (aWordActSparseQ is s w P) =
          AWordField is s (evalSparse ATwo' P)
  | [], s, w, P, hP => by
      rw [aWordActSparseQ, AWordField_nil, idFieldN_apply]
      by_cases hs : s = 0
      · rw [if_pos hs, if_pos hs, LinearMap.id_apply]
      · rw [if_neg hs, if_neg hs]
        simp [evalSparse]
  | i :: is, s, w, P, hP => by
      rw [aWordActSparseQ, evalSparse_sumSparseIcc,
        aWordWeightQ_eq_aWordWeight, AWordField_cons,
        WpTwoAMProof.nprod_apply_grading_bounded
          (AFieldTwo_isField i) (AWordField_isField is)
          (i + 1) (aWordWeight is) (AFieldTwo_graded i)
          (AWordField_graded is) s hP]
      apply Finset.sum_congr rfl
      intro m hm
      rw [normalOrdered_apply]
      by_cases hm0 : 0 ≤ m
      · rw [if_pos hm0, if_pos hm0, Module.End.mul_apply,
          evalSparse_aFieldActSparseQ,
          evalSparse_aWordActSparseQ is (s - m) w P hP]
      · rw [if_neg hm0, if_neg hm0, Module.End.mul_apply]
        have hgrade := (AFieldTwo_graded i) m w (evalSparse ATwo' P) hP
        have hdegree : (i : ℤ) + 1 + (w : ℤ) + m =
            ((i + 1 + w : ℕ) : ℤ) + m := by
          push_cast
          ring
        rw [hdegree] at hgrade
        have hnext : evalSparse ATwo' (aFieldActSparseQ i m P) ∈
            gradingWN (rank Ltwo) ((i + 1 + w : ℕ) + m).toNat := by
          rw [evalSparse_aFieldActSparseQ]
          by_cases hd : 0 ≤ ((i + 1 + w : ℕ) : ℤ) + m
          · rw [gradingZN_of_nonneg hd] at hgrade
            simpa only [Int.toNat_of_nonneg hd] using hgrade
          · have hd' : ((i + 1 + w : ℕ) : ℤ) + m < 0 := by omega
            rw [gradingZN_of_neg hd', Submodule.mem_bot] at hgrade
            rw [hgrade]
            exact zero_mem (gradingWN (rank Ltwo) _)
        rw [evalSparse_aWordActSparseQ is (s - m) _
          (aFieldActSparseQ i m P) hnext, evalSparse_aFieldActSparseQ]

theorem evalSparse_sThreeSparseQ :
    evalSparse ATwo' sThreeSparseQ = vSchur Ltwo alphaTwo 3 := by
  rw [sThreeSparseQ, evalSparse_normalizeQ,
    evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ]
  have hsyntax : complexifyRawQ
      [(1 / 6, [0, 0, 0]), (1 / 2, [0, 1]), (1 / 3, [2])] =
        sThreeAPoly := by
    norm_num [complexifyRawQ, sThreeAPoly]
  rw [hsyntax, eval_sThreeAPoly]

/-- The sparse source recurrence evaluates to the original bounded complex evaluator. -/
theorem evalSparse_hProductSparseQ :
    evalSparse ATwo' hProductSparseQ = evalAPoly hProductAPoly := by
  have hsparse : evalSparse ATwo' sThreeSparseQ ∈
      gradingWN (rank Ltwo) 3 := by
    rw [evalSparse_sThreeSparseQ]
    exact Screen.vSchur_mem_gradingWN Ltwo alphaTwo 3
  have hcomplex : evalAPoly sThreeAPoly ∈ gradingWN (rank Ltwo) 3 := by
    rw [eval_sThreeAPoly]
    exact Screen.vSchur_mem_gradingWN Ltwo alphaTwo 3
  rw [hProductSparseQ, evalSparse_addQ, evalSparse_addQ,
    hPartZeroZeroZeroSparseQ, hPartZeroOneSparseQ, hPartTwoSparseQ,
    evalSparse_scaleQ, evalSparse_scaleQ, evalSparse_scaleQ,
    evalSparse_aWordActSparseQ [0, 0, 0] 4 3 sThreeSparseQ hsparse,
    evalSparse_aWordActSparseQ [0, 1] 4 3 sThreeSparseQ hsparse,
    evalSparse_aWordActSparseQ [2] 4 3 sThreeSparseQ hsparse]
  rw [hProductAPoly, evalAPoly_append, evalAPoly_append,
    eval_scaleAPoly, eval_scaleAPoly, eval_scaleAPoly,
    eval_aWordAct [0, 0, 0] 4 3 sThreeAPoly hcomplex,
    eval_aWordAct [0, 1] 4 3 sThreeAPoly hcomplex,
    eval_aWordAct [2] 4 3 sThreeAPoly hcomplex]
  rw [algebraMap_rat_mul_fock, algebraMap_rat_mul_fock,
    algebraMap_rat_mul_fock]
  rw [evalSparse_sThreeSparseQ, eval_sThreeAPoly]
  module

theorem evalSparse_hProductExpectedSparse :
    evalSparse ATwo' hProductExpectedSparse = evalAPoly hProductExpected := by
  rw [hProductExpectedSparse, evalSparse_normalizeQ,
    evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ]
  congr 1
  norm_num [complexifyRawQ, hProductExpectedRawQ, hProductExpected]

/-- Semantic conclusion of the independently checked 32-coordinate certificate. -/
theorem eval_hProductAPoly_eq_expected :
    evalAPoly hProductAPoly = evalAPoly hProductExpected := by
  rw [← evalSparse_hProductSparseQ, hProductSparseQ_eq_expected,
    evalSparse_hProductExpectedSparse]

/-- State-level endpoint consumed by the final Adamovic--Milas assembly. -/
theorem Htrip_neg_five_Htrip_eq_expected (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2) =
      latStateGen Ltwo (evalAPoly hProductExpected) 0 := by
  rw [WpTwoAMClose.Htrip_neg_five_Htrip_eq_hProduct hp,
    eval_hProductAPoly_eq_expected]

end VOA.LatGen.WpTwoAMSparseBridge

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMSparseBridge.hProductSparseQ_eq_expected
#print axioms VOA.LatGen.WpTwoAMSparseBridge.evalSparse_aWordActSparseQ
#print axioms VOA.LatGen.WpTwoAMSparseBridge.Htrip_neg_five_Htrip_eq_expected
end AxiomAudit

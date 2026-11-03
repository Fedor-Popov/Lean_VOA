/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoVirasoroCoords
import VOA.Examples.TripletWpTwoAMSchur
import VOA.Examples.TripletWpTwoMixed
import VOA.Core.Reconstruction

/-!
# Closing the finite Adamovic--Milas coordinate identity at `p = 2`

This file is an independent, executable audit of the two screened terms in the exact
weight-ten identity.  The Virasoro side is consumed from `TripletWpTwoVirasoroCoords`.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpTwoAMClose

open scoped BigOperators TensorProduct
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2
open VOA.LatGen.WpTwoVirasoroCoords

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private abbrev alphaTwo : Ltwo.carrier := alphaP 2
private noncomputable abbrev ATwo (i : ℕ) : FockN (rank Ltwo) := vVar Ltwo alphaTwo i

/-! ## The invariant rank-one current field -/

/-- The vertex field of one polynomial generator in an arbitrary Heisenberg family. -/
theorem YN_X (r i : ℕ) (a : Fin r) :
    YN r 1 (MvPolynomial.X (i, a)) = genFieldN r 1 a i := by
  rw [MvPolynomial.X, YN_monomial_one, YmonN]
  have hword : monoWordN (Finsupp.single (i, a) 1) = [(i, a)] := by
    unfold monoWordN
    rw [show (Finsupp.single (i, a) 1 : (ℕ × Fin r) →₀ ℕ).support = {(i, a)} from
      Finsupp.support_single (i, a) (by norm_num : (1 : ℕ) ≠ 0)]
    simp
  rw [hword, YwordN_cons]
  exact nprod_idFieldN (genFieldN_isField r 1 a i)

/-- The invariant field `Y(A_i,z)`, before using the rank-one specialization. -/
noncomputable def AFieldTwo (i : ℕ) : FormalDist (Module.End ℂ (FockN (rank Ltwo))) :=
  ∑ a : Fin (rank Ltwo), chargeCoord Ltwo alphaTwo a • genFieldN (rank Ltwo) 1 a i

/-- `YN` sends the invariant state coordinate `A_i` to the corresponding invariant current
derivative field. -/
theorem YN_ATwo (i : ℕ) : YN (rank Ltwo) 1 (ATwo i) = AFieldTwo i := by
  rw [ATwo, vVar, map_sum, AFieldTwo]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, YN_X]

/-- Exact coefficient of the invariant derivative current.  This is where the repository's
`z^s` convention and its rising-factorial derivative normalization are fixed. -/
theorem AFieldTwo_coeff (i : ℕ) (s : ℤ) :
    AFieldTwo i s =
      (((((∏ l ∈ Finset.range i, (s + 1 + l) : ℤ) : ℤ) : ℂ) *
          (i.factorial : ℂ)⁻¹) •
        chargeOsc Ltwo alphaTwo (-(s + i) - 1)) := by
  rw [AFieldTwo]
  have hsum :
      (∑ a : Fin (rank Ltwo), chargeCoord Ltwo alphaTwo a •
          genFieldN (rank Ltwo) 1 a i) s =
        ∑ a : Fin (rank Ltwo), chargeCoord Ltwo alphaTwo a •
          (genFieldN (rank Ltwo) 1 a i) s :=
    Finset.sum_apply s Finset.univ _
  rw [hsum, chargeOsc]
  simp_rw [genFieldN_coeff]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [chargeCoord]
  module

theorem AFieldTwo_isField (i : ℕ) : IsField (AFieldTwo i) := by
  rw [← YN_ATwo]
  exact YN_isField (rank Ltwo) 1 (ATwo i)

theorem AFieldTwo_graded (i : ℕ) :
    GradedFieldN (rank Ltwo) (AFieldTwo i) ((i : ℤ) + 1) := by
  rw [← YN_ATwo]
  exact YN_gradedField_of_mem (rank Ltwo) 1
    (Screen.vVar_mem_gradingWN Ltwo alphaTwo i)

/-- The `(-1)`-product by `A_i` is literal polynomial multiplication. -/
theorem heis_smul_ATwo_neg_one (i : ℕ) (q : FockN (rank Ltwo)) :
    (heisenbergNVOA (rank Ltwo) 1 (by norm_num)).smul (ATwo i) (-1) q =
      ATwo i * q := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  change (YN (rank Ltwo) 1 (ATwo i)) 0 q = ATwo i * q
  rw [YN_ATwo, AFieldTwo_coeff]
  have hprod : ∏ x ∈ Finset.range i, (1 + (x : ℤ)) = (i.factorial : ℤ) := by
    simpa using prod_range_zero_eq_factorialN i
  simp only [zero_add]
  rw [hprod, LinearMap.smul_apply]
  norm_num [Nat.factorial_ne_zero]
  rw [show -(i : ℤ) - 1 = -((i : ℤ) + 1) by ring]
  rw [chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply]

/-- State multiplication by one invariant coordinate is represented by one normal product. -/
theorem YN_mul_ATwo (i : ℕ) (q : FockN (rank Ltwo)) :
    YN (rank Ltwo) 1 (ATwo i * q) =
      nprod (AFieldTwo_isField i) (YN_isField (rank Ltwo) 1 q) := by
  let W := heisenbergNVOA (rank Ltwo) 1 (by norm_num)
  have h := W.assoc_neg (ATwo i) q 0
  dsimp [W] at h
  norm_num at h
  rw [heis_smul_ATwo_neg_one] at h
  change YN (rank Ltwo) 1 (ATwo i * q) = _ at h
  rw [negProd] at h
  norm_num at h
  change YN (rank Ltwo) 1 (ATwo i * q) =
      nprod (YN_isField (rank Ltwo) 1 (ATwo i))
        (YN_isField (rank Ltwo) 1 q) at h
  exact h.trans (nprodN_eq_nprodN
    (YN_isField (rank Ltwo) 1 (ATwo i)) (YN_isField (rank Ltwo) 1 q)
    (AFieldTwo_isField i) (YN_isField (rank Ltwo) 1 q) (YN_ATwo i) rfl)

/-- Right-associated invariant normal products, matching `evalAWord`. -/
noncomputable def AWordFieldF :
    List ℕ → {f : FormalDist (Module.End ℂ (FockN (rank Ltwo))) // IsField f}
  | [] => ⟨idFieldN (rank Ltwo), idFieldN_isField (rank Ltwo)⟩
  | i :: is =>
      let p := AWordFieldF is
      ⟨nprod (AFieldTwo_isField i) p.2, (AFieldTwo_isField i).nprod p.2⟩

noncomputable def AWordField (is : List ℕ) :
    FormalDist (Module.End ℂ (FockN (rank Ltwo))) := (AWordFieldF is).1

theorem AWordField_isField (is : List ℕ) : IsField (AWordField is) :=
  (AWordFieldF is).2

@[simp] theorem AWordField_nil : AWordField [] = idFieldN (rank Ltwo) := rfl

theorem AWordField_cons (i : ℕ) (is : List ℕ) :
    AWordField (i :: is) =
      nprod (AFieldTwo_isField i) (AWordField_isField is) := rfl

/-- The invariant word-field bridge, avoiding any choice of orthonormal rank-one coordinate. -/
theorem YN_evalAWord : ∀ is : List ℕ,
    YN (rank Ltwo) 1 (evalAWord is) = AWordField is
  | [] => by rw [evalAWord, YN_vacuum, AWordField_nil]
  | i :: is => by
      rw [evalAWord, YN_mul_ATwo, AWordField_cons]
      exact nprodN_eq_nprodN (AFieldTwo_isField i)
        (YN_isField (rank Ltwo) 1 (evalAWord is))
        (AFieldTwo_isField i) (AWordField_isField is) rfl (YN_evalAWord is)

theorem evalAWord_eq_map_prod (is : List ℕ) :
    evalAWord is = (is.map ATwo).prod * vacuumN (rank Ltwo) := by
  induction is with
  | nil => simp [evalAWord]
  | cons i is ih =>
      rw [evalAWord, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

theorem evalAWord_perm {is js : List ℕ} (h : is.Perm js) :
    evalAWord is = evalAWord js := by
  rw [evalAWord_eq_map_prod, evalAWord_eq_map_prod]
  rw [(h.map ATwo).prod_eq]

theorem evalAWord_mergeSort (is : List ℕ) :
    evalAWord is =
      evalAWord (is.mergeSort fun i j => decide (i ≤ j)) :=
  evalAWord_perm (List.mergeSort_perm is _).symm

noncomputable def evalAWordSorted (is : List ℕ) : FockN (rank Ltwo) :=
  evalAWord (is.mergeSort fun i j => decide (i ≤ j))

theorem evalAWord_eq_sorted (is : List ℕ) :
    evalAWord is = evalAWordSorted is :=
  evalAWord_mergeSort is

/-! ## Executable action of the invariant current -/

/-- Positive invariant oscillators contract exactly one matching creation coordinate. -/
theorem chargeOsc_pos_ATwo (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    chargeOsc Ltwo alphaTwo (n : ℤ) (ATwo i) =
      if n = i + 1 then (4 * (n : ℂ)) • vacuumN (rank Ltwo) else 0 := by
  have h := congrArg
    (fun T : Module.End ℂ (FockN (rank Ltwo)) => T (vacuumN (rank Ltwo)))
    (chargeOsc_comm Ltwo (latP_posDef 2 (by norm_num)) alphaTwo alphaTwo
      (n : ℤ) (-((i : ℤ) + 1)))
  simp only [Module.End.mul_apply, LinearMap.sub_apply] at h
  rw [WpTwoAMCoords.chargeOsc_neg_vacuum_eq_vVar,
    chargeOsc_vacuum Ltwo alphaTwo (n : ℤ) (by positivity), map_zero, sub_zero] at h
  have hform : Ltwo.form alphaTwo alphaTwo = 4 := by simpa using latP_form_alpha 2
  rw [hform] at h
  by_cases hni : n = i + 1
  · rw [if_pos hni]
    rw [if_pos (by omega)] at h
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, Int.cast_ofNat] using h
  · rw [if_neg hni]
    rw [if_neg (by omega)] at h
    simpa using h

/-- Syntactic contraction of a positive `alpha(n)` with one invariant coordinate word. -/
def annihilateAWord (n : ℕ) : List ℕ → APolyTwo
  | [] => []
  | i :: is =>
      (if n = i + 1 then [((4 : ℂ) * n, is)] else []) ++
        prependA i (annihilateAWord n is)

theorem eval_annihilateAWord (n : ℕ) (hn : 1 ≤ n) : ∀ is : List ℕ,
    evalAPoly (annihilateAWord n is) =
      chargeOsc Ltwo alphaTwo (n : ℤ) (evalAWord is)
  | [] => by
      rw [annihilateAWord, evalAPoly_nil, evalAWord,
        chargeOsc_vacuum Ltwo alphaTwo (n : ℤ) (by positivity)]
  | i :: is => by
      rw [annihilateAWord, evalAPoly_append, eval_prependA, evalAWord,
        WpC2.chargeOsc_mul' Ltwo alphaTwo (by exact_mod_cast hn),
        chargeOsc_pos_ATwo n hn i, ← eval_annihilateAWord n hn is]
      by_cases hni : n = i + 1
      · rw [if_pos hni, evalAPoly_singleton, if_pos hni]
        simp only [vacuumN, one_mul, smul_mul_assoc]
      · rw [if_neg hni, evalAPoly_nil, if_neg hni, zero_mul, zero_add]

/-- The derivative normalization multiplying the oscillator in `Y(A_i,z)_s`. -/
noncomputable def aFieldCoeff (i : ℕ) (s : ℤ) : ℂ :=
  (((∏ l ∈ Finset.range i, (s + 1 + l) : ℤ) : ℤ) : ℂ) *
    (i.factorial : ℂ)⁻¹

/-- Oscillator mode occurring in `Y(A_i,z)_s`. -/
def aFieldMode (i : ℕ) (s : ℤ) : ℤ := -(s + i) - 1

/-- Executable action of one invariant derivative-current coefficient on one word. -/
noncomputable def aFieldActWord (i : ℕ) (s : ℤ) (is : List ℕ) : APolyTwo :=
  if aFieldMode i s < 0 then
    scaleAPoly (aFieldCoeff i s)
      (prependA (-aFieldMode i s - 1).toNat [(1, is)])
  else if aFieldMode i s = 0 then []
  else
    scaleAPoly (aFieldCoeff i s)
      (annihilateAWord (aFieldMode i s).toNat is)

/-- Executable action on a finite polynomial. -/
noncomputable def aFieldActPoly (i : ℕ) (s : ℤ) (P : APolyTwo) : APolyTwo :=
  P.flatMap fun t => scaleAPoly t.1 (aFieldActWord i s t.2)

theorem eval_aFieldActWord (i : ℕ) (s : ℤ) (is : List ℕ) :
    evalAPoly (aFieldActWord i s is) = AFieldTwo i s (evalAWord is) := by
  rw [AFieldTwo_coeff, LinearMap.smul_apply]
  change evalAPoly (aFieldActWord i s is) =
    aFieldCoeff i s • chargeOsc Ltwo alphaTwo (aFieldMode i s) (evalAWord is)
  rw [aFieldActWord]
  by_cases hneg : aFieldMode i s < 0
  · rw [if_pos hneg, eval_scaleAPoly, eval_prependA, evalAPoly_singleton]
    have hidx : aFieldMode i s = -(((-aFieldMode i s - 1).toNat : ℕ) : ℤ) - 1 := by
      omega
    rw [hidx, show -(((-aFieldMode i s - 1).toNat : ℕ) : ℤ) - 1 =
        -((((-aFieldMode i s - 1).toNat : ℕ) : ℤ) + 1) by ring,
      chargeOsc_neg_eq_mulLeft_vVar, LinearMap.mulLeft_apply]
    simp only [one_smul]
    rw [show (- -((((-aFieldMode i s - 1).toNat : ℕ) : ℤ) + 1) - 1).toNat =
        (-aFieldMode i s - 1).toNat by omega]
  · rw [if_neg hneg]
    by_cases hzero : aFieldMode i s = 0
    · rw [if_pos hzero, evalAPoly_nil, hzero]
      simp [chargeOsc]
    · rw [if_neg hzero, eval_scaleAPoly]
      have hpos : 1 ≤ (aFieldMode i s).toNat := by omega
      rw [eval_annihilateAWord (aFieldMode i s).toNat hpos]
      rw [show (((aFieldMode i s).toNat : ℕ) : ℤ) = aFieldMode i s by omega]

theorem eval_aFieldActPoly (i : ℕ) (s : ℤ) : ∀ P : APolyTwo,
    evalAPoly (aFieldActPoly i s P) = AFieldTwo i s (evalAPoly P)
  | [] => by simp [aFieldActPoly, map_zero]
  | t :: P => by
      rcases t with ⟨c, is⟩
      change evalAPoly
          (scaleAPoly c (aFieldActWord i s is) ++ aFieldActPoly i s P) =
        AFieldTwo i s (c • evalAWord is + evalAPoly P)
      rw [evalAPoly_append, eval_scaleAPoly, eval_aFieldActWord,
        eval_aFieldActPoly i s P, map_add, map_smul]

/-! ## A bounded normal-product evaluator -/

def aWordWeight : List ℕ → ℕ
  | [] => 0
  | i :: is => i + 1 + aWordWeight is

theorem evalAWord_mem_grading : ∀ is : List ℕ,
    evalAWord is ∈ gradingWN (rank Ltwo) (aWordWeight is)
  | [] => by simpa [evalAWord, aWordWeight] using vacuumN_mem_gradingWN (rank Ltwo)
  | i :: is => by
      rw [evalAWord, aWordWeight, mem_gradingWN]
      have hi := Screen.vVar_mem_gradingWN Ltwo alphaTwo i
      have his := evalAWord_mem_grading is
      rw [mem_gradingWN] at hi his
      exact hi.mul his

theorem AWordField_graded (is : List ℕ) :
    GradedFieldN (rank Ltwo) (AWordField is) (aWordWeight is : ℤ) := by
  rw [← YN_evalAWord]
  exact YN_gradedField_of_mem (rank Ltwo) 1 (evalAWord_mem_grading is)

/-- Concatenation of the polynomial values indexed by a finite set. -/
noncomputable def sumAPoly {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) (f : ι → APolyTwo) : APolyTwo :=
  s.toList.flatMap f

theorem evalAPoly_flatMap {ι : Type*} (l : List ι) (f : ι → APolyTwo) :
    evalAPoly (l.flatMap f) = (l.map fun x => evalAPoly (f x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem eval_sumAPoly {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) (f : ι → APolyTwo) :
    evalAPoly (sumAPoly s f) = ∑ x ∈ s, evalAPoly (f x) := by
  rw [sumAPoly, evalAPoly_flatMap]
  have h := List.sum_toFinset (fun x => evalAPoly (f x)) s.nodup_toList
  rw [Finset.toList_toFinset] at h
  exact h.symm

/-- A kernel-computable ascending list of all integers in `[lo,hi]`. -/
def intIccList (lo hi : ℤ) : List ℤ :=
  (List.range (hi - lo + 1).toNat).map fun n : ℕ => lo + (n : ℤ)

private theorem intIccList_neg_two_eight :
    intIccList (-2) 8 = [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem intIccList_neg_one_eight :
    intIccList (-1) 8 = [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem intIccList_neg_three_eight :
    intIccList (-3) 8 = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem intIccList_neg_four_eight :
    intIccList (-4) 8 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem intIccList_neg_five_eight :
    intIccList (-5) 8 = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem intIccList_neg_five_seven :
    intIccList (-5) 7 = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7] := by rfl
private theorem intIccList_neg_five_six :
    intIccList (-5) 6 = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6] := by rfl
private theorem intIccList_neg_five_five :
    intIccList (-5) 5 = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5] := by rfl
private theorem intIccList_neg_five_four :
    intIccList (-5) 4 = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4] := by rfl
private theorem intIccList_neg_five_three :
    intIccList (-5) 3 = [-5, -4, -3, -2, -1, 0, 1, 2, 3] := by rfl
private theorem intIccList_neg_five_two :
    intIccList (-5) 2 = [-5, -4, -3, -2, -1, 0, 1, 2] := by rfl
private theorem intIccList_neg_five_one :
    intIccList (-5) 1 = [-5, -4, -3, -2, -1, 0, 1] := by rfl
private theorem intIccList_neg_five_zero :
    intIccList (-5) 0 = [-5, -4, -3, -2, -1, 0] := by rfl
private theorem intIccList_neg_five_neg_one :
    intIccList (-5) (-1) = [-5, -4, -3, -2, -1] := by rfl
private theorem intIccList_neg_one_nine :
    intIccList (-1) 9 = [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by rfl
private theorem intIccList_neg_two_nine :
    intIccList (-2) 9 = [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by rfl
private theorem intIccList_neg_three_nine :
    intIccList (-3) 9 = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by rfl
private theorem intIccList_neg_four_nine :
    intIccList (-4) 9 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by rfl
private theorem intIccList_neg_four_seven :
    intIccList (-4) 7 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7] := by rfl
private theorem intIccList_neg_four_six :
    intIccList (-4) 6 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6] := by rfl
private theorem intIccList_neg_four_five :
    intIccList (-4) 5 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5] := by rfl
private theorem intIccList_neg_four_four :
    intIccList (-4) 4 = [-4, -3, -2, -1, 0, 1, 2, 3, 4] := by rfl
private theorem intIccList_neg_four_three :
    intIccList (-4) 3 = [-4, -3, -2, -1, 0, 1, 2, 3] := by rfl
private theorem intIccList_neg_four_two :
    intIccList (-4) 2 = [-4, -3, -2, -1, 0, 1, 2] := by rfl
private theorem intIccList_neg_four_one :
    intIccList (-4) 1 = [-4, -3, -2, -1, 0, 1] := by rfl
private theorem intIccList_neg_four_zero :
    intIccList (-4) 0 = [-4, -3, -2, -1, 0] := by rfl
private theorem intIccList_neg_four_neg_one :
    intIccList (-4) (-1) = [-4, -3, -2, -1] := by rfl

private theorem range_zero : List.range 0 = [] := by rfl
private theorem range_one : List.range 1 = [0] := by rfl
private theorem range_two : List.range 2 = [0, 1] := by rfl
private theorem range_three : List.range 3 = [0, 1, 2] := by rfl
private theorem range_four : List.range 4 = [0, 1, 2, 3] := by rfl
private theorem range_five : List.range 5 = [0, 1, 2, 3, 4] := by rfl
private theorem range_six : List.range 6 = [0, 1, 2, 3, 4, 5] := by rfl
private theorem range_seven : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := by rfl
private theorem range_eight : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by rfl
private theorem range_nine : List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by rfl
private theorem range_ten : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by rfl
private theorem range_eleven :
    List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by rfl
private theorem range_twelve :
    List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by rfl
private theorem range_thirteen :
    List.range 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by rfl
private theorem range_fourteen :
    List.range 14 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by rfl

theorem intIccList_nodup (lo hi : ℤ) : (intIccList lo hi).Nodup := by
  rw [intIccList]
  apply List.Nodup.map (f := fun n : ℕ => lo + (n : ℤ))
  · intro x y h
    exact_mod_cast (add_left_cancel h)
  · exact List.nodup_range

theorem intIccList_toFinset (lo hi : ℤ) :
    (intIccList lo hi).toFinset = Finset.Icc lo hi := by
  ext x
  simp only [intIccList, List.mem_toFinset, List.mem_map, List.mem_range,
    Finset.mem_Icc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hnZ : (n : ℤ) < hi - lo + 1 := by
      have hlen : 0 ≤ hi - lo + 1 := by omega
      omega
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(x - lo).toNat, ?_, ?_⟩
    · have hdiff : 0 ≤ x - lo := by omega
      have hlen : 0 ≤ hi - lo + 1 := by omega
      omega
    · omega

noncomputable def sumAPolyIcc (lo hi : ℤ) (f : ℤ → APolyTwo) : APolyTwo :=
  (intIccList lo hi).flatMap f

theorem eval_sumAPolyIcc (lo hi : ℤ) (f : ℤ → APolyTwo) :
    evalAPoly (sumAPolyIcc lo hi f) = ∑ x ∈ Finset.Icc lo hi, evalAPoly (f x) := by
  rw [sumAPolyIcc, evalAPoly_flatMap]
  have h := List.sum_toFinset (fun x => evalAPoly (f x)) (intIccList_nodup lo hi)
  rw [intIccList_toFinset] at h
  exact h.symm

private theorem sum_Icc_neg_six_seven {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (-6 : ℤ) 7, f m =
      f (-6) + f (-5) + f (-4) + f (-3) + f (-2) + f (-1) + f 0 +
      f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h : Finset.Icc (-6 : ℤ) 7 =
      {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

private theorem sum_Icc_neg_four_nine {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (-4 : ℤ) 9, f m =
      f (-4) + f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 +
      f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have h : Finset.Icc (-4 : ℤ) 9 =
      {-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

private theorem sum_Icc_neg_one_nine {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ m ∈ Finset.Icc (-1 : ℤ) 9, f m =
      f (-1) + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have h : Finset.Icc (-1 : ℤ) 9 = {-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp
  abel

/-- The fully executable, grading-bounded action of an invariant normal-product word. -/
noncomputable def aWordAct : List ℕ → ℤ → ℕ → APolyTwo → APolyTwo
  | [], s, _w, P => if s = 0 then P else []
  | i :: is, s, w, P =>
      sumAPolyIcc (-((i + 1 + w : ℕ) : ℤ))
          (max (-1) ((aWordWeight is + w : ℕ) + s))
        fun m => if 0 ≤ m then
          aFieldActPoly i m (aWordAct is (s - m) w P)
        else
          aWordAct is (s - m) ((i + 1 + w : ℕ) + m).toNat
            (aFieldActPoly i m P)

theorem eval_aWordAct : ∀ (is : List ℕ) (s : ℤ) (w : ℕ) (P : APolyTwo),
    evalAPoly P ∈ gradingWN (rank Ltwo) w →
      evalAPoly (aWordAct is s w P) = AWordField is s (evalAPoly P)
  | [], s, w, P, hP => by
      rw [aWordAct, AWordField_nil, idFieldN_apply]
      by_cases hs : s = 0
      · rw [if_pos hs, if_pos hs, LinearMap.id_apply]
      · rw [if_neg hs, if_neg hs, evalAPoly_nil, LinearMap.zero_apply]
  | i :: is, s, w, P, hP => by
      rw [aWordAct, eval_sumAPolyIcc, AWordField_cons,
        WpTwoAMProof.nprod_apply_grading_bounded
          (AFieldTwo_isField i) (AWordField_isField is)
          (i + 1) (aWordWeight is) (AFieldTwo_graded i)
          (AWordField_graded is) s hP]
      apply Finset.sum_congr rfl
      intro m hm
      rw [normalOrdered_apply]
      by_cases hm0 : 0 ≤ m
      · rw [if_pos hm0, if_pos hm0, Module.End.mul_apply,
          eval_aFieldActPoly, eval_aWordAct is (s - m) w P hP]
      · rw [if_neg hm0, if_neg hm0, Module.End.mul_apply]
        have hgrade := (AFieldTwo_graded i) m w (evalAPoly P) hP
        have hdegree : (i : ℤ) + 1 + (w : ℤ) + m = ((i + 1 + w : ℕ) : ℤ) + m := by
          push_cast
          ring
        rw [hdegree] at hgrade
        have hnext : evalAPoly (aFieldActPoly i m P) ∈
            gradingWN (rank Ltwo) ((i + 1 + w : ℕ) + m).toNat := by
          rw [eval_aFieldActPoly]
          by_cases hd : 0 ≤ ((i + 1 + w : ℕ) : ℤ) + m
          · rw [gradingZN_of_nonneg hd] at hgrade
            simpa only [Int.toNat_of_nonneg hd] using hgrade
          · have hd' : ((i + 1 + w : ℕ) : ℤ) + m < 0 := by omega
            rw [gradingZN_of_neg hd', Submodule.mem_bot] at hgrade
            rw [hgrade]
            exact zero_mem (gradingWN (rank Ltwo) _)
        rw [eval_aWordAct is (s - m) _ (aFieldActPoly i m P) hnext,
          eval_aFieldActPoly]

/-! ## The exact `H_{-5}H` polynomial -/

noncomputable def sThreeAPoly : APolyTwo :=
  [(1 / 6, [0, 0, 0]), (1 / 2, [0, 1]), (1 / 3, [2])]

theorem eval_sThreeAPoly :
    evalAPoly sThreeAPoly = vSchur Ltwo alphaTwo 3 := by
  rw [sThreeAPoly, WpC2.vSchur_three']
  simp only [evalAPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    evalAWord, add_zero, vacuumN, mul_one]
  ring

theorem YN_sThree :
    YN (rank Ltwo) 1 (vSchur Ltwo alphaTwo 3) =
      (1 / 6 : ℂ) • AWordField [0, 0, 0]
        + (1 / 2 : ℂ) • AWordField [0, 1]
        + (1 / 3 : ℂ) • AWordField [2] := by
  rw [← eval_sThreeAPoly]
  simp only [sThreeAPoly, evalAPoly, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, map_add, map_smul, YN_evalAWord]
  module

noncomputable def hProductAPoly : APolyTwo :=
  scaleAPoly (1 / 6 : ℂ) (aWordAct [0, 0, 0] 4 3 sThreeAPoly)
    ++ scaleAPoly (1 / 2 : ℂ) (aWordAct [0, 1] 4 3 sThreeAPoly)
    ++ scaleAPoly (1 / 3 : ℂ) (aWordAct [2] 4 3 sThreeAPoly)

noncomputable def hProductPartTwo : APolyTwo :=
  scaleAPoly (1 / 3 : ℂ) (aWordAct [2] 4 3 sThreeAPoly)

noncomputable def hProductExpectedTwo : APolyTwo :=
  [(5 / 6, [0, 0, 0, 6]),
   (5 / 2, [0, 1, 6]),
   (5 / 3, [2, 6])]

noncomputable def hProductPartZeroOne : APolyTwo :=
  scaleAPoly (1 / 2 : ℂ) (aWordAct [0, 1] 4 3 sThreeAPoly)

noncomputable def hProductExpectedZeroOne : APolyTwo :=
  [(5 / 12, [0, 0, 0, 2, 3]),
   (5 / 4, [0, 1, 2, 3]),
   (5 / 6, [2, 2, 3]),
   (5 / 12, [0, 0, 0, 1, 4]),
   (5 / 4, [0, 1, 1, 4]),
   (5 / 6, [1, 2, 4]),
   (5 / 12, [0, 0, 0, 0, 5]),
   (5 / 4, [0, 0, 1, 5]),
   (5 / 6, [0, 2, 5]),
   (5, [0, 0, 7]),
   (5, [1, 7]),
   (10, [0, 8]),
   (10, [9])]

/-- Direct evaluation of the three source monomials against the three target monomials. -/
theorem YN_sThree_four_sThree_eq_hProduct :
    YN (rank Ltwo) 1 (vSchur Ltwo alphaTwo 3) 4
        (vSchur Ltwo alphaTwo 3) = evalAPoly hProductAPoly := by
  have hgrade := Screen.vSchur_mem_gradingWN Ltwo alphaTwo 3
  have hP : evalAPoly sThreeAPoly ∈ gradingWN (rank Ltwo) 3 := by
    rwa [eval_sThreeAPoly]
  rw [hProductAPoly, evalAPoly_append, evalAPoly_append,
    eval_scaleAPoly, eval_scaleAPoly, eval_scaleAPoly,
    eval_aWordAct [0, 0, 0] 4 3 sThreeAPoly hP,
    eval_aWordAct [0, 1] 4 3 sThreeAPoly hP,
    eval_aWordAct [2] 4 3 sThreeAPoly hP]
  rw [YN_sThree]
  change ((1 / 6 : ℂ) • AWordField [0, 0, 0] 4
        + (1 / 2 : ℂ) • AWordField [0, 1] 4
        + (1 / 3 : ℂ) • AWordField [2] 4)
      (vSchur Ltwo alphaTwo 3) = _
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [eval_sThreeAPoly]

/-- Independent, human-readable normal form of the 32 nonzero weight-ten monomials. -/
noncomputable def hProductExpected : APolyTwo :=
  [(1 / 12, [0, 0, 0, 1, 1, 2]),
   (1 / 4, [0, 1, 1, 1, 2]),
   (1 / 12, [0, 0, 0, 0, 2, 2]),
   (1 / 4, [0, 0, 1, 2, 2]),
   (1 / 6, [1, 1, 2, 2]),
   (1 / 6, [0, 2, 2, 2]),
   (1 / 6, [0, 0, 0, 0, 1, 3]),
   (1 / 2, [0, 0, 1, 1, 3]),
   (5 / 12, [0, 0, 0, 2, 3]),
   (19 / 12, [0, 1, 2, 3]),
   (5 / 6, [2, 2, 3]),
   (1, [0, 0, 3, 3]),
   (1, [1, 3, 3]),
   (1 / 12, [0, 0, 0, 0, 0, 4]),
   (2 / 3, [0, 0, 0, 1, 4]),
   (5 / 4, [0, 1, 1, 4]),
   (13 / 6, [0, 0, 2, 4]),
   (17 / 6, [1, 2, 4]),
   (4, [0, 3, 4]),
   (2, [4, 4]),
   (5 / 12, [0, 0, 0, 0, 5]),
   (13 / 4, [0, 0, 1, 5]),
   (2, [1, 1, 5]),
   (29 / 6, [0, 2, 5]),
   (4, [3, 5]),
   (17 / 6, [0, 0, 0, 6]),
   (17 / 2, [0, 1, 6]),
   (17 / 3, [2, 6]),
   (9, [0, 0, 7]),
   (9, [1, 7]),
   (22, [0, 8]),
   (26, [9])]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The one-current source word is the smallest independently checkable part of the
32-term calculation. -/
theorem eval_hProductPartTwo :
    evalAPoly hProductPartTwo = evalAPoly hProductExpectedTwo := by
  rw [hProductPartTwo, eval_scaleAPoly, aWordAct, eval_sumAPolyIcc]
  norm_num [aWordWeight]
  rw [sum_Icc_neg_six_seven]
  norm_num [hProductExpectedTwo, sThreeAPoly, aWordAct, aWordWeight,
    aFieldActPoly, aFieldActWord, aFieldMode, aFieldCoeff, annihilateAWord,
    scaleAPoly, prependA, evalAPoly, evalAWord]
  norm_num [Finset.prod_range_succ]
  rw [show Int.toNat 6 = 6 by norm_num [Int.toNat]]
  have h0 : ATwo 6 * (ATwo 0 * (ATwo 0 * (ATwo 0 * vacuumN (rank Ltwo)))) =
      ATwo 0 * (ATwo 0 * (ATwo 0 * (ATwo 6 * vacuumN (rank Ltwo)))) := by ring
  have h1 : ATwo 6 * (ATwo 0 * (ATwo 1 * vacuumN (rank Ltwo))) =
      ATwo 0 * (ATwo 1 * (ATwo 6 * vacuumN (rank Ltwo))) := by ring
  have h2 : ATwo 6 * (ATwo 2 * vacuumN (rank Ltwo)) =
      ATwo 2 * (ATwo 6 * vacuumN (rank Ltwo)) := by ring
  rw [h0, h1, h2]
  module

/-- Literal finite certificate for the two-current source word. -/
theorem eval_hProductPartZeroOne :
    evalAPoly hProductPartZeroOne = evalAPoly hProductExpectedZeroOne := by
  rw [hProductPartZeroOne, eval_scaleAPoly, aWordAct, eval_sumAPolyIcc]
  norm_num [aWordWeight]
  rw [sum_Icc_neg_four_nine]
  norm_num [hProductExpectedZeroOne, sThreeAPoly, aWordAct, aWordWeight,
    sumAPolyIcc,
    intIccList_neg_two_eight, intIccList_neg_three_eight,
    intIccList_neg_four_eight, intIccList_neg_five_eight,
    intIccList_neg_five_seven, intIccList_neg_five_six,
    intIccList_neg_five_five, intIccList_neg_five_four,
    intIccList_neg_five_three, intIccList_neg_five_two,
    intIccList_neg_five_one, intIccList_neg_five_zero,
    intIccList_neg_five_neg_one,
    aFieldActPoly, aFieldActWord, aFieldMode, aFieldCoeff, annihilateAWord,
    scaleAPoly, prependA, evalAPoly]
  norm_num [Finset.prod_range_succ, Int.toNat]
  simp_rw [evalAWord_eq_sorted]
  norm_num [evalAWordSorted, List.mergeSort, evalAWord]
  module

/-! ## Cocycle and published-coefficient audits -/

theorem cocycle_two (a b : Ltwo.carrier) : latticeCocycle Ltwo a b = 1 :=
  WpTwoAMProof.latticeCocycle_latP_two a b

theorem published_B_two : (1024 / 1575 : ℂ) ≠ 0 := by norm_num

/-! ## The double-screened state -/

/-- Both screenings, with both cocycle orientations still visible until the last step. -/
theorem Qwp_sq_neg_two_eq_EEVec (hp : 1 ≤ 2) :
    Qwp 2 hp (Qwp 2 hp
        (latChargeGen Ltwo (-alphaTwo + -alphaTwo))) =
      latStateGen Ltwo
        (EEVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7)) 0 := by
  rw [Qwp_eq_Qscr, Screen.Qscr_latChargeGen]
  have hself : Ltwo.form alphaTwo alphaTwo = 4 := by
    simpa using latP_form_alpha 2
  have hformOuter : Ltwo.form alphaTwo (-alphaTwo + -alphaTwo) = -8 := by
    rw [map_add, map_neg]
    change -Ltwo.form alphaTwo alphaTwo + -Ltwo.form alphaTwo alphaTwo = -8
    rw [hself]
    norm_num
  rw [hformOuter]
  norm_num
  rw [EEVec_vacuum]
  norm_num
  rw [Screen.Qscr_latStateGen]
  have hformInner : Ltwo.form alphaTwo (-alphaTwo) = -4 := by
    rw [map_neg]
    change -Ltwo.form alphaTwo alphaTwo = -4
    rw [hself]
  rw [hformInner]
  norm_num
  rw [cocycle_two, cocycle_two]
  simp only [one_smul]
  change latStateGen Ltwo
      (EEVec Ltwo alphaTwo 3 (vSchur Ltwo alphaTwo 7)) 0 = _
  rfl

/-- The screened side in the independently audited three-term Schur normal form. -/
theorem Qwp_sq_neg_two_eq_schur (hp : 1 ≤ 2) :
    Qwp 2 hp (Qwp 2 hp
        (latChargeGen Ltwo (-alphaTwo + -alphaTwo))) =
      latStateGen Ltwo
        ((2 : ℂ) • (vSchur Ltwo alphaTwo 3 * vSchur Ltwo alphaTwo 7) +
          (-8 : ℂ) • (vSchur Ltwo alphaTwo 4 * vSchur Ltwo alphaTwo 6) +
          (6 : ℂ) • (vSchur Ltwo alphaTwo 5 * vSchur Ltwo alphaTwo 5)) 0 := by
  rw [Qwp_sq_neg_two_eq_EEVec hp,
    WpTwoAMSchur.EEVec_three_vSchur_seven_eq]

/-- The exact lattice lift of the bounded 32-coordinate evaluator.  The mode audit is explicit:
the VOA product at mode `-5` is field coefficient `4`. -/
theorem Htrip_neg_five_Htrip_eq_hProduct (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).smul (Htrip 2) (-5) (Htrip 2) =
      latStateGen Ltwo (evalAPoly hProductAPoly) 0 := by
  rw [Htrip, Screen.Hscr_eq Ltwo alphaTwo 2 hp (latP_form_alpha 2),
    cocycle_two, one_smul, PreVertexAlgebra.smul_def, mode_apply,
    tripletLatticeVOA_Y]
  change YfullGen Ltwo (latP_even 2) (latP_posDef 2 hp)
      (mkEα Ltwo 0 (vSchur Ltwo alphaTwo 3)) 4
      (mkEα Ltwo 0 (vSchur Ltwo alphaTwo 3)) =
    mkEα Ltwo 0 (evalAPoly hProductAPoly)
  rw [(WpTwoAMCoords.YfullGen_neutralFieldLift
    (latP_even 2) (latP_posDef 2 hp) (vSchur Ltwo alphaTwo 3))]
  rw [YN_sThree_four_sThree_eq_hProduct]

end VOA.LatGen.WpTwoAMClose

section AxiomAudit
#print axioms VOA.LatGen.WpTwoAMClose.cocycle_two
#print axioms VOA.LatGen.WpTwoAMClose.published_B_two
#print axioms VOA.LatGen.WpTwoAMClose.Qwp_sq_neg_two_eq_EEVec
end AxiomAudit

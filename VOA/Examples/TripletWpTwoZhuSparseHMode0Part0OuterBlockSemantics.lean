/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseSemantics
import VOA.Examples.TripletWpTwoZhuSparseHMode0Part0OuterPosABlock3

/-! # Evaluated three-block assembly for nonnegative mode-zero cubic summands

Literal sparse-list additivity is deliberately not required here: the canonical merge operation
stores a representation invariant that is expensive to replay.  The state evaluator is linear,
and state equality is the endpoint used by the intrinsic Zhu certificate.  This file therefore
certifies the three right-state blocks individually and assembles them after evaluation.
-/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.SparseRational
open VOA.LatGen VOA.LatGen.WpTwoAMClose
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoAMSparseBridge
open VOA.LatGen.WpTwoZhuSparseCompute

private noncomputable abbrev LtwoBlock : IntegralLattice := sparseLatticeTwo

/-- A sparse coordinate supported on words of one weight evaluates in that weight space. -/
theorem evalZhuSparseQ_mem_gradingWN_of_word_weights
    (P : SparseRational.Poly ℕ) (w : ℕ)
    (hP : ∀ t ∈ P, aWordWeight t.1 = w) :
    evalZhuSparseQ P ∈ gradingWN (rank LtwoBlock) w := by
  induction P with
  | nil =>
      rw [evalZhuSparseQ_nil]
      exact Submodule.zero_mem _
  | cons t P ih =>
      rcases t with ⟨word, q⟩
      unfold evalZhuSparseQ evalSparse
      simp only [List.map_cons, List.sum_cons]
      rw [evalWord_ATwo', algebraMap_rat_mul_fock]
      apply Submodule.add_mem
      · apply Submodule.smul_mem
        have hw := evalAWord_mem_grading word
        simpa [hP (word, q) (by simp)] using hw
      · apply ih
        intro u hu
        exact hP u (by simp [hu])

/-- Each right-state block is homogeneous of weight six. -/
theorem evalZhuSparseQ_l3hBlockSparseQ_mem_gradingWN (k : ℕ) (hk : k < 3) :
    evalZhuSparseQ (l3hBlockSparseQ k) ∈ gradingWN (rank LtwoBlock) 6 := by
  apply evalZhuSparseQ_mem_gradingWN_of_word_weights
  intro t ht
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl <;>
    simp [l3hBlockSparseQ] at ht <;>
    rcases ht with rfl | rfl | rfl <;>
    norm_num [aWordWeight]

/-- The three contiguous blocks are exactly the audited `L(-3)H` sparse coordinate. -/
theorem l3hExpectedQ_eq_sum_blocks :
    l3hExpectedQ = sumQ [l3hBlockSparseQ 0, l3hBlockSparseQ 1,
      l3hBlockSparseQ 2] := by
  norm_num [l3hExpectedQ, l3hBlockSparseQ, sumQ, addQ, compareWord]

/-- Uniform evaluated additivity for every nonnegative outer current mode.  In particular this
single theorem is reused for modes `0` through `9`; it is not a mode-by-mode normalization. -/
theorem eval_hMode0Part0OuterSparseQ_eq_blocks (m : ℤ) (hm : 0 ≤ m) :
    evalZhuSparseQ (hMode0Part0OuterSparseQ m) =
      evalZhuSparseQ (sumQ [hMode0Part0OuterBlockSparseQ m 0,
        hMode0Part0OuterBlockSparseQ m 1,
        hMode0Part0OuterBlockSparseQ m 2]) := by
  have hfull : evalZhuSparseQ l3hExpectedQ ∈ gradingWN (rank LtwoBlock) 6 := by
    have h := ZhuStateDesc.eval_mem_gradingWN
      (by omega) (.l3h) (by simp [ZhuStateDesc.Valid])
    simpa only [ZhuStateDesc.eval, l3hSparseQ_eq_expected] using h
  have hblock0 := evalZhuSparseQ_l3hBlockSparseQ_mem_gradingWN 0 (by omega)
  have hblock1 := evalZhuSparseQ_l3hBlockSparseQ_mem_gradingWN 1 (by omega)
  have hblock2 := evalZhuSparseQ_l3hBlockSparseQ_mem_gradingWN 2 (by omega)
  have evalField (P : SparseRational.Poly ℕ) :
      evalZhuSparseQ (aFieldActSparseQ 0 m P) =
        AFieldTwo 0 m (evalZhuSparseQ P) := by
    unfold evalZhuSparseQ
    exact evalSparse_aFieldActSparseQ 0 m P
  unfold hMode0Part0OuterSparseQ hMode0Part0OuterBlockSparseQ
  rw [if_pos hm, evalZhuSparseQ_scaleQ, evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [evalZhuSparseQ_scaleQ, evalZhuSparseQ_scaleQ, evalZhuSparseQ_scaleQ]
  rw [evalField, evalField, evalField, evalField]
  rw [evalZhuSparseQ_aWordAct [0, 0] (1 - m) 6 l3hExpectedQ hfull,
    evalZhuSparseQ_aWordAct [0, 0] (1 - m) 6 (l3hBlockSparseQ 0) hblock0,
    evalZhuSparseQ_aWordAct [0, 0] (1 - m) 6 (l3hBlockSparseQ 1) hblock1,
    evalZhuSparseQ_aWordAct [0, 0] (1 - m) 6 (l3hBlockSparseQ 2) hblock2]
  rw [l3hExpectedQ_eq_sum_blocks, evalZhuSparseQ_sumQ]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [map_add, smul_add]

theorem hMode0Part0Outer0ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer0ExpectedQ = sumQ [hMode0Part0Outer0Block0ExpectedQ,
      hMode0Part0Outer0Block1ExpectedQ, hMode0Part0Outer0Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer0ExpectedQ, hMode0Part0Outer0Block0ExpectedQ,
    hMode0Part0Outer0Block1ExpectedQ, hMode0Part0Outer0Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer1ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer1ExpectedQ = sumQ [hMode0Part0Outer1Block0ExpectedQ,
      hMode0Part0Outer1Block1ExpectedQ, hMode0Part0Outer1Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer1ExpectedQ, hMode0Part0Outer1Block0ExpectedQ,
    hMode0Part0Outer1Block1ExpectedQ, hMode0Part0Outer1Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer2ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer2ExpectedQ = sumQ [hMode0Part0Outer2Block0ExpectedQ,
      hMode0Part0Outer2Block1ExpectedQ, hMode0Part0Outer2Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer2ExpectedQ, hMode0Part0Outer2Block0ExpectedQ,
    hMode0Part0Outer2Block1ExpectedQ, hMode0Part0Outer2Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem hMode0Part0Outer3ExpectedQ_eq_sum_blocks :
    hMode0Part0Outer3ExpectedQ = sumQ [hMode0Part0Outer3Block0ExpectedQ,
      hMode0Part0Outer3Block1ExpectedQ, hMode0Part0Outer3Block2ExpectedQ] := by
  norm_num [hMode0Part0Outer3ExpectedQ, hMode0Part0Outer3Block0ExpectedQ,
    hMode0Part0Outer3Block1ExpectedQ, hMode0Part0Outer3Block2ExpectedQ,
    sumQ, addQ, compareWord]

theorem eval_hMode0Part0Outer0_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 0) =
      evalZhuSparseQ hMode0Part0Outer0ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 0 (by omega),
    hMode0Part0Outer0Block0_eq, hMode0Part0Outer0Block1_eq,
    hMode0Part0Outer0Block2_eq, ← hMode0Part0Outer0ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer1_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 1) =
      evalZhuSparseQ hMode0Part0Outer1ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 1 (by omega),
    hMode0Part0Outer1Block0_eq, hMode0Part0Outer1Block1_eq,
    hMode0Part0Outer1Block2_eq, ← hMode0Part0Outer1ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer2_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 2) =
      evalZhuSparseQ hMode0Part0Outer2ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 2 (by omega),
    hMode0Part0Outer2Block0_eq, hMode0Part0Outer2Block1_eq,
    hMode0Part0Outer2Block2_eq, ← hMode0Part0Outer2ExpectedQ_eq_sum_blocks]

theorem eval_hMode0Part0Outer3_eq_expected :
    evalZhuSparseQ (hMode0Part0OuterSparseQ 3) =
      evalZhuSparseQ hMode0Part0Outer3ExpectedQ := by
  rw [eval_hMode0Part0OuterSparseQ_eq_blocks 3 (by omega),
    hMode0Part0Outer3Block0_eq, hMode0Part0Outer3Block1_eq,
    hMode0Part0Outer3Block2_eq, ← hMode0Part0Outer3ExpectedQ_eq_sum_blocks]

#print axioms eval_hMode0Part0OuterSparseQ_eq_blocks
#print axioms eval_hMode0Part0Outer0_eq_expected
#print axioms eval_hMode0Part0Outer1_eq_expected
#print axioms eval_hMode0Part0Outer2_eq_expected
#print axioms eval_hMode0Part0Outer3_eq_expected

end VOA.LatGen.WpTwoZhuSparseSemantics

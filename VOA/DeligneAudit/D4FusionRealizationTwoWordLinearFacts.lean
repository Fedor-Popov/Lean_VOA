/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoSparseLinear
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateSortedSound

/-! Logical and complex-linear consequences of every checked word step. -/
namespace VOA.DeligneAudit.D4Two.Certificate

noncomputable section

theorem word_checks (i : ℕ) (hi : i < 841) :
    wordMetaCheck i = true ∧ wordStepCheck i = true := by
  have h := List.all_eq_true.mp word_checks_all i
    (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)
  simpa only [Bool.and_eq_true] using h

theorem wordNode_range (i : ℕ) (hi : i < 841) :
    rangeCheck 841 (wordNode i).vector = true := by
  have h := (word_checks i hi).1
  simp only [wordMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem wordNode_level (i : ℕ) (hi : i < 841) : (wordNode i).level ≤ 4 := by
  have h := (word_checks i hi).1
  simp only [wordMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem wordNode_parent (i : ℕ) (hi : i < 841) (hi0 : i ≠ 0) :
    (wordNode i).parent < i ∧ (wordNode i).color < 28 ∧
      (wordNode i).level = (wordNode (wordNode i).parent).level + (wordNode i).mode ∧
      sortedZero ((wordNode i).vector ++ scale (-1)
        (applyColumns (pairColumn 28 (rawColumn (wordNode i).color)
          (wordNode i).color (wordNode i).mode) (wordNode (wordNode i).parent).vector)) = true := by
  have h := (word_checks i hi).2
  simp only [wordStepCheck, if_neg hi0, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  simpa only [and_assoc] using h

private theorem vec_eq_of_sortedDiff (n : ℕ) (v w : SV)
    (h : sortedZero (v ++ scale (-1) w) = true) : vec n v = vec n w := by
  apply sub_eq_zero.mp
  simpa only [vec_append, vec_scale, Int.cast_neg, Int.cast_one, neg_one_smul,
    sub_eq_add_neg] using vec_zero_of_sortedZero n h

/-- Every finite column step is an equality of genuine complex vectors. -/
theorem wordNode_vec_step (i : ℕ) (hi : i < 841) (hi0 : i ≠ 0) :
    vec 841 (wordNode i).vector =
      columnsEnd 841 (pairColumn 28 (rawColumn (wordNode i).color)
        (wordNode i).color (wordNode i).mode)
        (vec 841 (wordNode (wordNode i).parent).vector) := by
  obtain ⟨hp, _, _, hz⟩ := wordNode_parent i hi hi0
  rw [columnsEnd_vec _ _ _ (wordNode_range _ (hp.trans hi))]
  exact vec_eq_of_sortedDiff 841 _ _ hz

theorem wordNode_initial :
    vec 841 (wordNode 0).vector = Pi.single (⟨810, by decide⟩ : Fin 841) 1 := by
  change vec 841 [(810, 1)] = _
  exact DeligneSector.Sparse.vecC_single ⟨810, by decide⟩

end
end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.wordNode_vec_step

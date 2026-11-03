/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordLinearFacts

/-! Exact linear consequences of indexed action certificates. The case
family is generic here; the full dense range is checked separately. -/
namespace VOA.DeligneAudit.D4Two.Certificate

noncomputable section

def actionIndex (c k j : ℕ) : ℕ := (k * 28 + c) * 841 + j

theorem actionIndex_source (c k j : ℕ) (hj : j < 841) :
    actionSource (actionIndex c k j) = j := by
  simp only [actionSource, actionIndex]
  omega

theorem actionIndex_color (c k j : ℕ) (hc : c < 28) (hj : j < 841) :
    actionColor (actionIndex c k j) = c := by
  simp only [actionColor, actionIndex]
  omega

theorem actionIndex_mode (c k j : ℕ) (hc : c < 28) (hj : j < 841) :
    actionMode (actionIndex c k j) = k := by
  simp only [actionMode, actionIndex]
  omega

theorem actionIndex_lt (c k j : ℕ) (hc : c < 28) (hk : k < 4) (hj : j < 841) :
    actionIndex c k j < 94192 := by
  simp only [actionIndex]
  omega

theorem fullAction_parts (caseAt : ℕ → ActionCase) (i : ℕ)
    (h : fullActionCheck caseAt i = true) :
    (caseAt i).denominator ≠ 0 ∧
      ((caseAt i).terms.all fun p => decide (p.1 < 841) &&
        (if (wordNode (actionSource i)).level + actionMode i < 4 then
          decide ((wordNode p.1).level ≤ (wordNode (actionSource i)).level + actionMode i)
         else true)) = true ∧
      sortedZero (scale (caseAt i).denominator
        (applyColumns (pairColumn 28 (rawColumn (actionColor i))
          (actionColor i) (actionMode i)) (wordNode (actionSource i)).vector) ++
        scale (-1) (wordCombination (caseAt i).terms)) = true := by
  simpa only [fullActionCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem fullAction_target_bound (caseAt : ℕ → ActionCase) (i : ℕ)
    (h : fullActionCheck caseAt i = true) (p : ℕ × ℤ) (hp : p ∈ (caseAt i).terms) :
    p.1 < 841 := by
  have hh := List.all_eq_true.mp (fullAction_parts caseAt i h).2.1 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1

theorem fullAction_target_level (caseAt : ℕ → ActionCase) (i : ℕ)
    (h : fullActionCheck caseAt i = true)
    (hcritical : (wordNode (actionSource i)).level + actionMode i < 4)
    (p : ℕ × ℤ) (hp : p ∈ (caseAt i).terms) :
    (wordNode p.1).level ≤ (wordNode (actionSource i)).level + actionMode i := by
  have hh := List.all_eq_true.mp (fullAction_parts caseAt i h).2.1 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, if_pos hcritical] at hh
  exact hh.2

/-- Acceptance gives a genuine complex linear relation, with a nonzero
integer denominator. The actual source bridge is applied afterwards. -/
theorem fullAction_vector (caseAt : ℕ → ActionCase) (i : ℕ)
    (h : fullActionCheck caseAt i = true) :
    ((caseAt i).denominator : ℂ) •
      columnsEnd 841 (pairColumn 28 (rawColumn (actionColor i))
        (actionColor i) (actionMode i)) (vec 841 (wordNode (actionSource i)).vector) =
      ((caseAt i).terms.map fun p =>
        (p.2 : ℂ) • vec 841 (wordNode p.1).vector).sum := by
  have hs : actionSource i < 841 := Nat.mod_lt _ (by decide)
  rw [columnsEnd_vec _ _ _ (wordNode_range _ hs)]
  have he := vec_eq_of_sortedZero 841 (caseAt i).denominator _ _
    (fullAction_parts caseAt i h).2.2
  simpa only [wordCombination, vec_flatMap, vec_scale] using he

end
end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.fullAction_vector

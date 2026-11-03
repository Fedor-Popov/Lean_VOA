import VOA.DeligneAudit.D4FusionContactM2Count46
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem376Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem376Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem376_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([5, 6] ++ [v])) ↔ stem376Flags v = true := by
  decide +kernel

theorem stem376_count : (enumerateFrom leaders 2 6 [5, 6]).length = 18 := by
  calc
    _ = 1 + ((List.finRange 18).map stem376Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [5, 6] stem376Flags stem376Counts stem376_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem176_count
        · cases hv
        · exact stem177_count
        · cases hv
        · exact stem178_count
        · cases hv
        · exact stem179_count
        · cases hv
        · exact stem180_count
        · cases hv
        · exact stem181_count
        · exact stem182_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 18 := by decide +kernel

def stem377Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false].getD v.val false
def stem377Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem377_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([5, 7] ++ [v])) ↔ stem377Flags v = true := by
  decide +kernel

theorem stem377_count : (enumerateFrom leaders 2 7 [5, 7]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem377Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 7 [5, 7] stem377Flags stem377Counts stem377_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem183_count
        · cases hv
        · exact stem184_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem185_count
        · cases hv
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 8 := by decide +kernel

def stem378Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, true, true].getD v.val false
def stem378Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem378_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([5, 8] ++ [v])) ↔ stem378Flags v = true := by
  decide +kernel

theorem stem378_count : (enumerateFrom leaders 2 8 [5, 8]).length = 12 := by
  calc
    _ = 1 + ((List.finRange 18).map stem378Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [5, 8] stem378Flags stem378Counts stem378_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem186_count
        · exact stem187_count
        · exact stem188_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem189_count
        · exact stem190_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 12 := by decide +kernel

def stem379Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, true].getD v.val false
def stem379Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem379_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([5, 10] ++ [v])) ↔ stem379Flags v = true := by
  decide +kernel

theorem stem379_count : (enumerateFrom leaders 2 10 [5, 10]).length = 11 := by
  calc
    _ = 1 + ((List.finRange 18).map stem379Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [5, 10] stem379Flags stem379Counts stem379_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem191_count
        · cases hv
        · exact stem192_count
        · cases hv
        · exact stem193_count
        · cases hv
        · exact stem194_count
        · exact stem195_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 11 := by decide +kernel

def stem380Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem380Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem380_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([5, 11] ++ [v])) ↔ stem380Flags v = true := by
  decide +kernel

theorem stem380_count : (enumerateFrom leaders 2 11 [5, 11]).length = 5 := by
  calc
    _ = 1 + ((List.finRange 18).map stem380Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 11 [5, 11] stem380Flags stem380Counts stem380_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem196_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem197_count
        · cases hv
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 5 := by decide +kernel

def stem381Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem381Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem381_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([5, 12] ++ [v])) ↔ stem381Flags v = true := by
  decide +kernel

theorem stem381_count : (enumerateFrom leaders 2 12 [5, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem381Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [5, 12] stem381Flags stem381Counts stem381_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem198_count
        · exact stem199_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 4 := by decide +kernel

def stem382Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem382Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem382_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([5, 14] ++ [v])) ↔ stem382Flags v = true := by
  decide +kernel

theorem stem382_count : (enumerateFrom leaders 2 14 [5, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem382Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [5, 14] stem382Flags stem382Counts stem382_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem200_count
        · exact stem201_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 4 := by decide +kernel

def stem383Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem383Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem383_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([5, 16] ++ [v])) ↔ stem383Flags v = true := by
  decide +kernel

theorem stem383_count : (enumerateFrom leaders 2 16 [5, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem383Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [5, 16] stem383Flags stem383Counts stem383_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem202_count
        · exact stem203_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 4 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem383_count

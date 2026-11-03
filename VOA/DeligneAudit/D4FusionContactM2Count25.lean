import VOA.DeligneAudit.D4FusionContactM2Count24
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem200Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem200Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem200_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([5, 14, 16] ++ [v])) ↔ stem200Flags v = true := by
  decide +kernel

theorem stem200_count : (enumerateFrom leaders 1 16 [5, 14, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem200Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [5, 14, 16] stem200Flags stem200Counts stem200_flags
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
        · rfl
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
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 2 := by decide +kernel

def stem201Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem201Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem201_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([5, 14, 17] ++ [v])) ↔ stem201Flags v = true := by
  decide +kernel

theorem stem201_count : (enumerateFrom leaders 1 17 [5, 14, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem201Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [5, 14, 17] stem201Flags stem201Counts stem201_flags
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
        · cases hv
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
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
    _ = 1 := by decide +kernel

def stem202Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem202Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem202_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([5, 16, 16] ++ [v])) ↔ stem202Flags v = true := by
  decide +kernel

theorem stem202_count : (enumerateFrom leaders 1 16 [5, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem202Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [5, 16, 16] stem202Flags stem202Counts stem202_flags
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
        · rfl
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
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 2 := by decide +kernel

def stem203Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem203Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem203_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([5, 16, 17] ++ [v])) ↔ stem203Flags v = true := by
  decide +kernel

theorem stem203_count : (enumerateFrom leaders 1 17 [5, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem203Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [5, 16, 17] stem203Flags stem203Counts stem203_flags
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
        · cases hv
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
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
    _ = 1 := by decide +kernel

def stem204Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false].getD v.val false
def stem204Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem204_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([6, 6, 8] ++ [v])) ↔ stem204Flags v = true := by
  decide +kernel

theorem stem204_count : (enumerateFrom leaders 1 8 [6, 6, 8]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem204Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [6, 6, 8] stem204Flags stem204Counts stem204_flags
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
        · rfl
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · rfl
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
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 3 := by decide +kernel

def stem205Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem205Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem205_flags : ∀ v : Fin 18,
    (9 ≤ v.val ∧ Avoids leaders ([6, 6, 9] ++ [v])) ↔ stem205Flags v = true := by
  decide +kernel

theorem stem205_count : (enumerateFrom leaders 1 9 [6, 6, 9]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem205Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 9 [6, 6, 9] stem205Flags stem205Counts stem205_flags
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
        · rfl
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
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 2 := by decide +kernel

def stem206Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem206Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem206_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([6, 6, 16] ++ [v])) ↔ stem206Flags v = true := by
  decide +kernel

theorem stem206_count : (enumerateFrom leaders 1 16 [6, 6, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem206Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [6, 6, 16] stem206Flags stem206Counts stem206_flags
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
        · rfl
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
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 2 := by decide +kernel

def stem207Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem207Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem207_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([6, 6, 17] ++ [v])) ↔ stem207Flags v = true := by
  decide +kernel

theorem stem207_count : (enumerateFrom leaders 1 17 [6, 6, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem207Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [6, 6, 17] stem207Flags stem207Counts stem207_flags
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
        · cases hv
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
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
    _ = 1 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem207_count

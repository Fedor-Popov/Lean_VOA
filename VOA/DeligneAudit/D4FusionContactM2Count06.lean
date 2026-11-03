import VOA.DeligneAudit.D4FusionContactM2Count05
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem048Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem048Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem048_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([1, 14, 16] ++ [v])) ↔ stem048Flags v = true := by
  decide +kernel

theorem stem048_count : (enumerateFrom leaders 1 16 [1, 14, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem048Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [1, 14, 16] stem048Flags stem048Counts stem048_flags
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

def stem049Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem049Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem049_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([1, 14, 17] ++ [v])) ↔ stem049Flags v = true := by
  decide +kernel

theorem stem049_count : (enumerateFrom leaders 1 17 [1, 14, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem049Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [1, 14, 17] stem049Flags stem049Counts stem049_flags
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

def stem050Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem050Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem050_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([1, 16, 16] ++ [v])) ↔ stem050Flags v = true := by
  decide +kernel

theorem stem050_count : (enumerateFrom leaders 1 16 [1, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem050Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [1, 16, 16] stem050Flags stem050Counts stem050_flags
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

def stem051Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem051Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem051_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([1, 16, 17] ++ [v])) ↔ stem051Flags v = true := by
  decide +kernel

theorem stem051_count : (enumerateFrom leaders 1 17 [1, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem051Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [1, 16, 17] stem051Flags stem051Counts stem051_flags
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

def stem052Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem052Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem052_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([2, 2, 4] ++ [v])) ↔ stem052Flags v = true := by
  decide +kernel

theorem stem052_count : (enumerateFrom leaders 1 4 [2, 2, 4]).length = 5 := by
  calc
    _ = 1 + ((List.finRange 18).map stem052Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 4 [2, 2, 4] stem052Flags stem052Counts stem052_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · rfl
        · cases hv
        · rfl
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · rfl
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
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 5 := by decide +kernel

def stem053Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem053Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem053_flags : ∀ v : Fin 18,
    (5 ≤ v.val ∧ Avoids leaders ([2, 2, 5] ++ [v])) ↔ stem053Flags v = true := by
  decide +kernel

theorem stem053_count : (enumerateFrom leaders 1 5 [2, 2, 5]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem053Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 5 [2, 2, 5] stem053Flags stem053Counts stem053_flags
      · intro v hv
        fin_cases v
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
        · rfl
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
        · exact False.elim (hv rfl)
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
    _ = 4 := by decide +kernel

def stem054Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem054Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem054_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([2, 2, 6] ++ [v])) ↔ stem054Flags v = true := by
  decide +kernel

theorem stem054_count : (enumerateFrom leaders 1 6 [2, 2, 6]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem054Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [2, 2, 6] stem054Flags stem054Counts stem054_flags
      · intro v hv
        fin_cases v
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
        · rfl
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
        · exact False.elim (hv rfl)
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
    _ = 4 := by decide +kernel

def stem055Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem055Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem055_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([2, 2, 7] ++ [v])) ↔ stem055Flags v = true := by
  decide +kernel

theorem stem055_count : (enumerateFrom leaders 1 7 [2, 2, 7]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem055Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 7 [2, 2, 7] stem055Flags stem055Counts stem055_flags
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
        · rfl
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 3 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem055_count

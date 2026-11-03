import VOA.DeligneAudit.D4FusionContactM2Count06
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem056Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem056Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem056_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([2, 2, 12] ++ [v])) ↔ stem056Flags v = true := by
  decide +kernel

theorem stem056_count : (enumerateFrom leaders 1 12 [2, 2, 12]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem056Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 12 [2, 2, 12] stem056Flags stem056Counts stem056_flags
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

def stem057Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem057Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem057_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([2, 2, 13] ++ [v])) ↔ stem057Flags v = true := by
  decide +kernel

theorem stem057_count : (enumerateFrom leaders 1 13 [2, 2, 13]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem057Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 13 [2, 2, 13] stem057Flags stem057Counts stem057_flags
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

def stem058Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem058Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem058_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([2, 2, 16] ++ [v])) ↔ stem058Flags v = true := by
  decide +kernel

theorem stem058_count : (enumerateFrom leaders 1 16 [2, 2, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem058Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [2, 2, 16] stem058Flags stem058Counts stem058_flags
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

def stem059Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem059Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem059_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([2, 2, 17] ++ [v])) ↔ stem059Flags v = true := by
  decide +kernel

theorem stem059_count : (enumerateFrom leaders 1 17 [2, 2, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem059Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [2, 2, 17] stem059Flags stem059Counts stem059_flags
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

def stem060Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem060Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem060_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([2, 4, 4] ++ [v])) ↔ stem060Flags v = true := by
  decide +kernel

theorem stem060_count : (enumerateFrom leaders 1 4 [2, 4, 4]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem060Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 4 [2, 4, 4] stem060Flags stem060Counts stem060_flags
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
        · rfl
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
        · exact False.elim (hv rfl)
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
    _ = 4 := by decide +kernel

def stem061Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false].getD v.val false
def stem061Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem061_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([2, 4, 6] ++ [v])) ↔ stem061Flags v = true := by
  decide +kernel

theorem stem061_count : (enumerateFrom leaders 1 6 [2, 4, 6]).length = 7 := by
  calc
    _ = 1 + ((List.finRange 18).map stem061Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [2, 4, 6] stem061Flags stem061Counts stem061_flags
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
        · rfl
        · cases hv
        · rfl
        · cases hv
        · rfl
        · cases hv
        · rfl
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
    _ = 7 := by decide +kernel

def stem062Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem062Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem062_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([2, 4, 7] ++ [v])) ↔ stem062Flags v = true := by
  decide +kernel

theorem stem062_count : (enumerateFrom leaders 1 7 [2, 4, 7]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem062Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 7 [2, 4, 7] stem062Flags stem062Counts stem062_flags
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

def stem063Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem063Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem063_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([2, 4, 8] ++ [v])) ↔ stem063Flags v = true := by
  decide +kernel

theorem stem063_count : (enumerateFrom leaders 1 8 [2, 4, 8]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem063Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [2, 4, 8] stem063Flags stem063Counts stem063_flags
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
        · rfl
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 4 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem063_count

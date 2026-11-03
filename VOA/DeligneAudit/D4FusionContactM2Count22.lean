import VOA.DeligneAudit.D4FusionContactM2Count21
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem176Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false].getD v.val false
def stem176Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem176_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([5, 6, 6] ++ [v])) ↔ stem176Flags v = true := by
  decide +kernel

theorem stem176_count : (enumerateFrom leaders 1 6 [5, 6, 6]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem176Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [5, 6, 6] stem176Flags stem176Counts stem176_flags
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

def stem177Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem177Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem177_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([5, 6, 8] ++ [v])) ↔ stem177Flags v = true := by
  decide +kernel

theorem stem177_count : (enumerateFrom leaders 1 8 [5, 6, 8]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem177Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [5, 6, 8] stem177Flags stem177Counts stem177_flags
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

def stem178Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem178Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem178_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([5, 6, 10] ++ [v])) ↔ stem178Flags v = true := by
  decide +kernel

theorem stem178_count : (enumerateFrom leaders 1 10 [5, 6, 10]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem178Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 10 [5, 6, 10] stem178Flags stem178Counts stem178_flags
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

def stem179Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem179Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem179_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([5, 6, 12] ++ [v])) ↔ stem179Flags v = true := by
  decide +kernel

theorem stem179_count : (enumerateFrom leaders 1 12 [5, 6, 12]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem179Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 12 [5, 6, 12] stem179Flags stem179Counts stem179_flags
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

def stem180Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem180Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem180_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([5, 6, 14] ++ [v])) ↔ stem180Flags v = true := by
  decide +kernel

theorem stem180_count : (enumerateFrom leaders 1 14 [5, 6, 14]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem180Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 14 [5, 6, 14] stem180Flags stem180Counts stem180_flags
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

def stem181Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem181Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem181_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([5, 6, 16] ++ [v])) ↔ stem181Flags v = true := by
  decide +kernel

theorem stem181_count : (enumerateFrom leaders 1 16 [5, 6, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem181Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [5, 6, 16] stem181Flags stem181Counts stem181_flags
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

def stem182Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem182Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem182_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([5, 6, 17] ++ [v])) ↔ stem182Flags v = true := by
  decide +kernel

theorem stem182_count : (enumerateFrom leaders 1 17 [5, 6, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem182Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [5, 6, 17] stem182Flags stem182Counts stem182_flags
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

def stem183Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem183Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem183_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([5, 7, 8] ++ [v])) ↔ stem183Flags v = true := by
  decide +kernel

theorem stem183_count : (enumerateFrom leaders 1 8 [5, 7, 8]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem183Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [5, 7, 8] stem183Flags stem183Counts stem183_flags
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 3 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem183_count

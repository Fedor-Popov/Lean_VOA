import VOA.DeligneAudit.D4FusionContactM2Count11
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem096Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem096Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem096_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([2, 13, 16] ++ [v])) ↔ stem096Flags v = true := by
  decide +kernel

theorem stem096_count : (enumerateFrom leaders 1 16 [2, 13, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem096Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [2, 13, 16] stem096Flags stem096Counts stem096_flags
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

def stem097Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem097Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem097_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([2, 14, 16] ++ [v])) ↔ stem097Flags v = true := by
  decide +kernel

theorem stem097_count : (enumerateFrom leaders 1 16 [2, 14, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem097Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [2, 14, 16] stem097Flags stem097Counts stem097_flags
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

def stem098Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem098Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem098_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([2, 14, 17] ++ [v])) ↔ stem098Flags v = true := by
  decide +kernel

theorem stem098_count : (enumerateFrom leaders 1 17 [2, 14, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem098Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [2, 14, 17] stem098Flags stem098Counts stem098_flags
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

def stem099Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem099Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem099_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([2, 16, 16] ++ [v])) ↔ stem099Flags v = true := by
  decide +kernel

theorem stem099_count : (enumerateFrom leaders 1 16 [2, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem099Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [2, 16, 16] stem099Flags stem099Counts stem099_flags
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

def stem100Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem100Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem100_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([2, 16, 17] ++ [v])) ↔ stem100Flags v = true := by
  decide +kernel

theorem stem100_count : (enumerateFrom leaders 1 17 [2, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem100Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [2, 16, 17] stem100Flags stem100Counts stem100_flags
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

def stem101Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem101Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem101_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([3, 4, 4] ++ [v])) ↔ stem101Flags v = true := by
  decide +kernel

theorem stem101_count : (enumerateFrom leaders 1 4 [3, 4, 4]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem101Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 4 [3, 4, 4] stem101Flags stem101Counts stem101_flags
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

def stem102Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false].getD v.val false
def stem102Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem102_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([3, 4, 6] ++ [v])) ↔ stem102Flags v = true := by
  decide +kernel

theorem stem102_count : (enumerateFrom leaders 1 6 [3, 4, 6]).length = 7 := by
  calc
    _ = 1 + ((List.finRange 18).map stem102Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [3, 4, 6] stem102Flags stem102Counts stem102_flags
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

def stem103Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem103Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem103_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([3, 4, 7] ++ [v])) ↔ stem103Flags v = true := by
  decide +kernel

theorem stem103_count : (enumerateFrom leaders 1 7 [3, 4, 7]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem103Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 7 [3, 4, 7] stem103Flags stem103Counts stem103_flags
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

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem103_count

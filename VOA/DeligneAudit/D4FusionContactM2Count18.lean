import VOA.DeligneAudit.D4FusionContactM2Count17
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem144Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem144Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem144_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([4, 4, 10] ++ [v])) ↔ stem144Flags v = true := by
  decide +kernel

theorem stem144_count : (enumerateFrom leaders 1 10 [4, 4, 10]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem144Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 10 [4, 4, 10] stem144Flags stem144Counts stem144_flags
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

def stem145Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem145Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem145_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([4, 4, 11] ++ [v])) ↔ stem145Flags v = true := by
  decide +kernel

theorem stem145_count : (enumerateFrom leaders 1 11 [4, 4, 11]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem145Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 11 [4, 4, 11] stem145Flags stem145Counts stem145_flags
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

def stem146Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem146Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem146_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([4, 4, 16] ++ [v])) ↔ stem146Flags v = true := by
  decide +kernel

theorem stem146_count : (enumerateFrom leaders 1 16 [4, 4, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem146Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [4, 4, 16] stem146Flags stem146Counts stem146_flags
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

def stem147Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem147Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem147_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([4, 4, 17] ++ [v])) ↔ stem147Flags v = true := by
  decide +kernel

theorem stem147_count : (enumerateFrom leaders 1 17 [4, 4, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem147Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [4, 4, 17] stem147Flags stem147Counts stem147_flags
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

def stem148Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false].getD v.val false
def stem148Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem148_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([4, 6, 6] ++ [v])) ↔ stem148Flags v = true := by
  decide +kernel

theorem stem148_count : (enumerateFrom leaders 1 6 [4, 6, 6]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem148Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [4, 6, 6] stem148Flags stem148Counts stem148_flags
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

def stem149Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem149Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem149_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([4, 6, 8] ++ [v])) ↔ stem149Flags v = true := by
  decide +kernel

theorem stem149_count : (enumerateFrom leaders 1 8 [4, 6, 8]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem149Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [4, 6, 8] stem149Flags stem149Counts stem149_flags
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

def stem150Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem150Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem150_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([4, 6, 10] ++ [v])) ↔ stem150Flags v = true := by
  decide +kernel

theorem stem150_count : (enumerateFrom leaders 1 10 [4, 6, 10]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem150Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 10 [4, 6, 10] stem150Flags stem150Counts stem150_flags
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

def stem151Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem151Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem151_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([4, 6, 12] ++ [v])) ↔ stem151Flags v = true := by
  decide +kernel

theorem stem151_count : (enumerateFrom leaders 1 12 [4, 6, 12]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem151Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 12 [4, 6, 12] stem151Flags stem151Counts stem151_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem151_count

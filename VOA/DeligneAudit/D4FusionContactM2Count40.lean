import VOA.DeligneAudit.D4FusionContactM2Count39
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem320Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem320Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem320_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([15, 16, 16] ++ [v])) ↔ stem320Flags v = true := by
  decide +kernel

theorem stem320_count : (enumerateFrom leaders 1 16 [15, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem320Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [15, 16, 16] stem320Flags stem320Counts stem320_flags
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

def stem321Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem321Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem321_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([15, 16, 17] ++ [v])) ↔ stem321Flags v = true := by
  decide +kernel

theorem stem321_count : (enumerateFrom leaders 1 17 [15, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem321Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [15, 16, 17] stem321Flags stem321Counts stem321_flags
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

def stem322Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem322Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem322_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([16, 16, 16] ++ [v])) ↔ stem322Flags v = true := by
  decide +kernel

theorem stem322_count : (enumerateFrom leaders 1 16 [16, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem322Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [16, 16, 16] stem322Flags stem322Counts stem322_flags
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

def stem323Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem323Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem323_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([16, 16, 17] ++ [v])) ↔ stem323Flags v = true := by
  decide +kernel

theorem stem323_count : (enumerateFrom leaders 1 17 [16, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem323Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [16, 16, 17] stem323Flags stem323Counts stem323_flags
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

def stem324Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem324Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem324_flags : ∀ v : Fin 18,
    (0 ≤ v.val ∧ Avoids leaders ([0, 0] ++ [v])) ↔ stem324Flags v = true := by
  decide +kernel

theorem stem324_count : (enumerateFrom leaders 2 0 [0, 0]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem324Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 0 [0, 0] stem324Flags stem324Counts stem324_flags
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
        · exact stem000_count
        · exact stem001_count
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

def stem325Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem325Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem325_flags : ∀ v : Fin 18,
    (2 ≤ v.val ∧ Avoids leaders ([0, 2] ++ [v])) ↔ stem325Flags v = true := by
  decide +kernel

theorem stem325_count : (enumerateFrom leaders 2 2 [0, 2]).length = 10 := by
  calc
    _ = 1 + ((List.finRange 18).map stem325Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 2 [0, 2] stem325Flags stem325Counts stem325_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem002_count
        · cases hv
        · exact stem003_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem004_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem005_count
        · exact stem006_count
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
        · exact False.elim (hv rfl)
    _ = 10 := by decide +kernel

def stem326Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, true].getD v.val false
def stem326Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem326_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([0, 4] ++ [v])) ↔ stem326Flags v = true := by
  decide +kernel

theorem stem326_count : (enumerateFrom leaders 2 4 [0, 4]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem326Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 4 [0, 4] stem326Flags stem326Counts stem326_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem007_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem008_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem009_count
        · exact stem010_count
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
        · exact False.elim (hv rfl)
    _ = 8 := by decide +kernel

def stem327Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true].getD v.val false
def stem327Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem327_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([0, 6] ++ [v])) ↔ stem327Flags v = true := by
  decide +kernel

theorem stem327_count : (enumerateFrom leaders 2 6 [0, 6]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem327Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [0, 6] stem327Flags stem327Counts stem327_flags
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
        · exact stem011_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem012_count
        · exact stem013_count
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
        · exact False.elim (hv rfl)
    _ = 6 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem327_count

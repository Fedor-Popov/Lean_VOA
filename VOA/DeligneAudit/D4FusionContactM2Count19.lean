import VOA.DeligneAudit.D4FusionContactM2Count18
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem152Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem152Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem152_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([4, 6, 14] ++ [v])) ↔ stem152Flags v = true := by
  decide +kernel

theorem stem152_count : (enumerateFrom leaders 1 14 [4, 6, 14]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem152Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 14 [4, 6, 14] stem152Flags stem152Counts stem152_flags
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

def stem153Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem153Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem153_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([4, 6, 16] ++ [v])) ↔ stem153Flags v = true := by
  decide +kernel

theorem stem153_count : (enumerateFrom leaders 1 16 [4, 6, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem153Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [4, 6, 16] stem153Flags stem153Counts stem153_flags
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

def stem154Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem154Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem154_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([4, 6, 17] ++ [v])) ↔ stem154Flags v = true := by
  decide +kernel

theorem stem154_count : (enumerateFrom leaders 1 17 [4, 6, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem154Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [4, 6, 17] stem154Flags stem154Counts stem154_flags
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

def stem155Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem155Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem155_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([4, 7, 8] ++ [v])) ↔ stem155Flags v = true := by
  decide +kernel

theorem stem155_count : (enumerateFrom leaders 1 8 [4, 7, 8]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem155Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 8 [4, 7, 8] stem155Flags stem155Counts stem155_flags
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

def stem156Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem156Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem156_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([4, 7, 10] ++ [v])) ↔ stem156Flags v = true := by
  decide +kernel

theorem stem156_count : (enumerateFrom leaders 1 10 [4, 7, 10]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem156Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 10 [4, 7, 10] stem156Flags stem156Counts stem156_flags
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

def stem157Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem157Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem157_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([4, 7, 16] ++ [v])) ↔ stem157Flags v = true := by
  decide +kernel

theorem stem157_count : (enumerateFrom leaders 1 16 [4, 7, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem157Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [4, 7, 16] stem157Flags stem157Counts stem157_flags
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

def stem158Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem158Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem158_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([4, 8, 10] ++ [v])) ↔ stem158Flags v = true := by
  decide +kernel

theorem stem158_count : (enumerateFrom leaders 1 10 [4, 8, 10]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem158Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 10 [4, 8, 10] stem158Flags stem158Counts stem158_flags
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

def stem159Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem159Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem159_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([4, 8, 11] ++ [v])) ↔ stem159Flags v = true := by
  decide +kernel

theorem stem159_count : (enumerateFrom leaders 1 11 [4, 8, 11]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem159Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 11 [4, 8, 11] stem159Flags stem159Counts stem159_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem159_count

import VOA.DeligneAudit.D4FusionContactM2Count16
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem136Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem136Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem136_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([3, 12, 17] ++ [v])) ↔ stem136Flags v = true := by
  decide +kernel

theorem stem136_count : (enumerateFrom leaders 1 17 [3, 12, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem136Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [3, 12, 17] stem136Flags stem136Counts stem136_flags
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

def stem137Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem137Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem137_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([3, 13, 16] ++ [v])) ↔ stem137Flags v = true := by
  decide +kernel

theorem stem137_count : (enumerateFrom leaders 1 16 [3, 13, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem137Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [3, 13, 16] stem137Flags stem137Counts stem137_flags
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

def stem138Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem138Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem138_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([3, 14, 16] ++ [v])) ↔ stem138Flags v = true := by
  decide +kernel

theorem stem138_count : (enumerateFrom leaders 1 16 [3, 14, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem138Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [3, 14, 16] stem138Flags stem138Counts stem138_flags
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

def stem139Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem139Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem139_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([3, 14, 17] ++ [v])) ↔ stem139Flags v = true := by
  decide +kernel

theorem stem139_count : (enumerateFrom leaders 1 17 [3, 14, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem139Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [3, 14, 17] stem139Flags stem139Counts stem139_flags
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

def stem140Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem140Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem140_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([3, 16, 16] ++ [v])) ↔ stem140Flags v = true := by
  decide +kernel

theorem stem140_count : (enumerateFrom leaders 1 16 [3, 16, 16]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem140Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 16 [3, 16, 16] stem140Flags stem140Counts stem140_flags
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

def stem141Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem141Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem141_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([3, 16, 17] ++ [v])) ↔ stem141Flags v = true := by
  decide +kernel

theorem stem141_count : (enumerateFrom leaders 1 17 [3, 16, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem141Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 17 [3, 16, 17] stem141Flags stem141Counts stem141_flags
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

def stem142Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem142Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem142_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([4, 4, 6] ++ [v])) ↔ stem142Flags v = true := by
  decide +kernel

theorem stem142_count : (enumerateFrom leaders 1 6 [4, 4, 6]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem142Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 6 [4, 4, 6] stem142Flags stem142Counts stem142_flags
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

def stem143Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false].getD v.val false
def stem143Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem143_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([4, 4, 7] ++ [v])) ↔ stem143Flags v = true := by
  decide +kernel

theorem stem143_count : (enumerateFrom leaders 1 7 [4, 4, 7]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem143Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 0 7 [4, 4, 7] stem143Flags stem143Counts stem143_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem143_count

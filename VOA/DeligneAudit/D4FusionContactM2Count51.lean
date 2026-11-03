import VOA.DeligneAudit.D4FusionContactM2Count50
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem408Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, true, true].getD v.val false
def stem408Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem408_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([9, 10] ++ [v])) ↔ stem408Flags v = true := by
  decide +kernel

theorem stem408_count : (enumerateFrom leaders 2 10 [9, 10]).length = 14 := by
  calc
    _ = 1 + ((List.finRange 18).map stem408Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [9, 10] stem408Flags stem408Counts stem408_flags
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
        · exact stem267_count
        · cases hv
        · exact stem268_count
        · exact stem269_count
        · exact stem270_count
        · cases hv
        · exact stem271_count
        · exact stem272_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 14 := by decide +kernel

def stem409Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem409Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem409_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([9, 11] ++ [v])) ↔ stem409Flags v = true := by
  decide +kernel

theorem stem409_count : (enumerateFrom leaders 2 11 [9, 11]).length = 5 := by
  calc
    _ = 1 + ((List.finRange 18).map stem409Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 11 [9, 11] stem409Flags stem409Counts stem409_flags
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
        · exact stem273_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem274_count
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

def stem410Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem410Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem410_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([9, 12] ++ [v])) ↔ stem410Flags v = true := by
  decide +kernel

theorem stem410_count : (enumerateFrom leaders 2 12 [9, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem410Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [9, 12] stem410Flags stem410Counts stem410_flags
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
        · exact stem275_count
        · cases hv
        · exact stem276_count
        · cases hv
        · exact stem277_count
        · exact stem278_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 8 := by decide +kernel

def stem411Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem411Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem411_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([9, 13] ++ [v])) ↔ stem411Flags v = true := by
  decide +kernel

theorem stem411_count : (enumerateFrom leaders 2 13 [9, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem411Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [9, 13] stem411Flags stem411Counts stem411_flags
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
        · exact stem279_count
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
    _ = 3 := by decide +kernel

def stem412Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem412Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem412_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([9, 14] ++ [v])) ↔ stem412Flags v = true := by
  decide +kernel

theorem stem412_count : (enumerateFrom leaders 2 14 [9, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem412Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [9, 14] stem412Flags stem412Counts stem412_flags
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
        · exact stem280_count
        · exact stem281_count
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

def stem413Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem413Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem413_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([9, 16] ++ [v])) ↔ stem413Flags v = true := by
  decide +kernel

theorem stem413_count : (enumerateFrom leaders 2 16 [9, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem413Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [9, 16] stem413Flags stem413Counts stem413_flags
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
        · exact stem282_count
        · exact stem283_count
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

def stem414Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem414Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem414_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([9, 17] ++ [v])) ↔ stem414Flags v = true := by
  decide +kernel

theorem stem414_count : (enumerateFrom leaders 2 17 [9, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem414Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [9, 17] stem414Flags stem414Counts stem414_flags
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

def stem415Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, true].getD v.val false
def stem415Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem415_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([10, 10] ++ [v])) ↔ stem415Flags v = true := by
  decide +kernel

theorem stem415_count : (enumerateFrom leaders 2 10 [10, 10]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem415Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [10, 10] stem415Flags stem415Counts stem415_flags
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
        · exact stem284_count
        · exact stem285_count
        · cases hv
        · cases hv
        · exact stem286_count
        · exact stem287_count
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 9 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem415_count

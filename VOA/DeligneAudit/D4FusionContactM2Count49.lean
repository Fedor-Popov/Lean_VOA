import VOA.DeligneAudit.D4FusionContactM2Count48
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem392Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem392Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem392_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([6, 17] ++ [v])) ↔ stem392Flags v = true := by
  decide +kernel

theorem stem392_count : (enumerateFrom leaders 2 17 [6, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem392Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [6, 17] stem392Flags stem392Counts stem392_flags
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

def stem393Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem393Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem393_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([7, 8] ++ [v])) ↔ stem393Flags v = true := by
  decide +kernel

theorem stem393_count : (enumerateFrom leaders 2 8 [7, 8]).length = 15 := by
  calc
    _ = 1 + ((List.finRange 18).map stem393Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [7, 8] stem393Flags stem393Counts stem393_flags
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
        · exact stem226_count
        · cases hv
        · exact stem227_count
        · cases hv
        · exact stem228_count
        · cases hv
        · exact stem229_count
        · cases hv
        · exact stem230_count
        · exact stem231_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 15 := by decide +kernel

def stem394Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem394Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem394_flags : ∀ v : Fin 18,
    (9 ≤ v.val ∧ Avoids leaders ([7, 9] ++ [v])) ↔ stem394Flags v = true := by
  decide +kernel

theorem stem394_count : (enumerateFrom leaders 2 9 [7, 9]).length = 7 := by
  calc
    _ = 1 + ((List.finRange 18).map stem394Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 9 [7, 9] stem394Flags stem394Counts stem394_flags
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
        · exact stem232_count
        · cases hv
        · exact stem233_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem234_count
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
    _ = 7 := by decide +kernel

def stem395Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem395Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem395_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([7, 10] ++ [v])) ↔ stem395Flags v = true := by
  decide +kernel

theorem stem395_count : (enumerateFrom leaders 2 10 [7, 10]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem395Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [7, 10] stem395Flags stem395Counts stem395_flags
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
        · exact stem235_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem236_count
        · exact stem237_count
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
        · exact False.elim (hv rfl)
    _ = 6 := by decide +kernel

def stem396Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem396Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem396_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([7, 12] ++ [v])) ↔ stem396Flags v = true := by
  decide +kernel

theorem stem396_count : (enumerateFrom leaders 2 12 [7, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem396Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [7, 12] stem396Flags stem396Counts stem396_flags
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
        · exact stem238_count
        · exact stem239_count
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

def stem397Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem397Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem397_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([7, 14] ++ [v])) ↔ stem397Flags v = true := by
  decide +kernel

theorem stem397_count : (enumerateFrom leaders 2 14 [7, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem397Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [7, 14] stem397Flags stem397Counts stem397_flags
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
        · exact stem240_count
        · exact stem241_count
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

def stem398Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem398Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem398_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([7, 16] ++ [v])) ↔ stem398Flags v = true := by
  decide +kernel

theorem stem398_count : (enumerateFrom leaders 2 16 [7, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem398Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [7, 16] stem398Flags stem398Counts stem398_flags
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
        · exact stem242_count
        · exact stem243_count
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

def stem399Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem399Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem399_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([7, 17] ++ [v])) ↔ stem399Flags v = true := by
  decide +kernel

theorem stem399_count : (enumerateFrom leaders 2 17 [7, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem399Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [7, 17] stem399Flags stem399Counts stem399_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem399_count

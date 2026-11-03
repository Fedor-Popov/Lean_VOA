import VOA.DeligneAudit.D4FusionContactM2Count41
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem336Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true].getD v.val false
def stem336Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem336_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([1, 6] ++ [v])) ↔ stem336Flags v = true := by
  decide +kernel

theorem stem336_count : (enumerateFrom leaders 2 6 [1, 6]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem336Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [1, 6] stem336Flags stem336Counts stem336_flags
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
        · exact stem036_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem037_count
        · exact stem038_count
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

def stem337Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, true].getD v.val false
def stem337Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem337_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([1, 8] ++ [v])) ↔ stem337Flags v = true := by
  decide +kernel

theorem stem337_count : (enumerateFrom leaders 2 8 [1, 8]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem337Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [1, 8] stem337Flags stem337Counts stem337_flags
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
        · exact stem039_count
        · cases hv
        · exact stem040_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem041_count
        · exact stem042_count
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
        · exact False.elim (hv rfl)
    _ = 8 := by decide +kernel

def stem338Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem338Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem338_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([1, 10] ++ [v])) ↔ stem338Flags v = true := by
  decide +kernel

theorem stem338_count : (enumerateFrom leaders 2 10 [1, 10]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem338Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [1, 10] stem338Flags stem338Counts stem338_flags
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
        · exact stem043_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem044_count
        · exact stem045_count
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

def stem339Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem339Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem339_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([1, 12] ++ [v])) ↔ stem339Flags v = true := by
  decide +kernel

theorem stem339_count : (enumerateFrom leaders 2 12 [1, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem339Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [1, 12] stem339Flags stem339Counts stem339_flags
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
        · exact stem046_count
        · exact stem047_count
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

def stem340Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem340Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem340_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([1, 14] ++ [v])) ↔ stem340Flags v = true := by
  decide +kernel

theorem stem340_count : (enumerateFrom leaders 2 14 [1, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem340Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [1, 14] stem340Flags stem340Counts stem340_flags
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
        · exact stem048_count
        · exact stem049_count
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

def stem341Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem341Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem341_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([1, 16] ++ [v])) ↔ stem341Flags v = true := by
  decide +kernel

theorem stem341_count : (enumerateFrom leaders 2 16 [1, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem341Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [1, 16] stem341Flags stem341Counts stem341_flags
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
        · exact stem050_count
        · exact stem051_count
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

def stem342Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem342Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem342_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([1, 17] ++ [v])) ↔ stem342Flags v = true := by
  decide +kernel

theorem stem342_count : (enumerateFrom leaders 2 17 [1, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem342Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [1, 17] stem342Flags stem342Counts stem342_flags
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

def stem343Flags (v : Fin 18) : Bool := [false, false, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true].getD v.val false
def stem343Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 5, 4, 4, 3, 0, 0, 0, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem343_flags : ∀ v : Fin 18,
    (2 ≤ v.val ∧ Avoids leaders ([2, 2] ++ [v])) ↔ stem343Flags v = true := by
  decide +kernel

theorem stem343_count : (enumerateFrom leaders 2 2 [2, 2]).length = 25 := by
  calc
    _ = 1 + ((List.finRange 18).map stem343Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 2 [2, 2] stem343Flags stem343Counts stem343_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem052_count
        · exact stem053_count
        · exact stem054_count
        · exact stem055_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem056_count
        · exact stem057_count
        · cases hv
        · cases hv
        · exact stem058_count
        · exact stem059_count
      · intro v hv
        fin_cases v
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
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
    _ = 25 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem343_count

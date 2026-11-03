import VOA.DeligneAudit.D4FusionContactM2Count55
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem448Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, true, true].getD v.val false
def stem448Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 15, 7, 6, 0, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem448_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([7] ++ [v])) ↔ stem448Flags v = true := by
  decide +kernel

theorem stem448_count : (enumerateFrom leaders 3 7 [7]).length = 42 := by
  calc
    _ = 1 + ((List.finRange 18).map stem448Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 7 [7] stem448Flags stem448Counts stem448_flags
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
        · exact stem393_count
        · exact stem394_count
        · exact stem395_count
        · cases hv
        · exact stem396_count
        · cases hv
        · exact stem397_count
        · cases hv
        · exact stem398_count
        · exact stem399_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 42 := by decide +kernel

def stem449Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, true, true, true, true, true, false, true, true].getD v.val false
def stem449Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 14, 5, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem449_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([8] ++ [v])) ↔ stem449Flags v = true := by
  decide +kernel

theorem stem449_count : (enumerateFrom leaders 3 8 [8]).length = 56 := by
  calc
    _ = 1 + ((List.finRange 18).map stem449Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 8 [8] stem449Flags stem449Counts stem449_flags
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
        · exact stem400_count
        · cases hv
        · exact stem401_count
        · exact stem402_count
        · exact stem403_count
        · exact stem404_count
        · exact stem405_count
        · cases hv
        · exact stem406_count
        · exact stem407_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 56 := by decide +kernel

def stem450Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, true].getD v.val false
def stem450Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 5, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem450_flags : ∀ v : Fin 18,
    (9 ≤ v.val ∧ Avoids leaders ([9] ++ [v])) ↔ stem450Flags v = true := by
  decide +kernel

theorem stem450_count : (enumerateFrom leaders 3 9 [9]).length = 40 := by
  calc
    _ = 1 + ((List.finRange 18).map stem450Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 9 [9] stem450Flags stem450Counts stem450_flags
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
        · exact stem408_count
        · exact stem409_count
        · exact stem410_count
        · exact stem411_count
        · exact stem412_count
        · cases hv
        · exact stem413_count
        · exact stem414_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 40 := by decide +kernel

def stem451Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, true, true].getD v.val false
def stem451Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem451_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([10] ++ [v])) ↔ stem451Flags v = true := by
  decide +kernel

theorem stem451_count : (enumerateFrom leaders 3 10 [10]).length = 30 := by
  calc
    _ = 1 + ((List.finRange 18).map stem451Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 10 [10] stem451Flags stem451Counts stem451_flags
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
        · exact stem415_count
        · cases hv
        · exact stem416_count
        · exact stem417_count
        · exact stem418_count
        · cases hv
        · exact stem419_count
        · exact stem420_count
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
    _ = 30 := by decide +kernel

def stem452Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true].getD v.val false
def stem452Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem452_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([11] ++ [v])) ↔ stem452Flags v = true := by
  decide +kernel

theorem stem452_count : (enumerateFrom leaders 3 11 [11]).length = 21 := by
  calc
    _ = 1 + ((List.finRange 18).map stem452Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 11 [11] stem452Flags stem452Counts stem452_flags
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
        · exact stem421_count
        · exact stem422_count
        · exact stem423_count
        · cases hv
        · exact stem424_count
        · exact stem425_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 21 := by decide +kernel

def stem453Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem453Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem453_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([12] ++ [v])) ↔ stem453Flags v = true := by
  decide +kernel

theorem stem453_count : (enumerateFrom leaders 3 12 [12]).length = 14 := by
  calc
    _ = 1 + ((List.finRange 18).map stem453Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 12 [12] stem453Flags stem453Counts stem453_flags
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
        · exact stem426_count
        · cases hv
        · exact stem427_count
        · cases hv
        · exact stem428_count
        · exact stem429_count
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
    _ = 14 := by decide +kernel

def stem454Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true].getD v.val false
def stem454Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem454_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([13] ++ [v])) ↔ stem454Flags v = true := by
  decide +kernel

theorem stem454_count : (enumerateFrom leaders 3 13 [13]).length = 10 := by
  calc
    _ = 1 + ((List.finRange 18).map stem454Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 13 [13] stem454Flags stem454Counts stem454_flags
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
        · exact stem430_count
        · cases hv
        · exact stem431_count
        · exact stem432_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 10 := by decide +kernel

def stem455Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true].getD v.val false
def stem455Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem455_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([14] ++ [v])) ↔ stem455Flags v = true := by
  decide +kernel

theorem stem455_count : (enumerateFrom leaders 3 14 [14]).length = 10 := by
  calc
    _ = 1 + ((List.finRange 18).map stem455Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 14 [14] stem455Flags stem455Counts stem455_flags
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
        · exact stem433_count
        · cases hv
        · exact stem434_count
        · exact stem435_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 10 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem455_count

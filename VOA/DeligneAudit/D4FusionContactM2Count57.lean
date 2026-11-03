import VOA.DeligneAudit.D4FusionContactM2Count56
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem456Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem456Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem456_flags : ∀ v : Fin 18,
    (15 ≤ v.val ∧ Avoids leaders ([15] ++ [v])) ↔ stem456Flags v = true := by
  decide +kernel

theorem stem456_count : (enumerateFrom leaders 3 15 [15]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem456Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 15 [15] stem456Flags stem456Counts stem456_flags
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
        · exact stem436_count
        · exact stem437_count
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
    _ = 6 := by decide +kernel

def stem457Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem457Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem457_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([16] ++ [v])) ↔ stem457Flags v = true := by
  decide +kernel

theorem stem457_count : (enumerateFrom leaders 3 16 [16]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem457Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 16 [16] stem457Flags stem457Counts stem457_flags
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
        · exact stem438_count
        · exact stem439_count
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
    _ = 6 := by decide +kernel

def stem458Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true].getD v.val false
def stem458Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem458_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([17] ++ [v])) ↔ stem458Flags v = true := by
  decide +kernel

theorem stem458_count : (enumerateFrom leaders 3 17 [17]).length = 2 := by
  calc
    _ = 1 + ((List.finRange 18).map stem458Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 17 [17] stem458Flags stem458Counts stem458_flags
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
        · exact stem440_count
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
        · exact False.elim (hv rfl)
    _ = 2 := by decide +kernel

def stem459Flags (v : Fin 18) : Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true].getD v.val false
def stem459Counts (v : Fin 18) : ℕ := [56, 52, 130, 105, 84, 68, 51, 42, 56, 40, 30, 21, 14, 10, 10, 6, 6, 2].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem459_flags : ∀ v : Fin 18,
    (0 ≤ v.val ∧ Avoids leaders ([] ++ [v])) ↔ stem459Flags v = true := by
  decide +kernel

theorem stem459_count : (enumerateFrom leaders 4 0 []).length = 784 := by
  calc
    _ = 1 + ((List.finRange 18).map stem459Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 3 0 [] stem459Flags stem459Counts stem459_flags
      · intro v hv
        fin_cases v
        · exact stem441_count
        · exact stem442_count
        · exact stem443_count
        · exact stem444_count
        · exact stem445_count
        · exact stem446_count
        · exact stem447_count
        · exact stem448_count
        · exact stem449_count
        · exact stem450_count
        · exact stem451_count
        · exact stem452_count
        · exact stem453_count
        · exact stem454_count
        · exact stem455_count
        · exact stem456_count
        · exact stem457_count
        · exact stem458_count
      · intro v hv
        fin_cases v
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 784 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem459_count

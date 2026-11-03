import VOA.DeligneAudit.D4FusionContactM2Count43
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem352Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem352Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem352_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([2, 14] ++ [v])) ↔ stem352Flags v = true := by
  decide +kernel

theorem stem352_count : (enumerateFrom leaders 2 14 [2, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem352Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [2, 14] stem352Flags stem352Counts stem352_flags
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
        · exact stem097_count
        · exact stem098_count
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

def stem353Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem353Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem353_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([2, 16] ++ [v])) ↔ stem353Flags v = true := by
  decide +kernel

theorem stem353_count : (enumerateFrom leaders 2 16 [2, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem353Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [2, 16] stem353Flags stem353Counts stem353_flags
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
        · exact stem099_count
        · exact stem100_count
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

def stem354Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem354Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem354_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([2, 17] ++ [v])) ↔ stem354Flags v = true := by
  decide +kernel

theorem stem354_count : (enumerateFrom leaders 2 17 [2, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem354Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [2, 17] stem354Flags stem354Counts stem354_flags
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

def stem355Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem355Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 4, 0, 7, 2, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem355_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([3, 4] ++ [v])) ↔ stem355Flags v = true := by
  decide +kernel

theorem stem355_count : (enumerateFrom leaders 2 4 [3, 4]).length = 28 := by
  calc
    _ = 1 + ((List.finRange 18).map stem355Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 4 [3, 4] stem355Flags stem355Counts stem355_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem101_count
        · cases hv
        · exact stem102_count
        · exact stem103_count
        · exact stem104_count
        · cases hv
        · exact stem105_count
        · cases hv
        · exact stem106_count
        · cases hv
        · exact stem107_count
        · cases hv
        · exact stem108_count
        · exact stem109_count
      · intro v hv
        fin_cases v
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
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 28 := by decide +kernel

def stem356Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem356Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem356_flags : ∀ v : Fin 18,
    (5 ≤ v.val ∧ Avoids leaders ([3, 5] ++ [v])) ↔ stem356Flags v = true := by
  decide +kernel

theorem stem356_count : (enumerateFrom leaders 2 5 [3, 5]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem356Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 5 [3, 5] stem356Flags stem356Counts stem356_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem110_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem111_count
        · cases hv
        · exact stem112_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem113_count
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 9 := by decide +kernel

def stem357Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem357Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem357_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([3, 6] ++ [v])) ↔ stem357Flags v = true := by
  decide +kernel

theorem stem357_count : (enumerateFrom leaders 2 6 [3, 6]).length = 18 := by
  calc
    _ = 1 + ((List.finRange 18).map stem357Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [3, 6] stem357Flags stem357Counts stem357_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem114_count
        · cases hv
        · exact stem115_count
        · cases hv
        · exact stem116_count
        · cases hv
        · exact stem117_count
        · cases hv
        · exact stem118_count
        · cases hv
        · exact stem119_count
        · exact stem120_count
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
        · exact False.elim (hv rfl)
    _ = 18 := by decide +kernel

def stem358Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false].getD v.val false
def stem358Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem358_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([3, 7] ++ [v])) ↔ stem358Flags v = true := by
  decide +kernel

theorem stem358_count : (enumerateFrom leaders 2 7 [3, 7]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem358Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 7 [3, 7] stem358Flags stem358Counts stem358_flags
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
        · exact stem121_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem122_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem123_count
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 8 := by decide +kernel

def stem359Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, true, true].getD v.val false
def stem359Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem359_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([3, 8] ++ [v])) ↔ stem359Flags v = true := by
  decide +kernel

theorem stem359_count : (enumerateFrom leaders 2 8 [3, 8]).length = 12 := by
  calc
    _ = 1 + ((List.finRange 18).map stem359Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [3, 8] stem359Flags stem359Counts stem359_flags
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
        · exact stem124_count
        · cases hv
        · exact stem125_count
        · exact stem126_count
        · cases hv
        · cases hv
        · exact stem127_count
        · exact stem128_count
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
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 12 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem359_count

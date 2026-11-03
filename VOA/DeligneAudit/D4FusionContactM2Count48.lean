import VOA.DeligneAudit.D4FusionContactM2Count47
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem384Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem384Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem384_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([5, 17] ++ [v])) ↔ stem384Flags v = true := by
  decide +kernel

theorem stem384_count : (enumerateFrom leaders 2 17 [5, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem384Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [5, 17] stem384Flags stem384Counts stem384_flags
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

def stem385Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true].getD v.val false
def stem385Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem385_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([6, 6] ++ [v])) ↔ stem385Flags v = true := by
  decide +kernel

theorem stem385_count : (enumerateFrom leaders 2 6 [6, 6]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem385Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [6, 6] stem385Flags stem385Counts stem385_flags
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
        · exact stem204_count
        · exact stem205_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem206_count
        · exact stem207_count
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
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 9 := by decide +kernel

def stem386Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem386Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem386_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([6, 8] ++ [v])) ↔ stem386Flags v = true := by
  decide +kernel

theorem stem386_count : (enumerateFrom leaders 2 8 [6, 8]).length = 15 := by
  calc
    _ = 1 + ((List.finRange 18).map stem386Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [6, 8] stem386Flags stem386Counts stem386_flags
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
        · exact stem208_count
        · cases hv
        · exact stem209_count
        · cases hv
        · exact stem210_count
        · cases hv
        · exact stem211_count
        · cases hv
        · exact stem212_count
        · exact stem213_count
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

def stem387Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem387Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem387_flags : ∀ v : Fin 18,
    (9 ≤ v.val ∧ Avoids leaders ([6, 9] ++ [v])) ↔ stem387Flags v = true := by
  decide +kernel

theorem stem387_count : (enumerateFrom leaders 2 9 [6, 9]).length = 7 := by
  calc
    _ = 1 + ((List.finRange 18).map stem387Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 9 [6, 9] stem387Flags stem387Counts stem387_flags
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
        · exact stem214_count
        · cases hv
        · exact stem215_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem216_count
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

def stem388Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem388Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem388_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([6, 10] ++ [v])) ↔ stem388Flags v = true := by
  decide +kernel

theorem stem388_count : (enumerateFrom leaders 2 10 [6, 10]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem388Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [6, 10] stem388Flags stem388Counts stem388_flags
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
        · exact stem217_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem218_count
        · exact stem219_count
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

def stem389Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem389Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem389_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([6, 12] ++ [v])) ↔ stem389Flags v = true := by
  decide +kernel

theorem stem389_count : (enumerateFrom leaders 2 12 [6, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem389Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [6, 12] stem389Flags stem389Counts stem389_flags
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
        · exact stem220_count
        · exact stem221_count
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

def stem390Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem390Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem390_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([6, 14] ++ [v])) ↔ stem390Flags v = true := by
  decide +kernel

theorem stem390_count : (enumerateFrom leaders 2 14 [6, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem390Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [6, 14] stem390Flags stem390Counts stem390_flags
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
        · exact stem222_count
        · exact stem223_count
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

def stem391Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem391Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem391_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([6, 16] ++ [v])) ↔ stem391Flags v = true := by
  decide +kernel

theorem stem391_count : (enumerateFrom leaders 2 16 [6, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem391Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [6, 16] stem391Flags stem391Counts stem391_flags
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
        · exact stem224_count
        · exact stem225_count
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

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem391_count

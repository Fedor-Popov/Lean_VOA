import VOA.DeligneAudit.D4FusionContactM2Count44
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem360Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, true].getD v.val false
def stem360Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem360_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([3, 10] ++ [v])) ↔ stem360Flags v = true := by
  decide +kernel

theorem stem360_count : (enumerateFrom leaders 2 10 [3, 10]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem360Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [3, 10] stem360Flags stem360Counts stem360_flags
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
        · exact stem129_count
        · exact stem130_count
        · cases hv
        · cases hv
        · exact stem131_count
        · exact stem132_count
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

def stem361Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem361Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem361_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([3, 12] ++ [v])) ↔ stem361Flags v = true := by
  decide +kernel

theorem stem361_count : (enumerateFrom leaders 2 12 [3, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem361Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [3, 12] stem361Flags stem361Counts stem361_flags
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
        · exact stem133_count
        · cases hv
        · exact stem134_count
        · cases hv
        · exact stem135_count
        · exact stem136_count
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

def stem362Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem362Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem362_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([3, 13] ++ [v])) ↔ stem362Flags v = true := by
  decide +kernel

theorem stem362_count : (enumerateFrom leaders 2 13 [3, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem362Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [3, 13] stem362Flags stem362Counts stem362_flags
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
        · exact stem137_count
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

def stem363Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem363Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem363_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([3, 14] ++ [v])) ↔ stem363Flags v = true := by
  decide +kernel

theorem stem363_count : (enumerateFrom leaders 2 14 [3, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem363Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [3, 14] stem363Flags stem363Counts stem363_flags
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
        · exact stem138_count
        · exact stem139_count
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

def stem364Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem364Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem364_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([3, 16] ++ [v])) ↔ stem364Flags v = true := by
  decide +kernel

theorem stem364_count : (enumerateFrom leaders 2 16 [3, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem364Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [3, 16] stem364Flags stem364Counts stem364_flags
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
        · exact stem140_count
        · exact stem141_count
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

def stem365Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem365Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem365_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([3, 17] ++ [v])) ↔ stem365Flags v = true := by
  decide +kernel

theorem stem365_count : (enumerateFrom leaders 2 17 [3, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem365Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [3, 17] stem365Flags stem365Counts stem365_flags
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

def stem366Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true].getD v.val false
def stem366Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 3, 2, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem366_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([4, 4] ++ [v])) ↔ stem366Flags v = true := by
  decide +kernel

theorem stem366_count : (enumerateFrom leaders 2 4 [4, 4]).length = 16 := by
  calc
    _ = 1 + ((List.finRange 18).map stem366Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 4 [4, 4] stem366Flags stem366Counts stem366_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem142_count
        · exact stem143_count
        · cases hv
        · cases hv
        · exact stem144_count
        · exact stem145_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem146_count
        · exact stem147_count
      · intro v hv
        fin_cases v
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
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 16 := by decide +kernel

def stem367Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem367Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem367_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([4, 6] ++ [v])) ↔ stem367Flags v = true := by
  decide +kernel

theorem stem367_count : (enumerateFrom leaders 2 6 [4, 6]).length = 18 := by
  calc
    _ = 1 + ((List.finRange 18).map stem367Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [4, 6] stem367Flags stem367Counts stem367_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem148_count
        · cases hv
        · exact stem149_count
        · cases hv
        · exact stem150_count
        · cases hv
        · exact stem151_count
        · cases hv
        · exact stem152_count
        · cases hv
        · exact stem153_count
        · exact stem154_count
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

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem367_count

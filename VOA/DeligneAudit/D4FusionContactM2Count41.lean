import VOA.DeligneAudit.D4FusionContactM2Count40
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem328Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, true].getD v.val false
def stem328Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem328_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([0, 8] ++ [v])) ↔ stem328Flags v = true := by
  decide +kernel

theorem stem328_count : (enumerateFrom leaders 2 8 [0, 8]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem328Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [0, 8] stem328Flags stem328Counts stem328_flags
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
        · exact stem014_count
        · cases hv
        · exact stem015_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem016_count
        · exact stem017_count
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

def stem329Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem329Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem329_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([0, 10] ++ [v])) ↔ stem329Flags v = true := by
  decide +kernel

theorem stem329_count : (enumerateFrom leaders 2 10 [0, 10]).length = 6 := by
  calc
    _ = 1 + ((List.finRange 18).map stem329Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [0, 10] stem329Flags stem329Counts stem329_flags
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
        · exact stem018_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem019_count
        · exact stem020_count
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

def stem330Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem330Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem330_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([0, 12] ++ [v])) ↔ stem330Flags v = true := by
  decide +kernel

theorem stem330_count : (enumerateFrom leaders 2 12 [0, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem330Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [0, 12] stem330Flags stem330Counts stem330_flags
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
        · exact stem021_count
        · exact stem022_count
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

def stem331Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem331Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem331_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([0, 14] ++ [v])) ↔ stem331Flags v = true := by
  decide +kernel

theorem stem331_count : (enumerateFrom leaders 2 14 [0, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem331Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [0, 14] stem331Flags stem331Counts stem331_flags
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
        · exact stem023_count
        · exact stem024_count
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

def stem332Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem332Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem332_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([0, 16] ++ [v])) ↔ stem332Flags v = true := by
  decide +kernel

theorem stem332_count : (enumerateFrom leaders 2 16 [0, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem332Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [0, 16] stem332Flags stem332Counts stem332_flags
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
        · exact stem025_count
        · exact stem026_count
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

def stem333Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem333Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem333_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([0, 17] ++ [v])) ↔ stem333Flags v = true := by
  decide +kernel

theorem stem333_count : (enumerateFrom leaders 2 17 [0, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem333Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [0, 17] stem333Flags stem333Counts stem333_flags
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

def stem334Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, true].getD v.val false
def stem334Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem334_flags : ∀ v : Fin 18,
    (2 ≤ v.val ∧ Avoids leaders ([1, 2] ++ [v])) ↔ stem334Flags v = true := by
  decide +kernel

theorem stem334_count : (enumerateFrom leaders 2 2 [1, 2]).length = 10 := by
  calc
    _ = 1 + ((List.finRange 18).map stem334Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 2 [1, 2] stem334Flags stem334Counts stem334_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem027_count
        · cases hv
        · exact stem028_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem029_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem030_count
        · exact stem031_count
      · intro v hv
        fin_cases v
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
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 10 := by decide +kernel

def stem335Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, true].getD v.val false
def stem335Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem335_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([1, 4] ++ [v])) ↔ stem335Flags v = true := by
  decide +kernel

theorem stem335_count : (enumerateFrom leaders 2 4 [1, 4]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem335Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 4 [1, 4] stem335Flags stem335Counts stem335_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem032_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem033_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem034_count
        · exact stem035_count
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
        · exact False.elim (hv rfl)
    _ = 8 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem335_count

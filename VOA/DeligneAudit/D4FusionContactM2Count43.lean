import VOA.DeligneAudit.D4FusionContactM2Count42
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem344Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem344Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 4, 0, 7, 2, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem344_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([2, 4] ++ [v])) ↔ stem344Flags v = true := by
  decide +kernel

theorem stem344_count : (enumerateFrom leaders 2 4 [2, 4]).length = 28 := by
  calc
    _ = 1 + ((List.finRange 18).map stem344Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 4 [2, 4] stem344Flags stem344Counts stem344_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem060_count
        · cases hv
        · exact stem061_count
        · exact stem062_count
        · exact stem063_count
        · cases hv
        · exact stem064_count
        · cases hv
        · exact stem065_count
        · cases hv
        · exact stem066_count
        · cases hv
        · exact stem067_count
        · exact stem068_count
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

def stem345Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false].getD v.val false
def stem345Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem345_flags : ∀ v : Fin 18,
    (5 ≤ v.val ∧ Avoids leaders ([2, 5] ++ [v])) ↔ stem345Flags v = true := by
  decide +kernel

theorem stem345_count : (enumerateFrom leaders 2 5 [2, 5]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem345Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 5 [2, 5] stem345Flags stem345Counts stem345_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem069_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem070_count
        · cases hv
        · exact stem071_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem072_count
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

def stem346Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem346Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem346_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([2, 6] ++ [v])) ↔ stem346Flags v = true := by
  decide +kernel

theorem stem346_count : (enumerateFrom leaders 2 6 [2, 6]).length = 18 := by
  calc
    _ = 1 + ((List.finRange 18).map stem346Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 6 [2, 6] stem346Flags stem346Counts stem346_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem073_count
        · cases hv
        · exact stem074_count
        · cases hv
        · exact stem075_count
        · cases hv
        · exact stem076_count
        · cases hv
        · exact stem077_count
        · cases hv
        · exact stem078_count
        · exact stem079_count
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

def stem347Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false].getD v.val false
def stem347Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem347_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([2, 7] ++ [v])) ↔ stem347Flags v = true := by
  decide +kernel

theorem stem347_count : (enumerateFrom leaders 2 7 [2, 7]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem347Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 7 [2, 7] stem347Flags stem347Counts stem347_flags
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
        · exact stem080_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem081_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem082_count
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

def stem348Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, true, true].getD v.val false
def stem348Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem348_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([2, 8] ++ [v])) ↔ stem348Flags v = true := by
  decide +kernel

theorem stem348_count : (enumerateFrom leaders 2 8 [2, 8]).length = 12 := by
  calc
    _ = 1 + ((List.finRange 18).map stem348Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [2, 8] stem348Flags stem348Counts stem348_flags
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
        · exact stem083_count
        · cases hv
        · exact stem084_count
        · exact stem085_count
        · cases hv
        · cases hv
        · exact stem086_count
        · exact stem087_count
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

def stem349Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, true].getD v.val false
def stem349Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem349_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([2, 10] ++ [v])) ↔ stem349Flags v = true := by
  decide +kernel

theorem stem349_count : (enumerateFrom leaders 2 10 [2, 10]).length = 9 := by
  calc
    _ = 1 + ((List.finRange 18).map stem349Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [2, 10] stem349Flags stem349Counts stem349_flags
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
        · exact stem088_count
        · exact stem089_count
        · cases hv
        · cases hv
        · exact stem090_count
        · exact stem091_count
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

def stem350Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem350Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem350_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([2, 12] ++ [v])) ↔ stem350Flags v = true := by
  decide +kernel

theorem stem350_count : (enumerateFrom leaders 2 12 [2, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem350Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [2, 12] stem350Flags stem350Counts stem350_flags
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
        · exact stem092_count
        · cases hv
        · exact stem093_count
        · cases hv
        · exact stem094_count
        · exact stem095_count
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

def stem351Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem351Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem351_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([2, 13] ++ [v])) ↔ stem351Flags v = true := by
  decide +kernel

theorem stem351_count : (enumerateFrom leaders 2 13 [2, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem351Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [2, 13] stem351Flags stem351Counts stem351_flags
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
        · exact stem096_count
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

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem351_count

import VOA.DeligneAudit.D4FusionContactM2Count51
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem416Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem416Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem416_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([10, 12] ++ [v])) ↔ stem416Flags v = true := by
  decide +kernel

theorem stem416_count : (enumerateFrom leaders 2 12 [10, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem416Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [10, 12] stem416Flags stem416Counts stem416_flags
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
        · exact stem288_count
        · cases hv
        · exact stem289_count
        · cases hv
        · exact stem290_count
        · exact stem291_count
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

def stem417Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem417Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem417_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([10, 13] ++ [v])) ↔ stem417Flags v = true := by
  decide +kernel

theorem stem417_count : (enumerateFrom leaders 2 13 [10, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem417Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [10, 13] stem417Flags stem417Counts stem417_flags
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
        · exact stem292_count
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

def stem418Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem418Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem418_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([10, 14] ++ [v])) ↔ stem418Flags v = true := by
  decide +kernel

theorem stem418_count : (enumerateFrom leaders 2 14 [10, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem418Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [10, 14] stem418Flags stem418Counts stem418_flags
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
        · exact stem293_count
        · exact stem294_count
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

def stem419Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem419Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem419_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([10, 16] ++ [v])) ↔ stem419Flags v = true := by
  decide +kernel

theorem stem419_count : (enumerateFrom leaders 2 16 [10, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem419Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [10, 16] stem419Flags stem419Counts stem419_flags
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
        · exact stem295_count
        · exact stem296_count
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

def stem420Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem420Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem420_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([10, 17] ++ [v])) ↔ stem420Flags v = true := by
  decide +kernel

theorem stem420_count : (enumerateFrom leaders 2 17 [10, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem420Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [10, 17] stem420Flags stem420Counts stem420_flags
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

def stem421Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem421Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem421_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([11, 12] ++ [v])) ↔ stem421Flags v = true := by
  decide +kernel

theorem stem421_count : (enumerateFrom leaders 2 12 [11, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem421Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [11, 12] stem421Flags stem421Counts stem421_flags
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
        · exact stem297_count
        · cases hv
        · exact stem298_count
        · cases hv
        · exact stem299_count
        · exact stem300_count
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

def stem422Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem422Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem422_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([11, 13] ++ [v])) ↔ stem422Flags v = true := by
  decide +kernel

theorem stem422_count : (enumerateFrom leaders 2 13 [11, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem422Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [11, 13] stem422Flags stem422Counts stem422_flags
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
        · exact stem301_count
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

def stem423Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem423Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem423_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([11, 14] ++ [v])) ↔ stem423Flags v = true := by
  decide +kernel

theorem stem423_count : (enumerateFrom leaders 2 14 [11, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem423Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [11, 14] stem423Flags stem423Counts stem423_flags
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
        · exact stem302_count
        · exact stem303_count
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem423_count

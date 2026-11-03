import VOA.DeligneAudit.D4FusionContactM2Count49
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem400Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true].getD v.val false
def stem400Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 3, 2, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem400_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([8, 8] ++ [v])) ↔ stem400Flags v = true := by
  decide +kernel

theorem stem400_count : (enumerateFrom leaders 2 8 [8, 8]).length = 16 := by
  calc
    _ = 1 + ((List.finRange 18).map stem400Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [8, 8] stem400Flags stem400Counts stem400_flags
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
        · exact stem244_count
        · exact stem245_count
        · exact stem246_count
        · exact stem247_count
        · cases hv
        · cases hv
        · exact stem248_count
        · exact stem249_count
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
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 16 := by decide +kernel

def stem401Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, true, true].getD v.val false
def stem401Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem401_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([8, 10] ++ [v])) ↔ stem401Flags v = true := by
  decide +kernel

theorem stem401_count : (enumerateFrom leaders 2 10 [8, 10]).length = 14 := by
  calc
    _ = 1 + ((List.finRange 18).map stem401Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [8, 10] stem401Flags stem401Counts stem401_flags
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
        · exact stem250_count
        · cases hv
        · exact stem251_count
        · exact stem252_count
        · exact stem253_count
        · cases hv
        · exact stem254_count
        · exact stem255_count
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
    _ = 14 := by decide +kernel

def stem402Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem402Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem402_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([8, 11] ++ [v])) ↔ stem402Flags v = true := by
  decide +kernel

theorem stem402_count : (enumerateFrom leaders 2 11 [8, 11]).length = 5 := by
  calc
    _ = 1 + ((List.finRange 18).map stem402Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 11 [8, 11] stem402Flags stem402Counts stem402_flags
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
        · exact stem256_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem257_count
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 5 := by decide +kernel

def stem403Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true].getD v.val false
def stem403Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem403_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([8, 12] ++ [v])) ↔ stem403Flags v = true := by
  decide +kernel

theorem stem403_count : (enumerateFrom leaders 2 12 [8, 12]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem403Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [8, 12] stem403Flags stem403Counts stem403_flags
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
        · exact stem258_count
        · cases hv
        · exact stem259_count
        · cases hv
        · exact stem260_count
        · exact stem261_count
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

def stem404Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false].getD v.val false
def stem404Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem404_flags : ∀ v : Fin 18,
    (13 ≤ v.val ∧ Avoids leaders ([8, 13] ++ [v])) ↔ stem404Flags v = true := by
  decide +kernel

theorem stem404_count : (enumerateFrom leaders 2 13 [8, 13]).length = 3 := by
  calc
    _ = 1 + ((List.finRange 18).map stem404Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 13 [8, 13] stem404Flags stem404Counts stem404_flags
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
        · exact stem262_count
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

def stem405Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem405Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem405_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([8, 14] ++ [v])) ↔ stem405Flags v = true := by
  decide +kernel

theorem stem405_count : (enumerateFrom leaders 2 14 [8, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem405Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [8, 14] stem405Flags stem405Counts stem405_flags
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
        · exact stem263_count
        · exact stem264_count
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

def stem406Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem406Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem406_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([8, 16] ++ [v])) ↔ stem406Flags v = true := by
  decide +kernel

theorem stem406_count : (enumerateFrom leaders 2 16 [8, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem406Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [8, 16] stem406Flags stem406Counts stem406_flags
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
        · exact stem265_count
        · exact stem266_count
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

def stem407Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem407Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem407_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([8, 17] ++ [v])) ↔ stem407Flags v = true := by
  decide +kernel

theorem stem407_count : (enumerateFrom leaders 2 17 [8, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem407Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [8, 17] stem407Flags stem407Counts stem407_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem407_count

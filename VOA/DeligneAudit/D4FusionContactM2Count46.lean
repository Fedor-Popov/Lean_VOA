import VOA.DeligneAudit.D4FusionContactM2Count45
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem368Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false].getD v.val false
def stem368Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem368_flags : ∀ v : Fin 18,
    (7 ≤ v.val ∧ Avoids leaders ([4, 7] ++ [v])) ↔ stem368Flags v = true := by
  decide +kernel

theorem stem368_count : (enumerateFrom leaders 2 7 [4, 7]).length = 8 := by
  calc
    _ = 1 + ((List.finRange 18).map stem368Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 7 [4, 7] stem368Flags stem368Counts stem368_flags
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
        · exact stem155_count
        · cases hv
        · exact stem156_count
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem157_count
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
        · exact False.elim (hv rfl)
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · rfl
    _ = 8 := by decide +kernel

def stem369Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, true, true].getD v.val false
def stem369Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 2, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem369_flags : ∀ v : Fin 18,
    (8 ≤ v.val ∧ Avoids leaders ([4, 8] ++ [v])) ↔ stem369Flags v = true := by
  decide +kernel

theorem stem369_count : (enumerateFrom leaders 2 8 [4, 8]).length = 12 := by
  calc
    _ = 1 + ((List.finRange 18).map stem369Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 8 [4, 8] stem369Flags stem369Counts stem369_flags
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
        · exact stem158_count
        · exact stem159_count
        · exact stem160_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem161_count
        · exact stem162_count
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
        · rfl
        · rfl
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 12 := by decide +kernel

def stem370Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, true].getD v.val false
def stem370Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 2, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem370_flags : ∀ v : Fin 18,
    (10 ≤ v.val ∧ Avoids leaders ([4, 10] ++ [v])) ↔ stem370Flags v = true := by
  decide +kernel

theorem stem370_count : (enumerateFrom leaders 2 10 [4, 10]).length = 11 := by
  calc
    _ = 1 + ((List.finRange 18).map stem370Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 10 [4, 10] stem370Flags stem370Counts stem370_flags
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
        · exact stem163_count
        · cases hv
        · exact stem164_count
        · cases hv
        · exact stem165_count
        · cases hv
        · exact stem166_count
        · exact stem167_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 11 := by decide +kernel

def stem371Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false].getD v.val false
def stem371Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem371_flags : ∀ v : Fin 18,
    (11 ≤ v.val ∧ Avoids leaders ([4, 11] ++ [v])) ↔ stem371Flags v = true := by
  decide +kernel

theorem stem371_count : (enumerateFrom leaders 2 11 [4, 11]).length = 5 := by
  calc
    _ = 1 + ((List.finRange 18).map stem371Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 11 [4, 11] stem371Flags stem371Counts stem371_flags
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
        · exact stem168_count
        · cases hv
        · cases hv
        · cases hv
        · exact stem169_count
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

def stem372Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem372Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem372_flags : ∀ v : Fin 18,
    (12 ≤ v.val ∧ Avoids leaders ([4, 12] ++ [v])) ↔ stem372Flags v = true := by
  decide +kernel

theorem stem372_count : (enumerateFrom leaders 2 12 [4, 12]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem372Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 12 [4, 12] stem372Flags stem372Counts stem372_flags
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
        · exact stem170_count
        · exact stem171_count
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

def stem373Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem373Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem373_flags : ∀ v : Fin 18,
    (14 ≤ v.val ∧ Avoids leaders ([4, 14] ++ [v])) ↔ stem373Flags v = true := by
  decide +kernel

theorem stem373_count : (enumerateFrom leaders 2 14 [4, 14]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem373Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 14 [4, 14] stem373Flags stem373Counts stem373_flags
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
        · exact stem172_count
        · exact stem173_count
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

def stem374Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true].getD v.val false
def stem374Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem374_flags : ∀ v : Fin 18,
    (16 ≤ v.val ∧ Avoids leaders ([4, 16] ++ [v])) ↔ stem374Flags v = true := by
  decide +kernel

theorem stem374_count : (enumerateFrom leaders 2 16 [4, 16]).length = 4 := by
  calc
    _ = 1 + ((List.finRange 18).map stem374Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 16 [4, 16] stem374Flags stem374Counts stem374_flags
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
        · exact stem174_count
        · exact stem175_count
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

def stem375Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem375Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem375_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([4, 17] ++ [v])) ↔ stem375Flags v = true := by
  decide +kernel

theorem stem375_count : (enumerateFrom leaders 2 17 [4, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem375Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [4, 17] stem375Flags stem375Counts stem375_flags
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

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem375_count

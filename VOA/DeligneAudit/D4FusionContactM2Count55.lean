import VOA.DeligneAudit.D4FusionContactM2Count54
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option linter.style.longLine false
set_option maxRecDepth 100000

def stem440Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false].getD v.val false
def stem440Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem440_flags : ∀ v : Fin 18,
    (17 ≤ v.val ∧ Avoids leaders ([17, 17] ++ [v])) ↔ stem440Flags v = true := by
  decide +kernel

theorem stem440_count : (enumerateFrom leaders 2 17 [17, 17]).length = 1 := by
  calc
    _ = 1 + ((List.finRange 18).map stem440Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 1 17 [17, 17] stem440Flags stem440Counts stem440_flags
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

def stem441Flags (v : Fin 18) : Bool := [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem441Counts (v : Fin 18) : ℕ := [4, 0, 10, 0, 8, 0, 6, 0, 8, 0, 6, 0, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem441_flags : ∀ v : Fin 18,
    (0 ≤ v.val ∧ Avoids leaders ([0] ++ [v])) ↔ stem441Flags v = true := by
  decide +kernel

theorem stem441_count : (enumerateFrom leaders 3 0 [0]).length = 56 := by
  calc
    _ = 1 + ((List.finRange 18).map stem441Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 0 [0] stem441Flags stem441Counts stem441_flags
      · intro v hv
        fin_cases v
        · exact stem324_count
        · cases hv
        · exact stem325_count
        · cases hv
        · exact stem326_count
        · cases hv
        · exact stem327_count
        · cases hv
        · exact stem328_count
        · cases hv
        · exact stem329_count
        · cases hv
        · exact stem330_count
        · cases hv
        · exact stem331_count
        · cases hv
        · exact stem332_count
        · exact stem333_count
      · intro v hv
        fin_cases v
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
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 56 := by decide +kernel

def stem442Flags (v : Fin 18) : Bool := [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true].getD v.val false
def stem442Counts (v : Fin 18) : ℕ := [0, 0, 10, 0, 8, 0, 6, 0, 8, 0, 6, 0, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem442_flags : ∀ v : Fin 18,
    (1 ≤ v.val ∧ Avoids leaders ([1] ++ [v])) ↔ stem442Flags v = true := by
  decide +kernel

theorem stem442_count : (enumerateFrom leaders 3 1 [1]).length = 52 := by
  calc
    _ = 1 + ((List.finRange 18).map stem442Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 1 [1] stem442Flags stem442Counts stem442_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · exact stem334_count
        · cases hv
        · exact stem335_count
        · cases hv
        · exact stem336_count
        · cases hv
        · exact stem337_count
        · cases hv
        · exact stem338_count
        · cases hv
        · exact stem339_count
        · cases hv
        · exact stem340_count
        · cases hv
        · exact stem341_count
        · exact stem342_count
      · intro v hv
        fin_cases v
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
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 52 := by decide +kernel

def stem443Flags (v : Fin 18) : Bool := [false, false, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true].getD v.val false
def stem443Counts (v : Fin 18) : ℕ := [0, 0, 25, 0, 28, 9, 18, 8, 12, 0, 9, 0, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem443_flags : ∀ v : Fin 18,
    (2 ≤ v.val ∧ Avoids leaders ([2] ++ [v])) ↔ stem443Flags v = true := by
  decide +kernel

theorem stem443_count : (enumerateFrom leaders 3 2 [2]).length = 130 := by
  calc
    _ = 1 + ((List.finRange 18).map stem443Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 2 [2] stem443Flags stem443Counts stem443_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · exact stem343_count
        · cases hv
        · exact stem344_count
        · exact stem345_count
        · exact stem346_count
        · exact stem347_count
        · exact stem348_count
        · cases hv
        · exact stem349_count
        · cases hv
        · exact stem350_count
        · exact stem351_count
        · exact stem352_count
        · cases hv
        · exact stem353_count
        · exact stem354_count
      · intro v hv
        fin_cases v
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
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 130 := by decide +kernel

def stem444Flags (v : Fin 18) : Bool := [false, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true].getD v.val false
def stem444Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 28, 9, 18, 8, 12, 0, 9, 0, 8, 3, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem444_flags : ∀ v : Fin 18,
    (3 ≤ v.val ∧ Avoids leaders ([3] ++ [v])) ↔ stem444Flags v = true := by
  decide +kernel

theorem stem444_count : (enumerateFrom leaders 3 3 [3]).length = 105 := by
  calc
    _ = 1 + ((List.finRange 18).map stem444Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 3 [3] stem444Flags stem444Counts stem444_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem355_count
        · exact stem356_count
        · exact stem357_count
        · exact stem358_count
        · exact stem359_count
        · cases hv
        · exact stem360_count
        · cases hv
        · exact stem361_count
        · exact stem362_count
        · exact stem363_count
        · cases hv
        · exact stem364_count
        · exact stem365_count
      · intro v hv
        fin_cases v
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
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 105 := by decide +kernel

def stem445Flags (v : Fin 18) : Bool := [false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, false, true, true].getD v.val false
def stem445Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 16, 0, 18, 8, 12, 0, 11, 5, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem445_flags : ∀ v : Fin 18,
    (4 ≤ v.val ∧ Avoids leaders ([4] ++ [v])) ↔ stem445Flags v = true := by
  decide +kernel

theorem stem445_count : (enumerateFrom leaders 3 4 [4]).length = 84 := by
  calc
    _ = 1 + ((List.finRange 18).map stem445Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 4 [4] stem445Flags stem445Counts stem445_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem366_count
        · cases hv
        · exact stem367_count
        · exact stem368_count
        · exact stem369_count
        · cases hv
        · exact stem370_count
        · exact stem371_count
        · exact stem372_count
        · cases hv
        · exact stem373_count
        · cases hv
        · exact stem374_count
        · exact stem375_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 84 := by decide +kernel

def stem446Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true].getD v.val false
def stem446Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 18, 8, 12, 0, 11, 5, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem446_flags : ∀ v : Fin 18,
    (5 ≤ v.val ∧ Avoids leaders ([5] ++ [v])) ↔ stem446Flags v = true := by
  decide +kernel

theorem stem446_count : (enumerateFrom leaders 3 5 [5]).length = 68 := by
  calc
    _ = 1 + ((List.finRange 18).map stem446Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 5 [5] stem446Flags stem446Counts stem446_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem376_count
        · exact stem377_count
        · exact stem378_count
        · cases hv
        · exact stem379_count
        · exact stem380_count
        · exact stem381_count
        · cases hv
        · exact stem382_count
        · cases hv
        · exact stem383_count
        · exact stem384_count
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
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 68 := by decide +kernel

def stem447Flags (v : Fin 18) : Bool := [false, false, false, false, false, false, true, false, true, true, true, false, true, false, true, false, true, true].getD v.val false
def stem447Counts (v : Fin 18) : ℕ := [0, 0, 0, 0, 0, 0, 9, 0, 15, 7, 6, 0, 4, 0, 4, 0, 4, 1].getD v.val 0

set_option maxHeartbeats 2000000 in
-- Check only one finite stem, with no recursive descendant expansion.
theorem stem447_flags : ∀ v : Fin 18,
    (6 ≤ v.val ∧ Avoids leaders ([6] ++ [v])) ↔ stem447Flags v = true := by
  decide +kernel

theorem stem447_count : (enumerateFrom leaders 3 6 [6]).length = 51 := by
  calc
    _ = 1 + ((List.finRange 18).map stem447Counts).sum := by
      apply enumerateFrom_length_of_flags leaders 2 6 [6] stem447Flags stem447Counts stem447_flags
      · intro v hv
        fin_cases v
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · cases hv
        · exact stem385_count
        · cases hv
        · exact stem386_count
        · exact stem387_count
        · exact stem388_count
        · cases hv
        · exact stem389_count
        · cases hv
        · exact stem390_count
        · cases hv
        · exact stem391_count
        · exact stem392_count
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
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · rfl
        · exact False.elim (hv rfl)
        · exact False.elim (hv rfl)
    _ = 51 := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem447_count

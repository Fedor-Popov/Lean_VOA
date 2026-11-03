import VOA.DeligneAudit.SL4TMixedStateFlag

/-! # Recursive cell counts with double and triple labels -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The double and triple counts of a cell, in that order. -/
abbrev MixedCellCounts := ℕ × ℕ

/-- A cell's truncation level is the sum of its double and triple counts. -/
def mixedCellLevel (c : MixedCellCounts) : ℕ := c.1 + c.2

def mixedCellShift (d t : ℕ) (c : MixedCellCounts) : MixedCellCounts :=
  (c.1 + d, c.2 + t)

def mixedADoubleCount (s : MixedAState) : ℕ := if mixedAZeroRoots s = 1 then 1 else 0

def mixedATripleCount (s : MixedAState) : ℕ := if mixedAZeroRoots s = 2 then 1 else 0

theorem mixedA_counts_level (s : MixedAState) :
    mixedADoubleCount s + mixedATripleCount s = mixedALevelShift s := by
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [mixedADoubleCount, mixedATripleCount, mixedALevelShift, mixedAZeroRoots]

theorem mixedA_counts_weight (s : MixedAState) :
    mixedADoubleCount s + 2 * mixedATripleCount s = mixedAZeroRoots s := by
  rcases s with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [mixedADoubleCount, mixedATripleCount, mixedAZeroRoots]

theorem mixedCellShift_level (d t : ℕ) (c : MixedCellCounts) :
    mixedCellLevel (mixedCellShift d t c) = mixedCellLevel c + (d + t) := by
  simp only [mixedCellLevel, mixedCellShift]
  omega

/-- Ordered mixed cells: peel every b-site before peeling any a-site. Invalid states are empty. -/
def mixedCellData (n : ℕ) (q : MixedParams) : List MixedCellCounts := by
  classical
  exact match n with
  | 0 => if MixedValid q then [(0, 0)] else []
  | n + 1 => if MixedValid q then
      if 1 ≤ q.B then
        (List.range 4).flatMap (fun i => if hi : i < 4 then
          (mixedCellData n (mixedBNext q (mixedBOrder ⟨i, hi⟩))).map
            (mixedCellShift (mixedBZeroRoots (mixedBOrder ⟨i, hi⟩)) 0) else [])
      else
        (List.range 9).flatMap (fun i => if hi : i < 9 then
          (mixedCellData n (mixedANext q (mixedAOrder ⟨i, hi⟩))).map
            (mixedCellShift (mixedADoubleCount (mixedAOrder ⟨i, hi⟩))
              (mixedATripleCount (mixedAOrder ⟨i, hi⟩))) else [])
    else []

/-- The levels of the recursively ordered cells. -/
def mixedCellLevels (n : ℕ) (q : MixedParams) : List ℕ :=
  (mixedCellData n q).map mixedCellLevel

theorem mixedCellData_invalid (n : ℕ) (q : MixedParams) (hq : ¬ MixedValid q) :
    mixedCellData n q = [] := by cases n <;> simp [mixedCellData, hq]

theorem mixedCellLevels_invalid (n : ℕ) (q : MixedParams) (hq : ¬ MixedValid q) :
    mixedCellLevels n q = [] := by simp [mixedCellLevels, mixedCellData_invalid n q hq]

theorem mixedCellLevels_b_step (n : ℕ) (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) :
    mixedCellLevels (n + 1) q = (List.range 4).flatMap (fun i => if hi : i < 4 then
      (mixedCellLevels n (mixedBNext q (mixedBOrder ⟨i, hi⟩))).map
        (fun k => k + mixedBZeroRoots (mixedBOrder ⟨i, hi⟩)) else []) := by
  simp only [mixedCellLevels, mixedCellData, if_pos hq, if_pos hB, List.map_flatMap]
  congr 1
  funext i
  split_ifs <;> simp [List.map_map, Function.comp_def, mixedCellShift_level]

theorem mixedCellLevels_a_step (n : ℕ) (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) :
    mixedCellLevels (n + 1) q = (List.range 9).flatMap (fun i => if hi : i < 9 then
      (mixedCellLevels n (mixedANext q (mixedAOrder ⟨i, hi⟩))).map
        (fun k => k + mixedALevelShift (mixedAOrder ⟨i, hi⟩)) else []) := by
  have hn : ¬ 1 ≤ q.B := by omega
  simp only [mixedCellLevels, mixedCellData, if_pos hq, if_neg hn, List.map_flatMap]
  congr 1
  funext i
  split_ifs <;> simp [List.map_map, Function.comp_def, mixedCellShift_level,
    mixedA_counts_level]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedA_counts_level
#print axioms VOA.DeligneAudit.SL4T.mixedA_counts_weight
#print axioms VOA.DeligneAudit.SL4T.mixedCellShift_level
#print axioms VOA.DeligneAudit.SL4T.mixedCellData_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_invalid
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_b_step
#print axioms VOA.DeligneAudit.SL4T.mixedCellLevels_a_step

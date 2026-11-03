/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part0
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part0
import VOA.Examples.TripletWpTwoZhuSparseHMode3Part2

/-! # Full H-left coordinates at Zhu modes two and three -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- The three independently certified H monomials merge to the complete mode.
theorem hEntryMode2_eq :
    hEntryModeSparseQ 2 = hEntry0Mode2ExpectedQ := by
  rw [hEntryMode_split 2 (by norm_num), hEntryMode2Part0_eq,
    hEntryMode2Part1_eq, hEntryMode2Part2_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hEntry0Mode2Part0ExpectedQ, hEntry0Mode2Part1ExpectedQ,
    hEntry0Mode2Part2ExpectedQ, hEntry0Mode2ExpectedQ,
    sumQ, addQ, normalizeQ, insertQ, sortWord, insertVar, insertSorted,
    compareWord, List.map_cons, List.map_nil]

set_option maxHeartbeats 1000000 in
-- The three independently certified H monomials merge to the complete mode.
theorem hEntryMode3_eq :
    hEntryModeSparseQ 3 = hEntry0Mode3ExpectedQ := by
  rw [hEntryMode_split 3 (by norm_num), hEntryMode3Part0_eq,
    hEntryMode3Part1_eq, hEntryMode3Part2_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hEntry0Mode3Part0ExpectedQ, hEntry0Mode3Part1ExpectedQ,
    hEntry0Mode3Part2ExpectedQ, hEntry0Mode3ExpectedQ,
    sumQ, addQ, normalizeQ, insertQ, sortWord, insertVar, insertSorted,
    compareWord, List.map_cons, List.map_nil]

#print axioms hEntryMode2_eq
#print axioms hEntryMode3_eq

end VOA.LatGen.WpTwoZhuSparseCompute

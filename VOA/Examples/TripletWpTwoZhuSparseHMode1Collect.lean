/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode1Part0Collect

/-! # Full H-left coordinate at Zhu mode one -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

set_option maxHeartbeats 1000000 in
-- The three independently certified H monomials merge to the complete mode.
theorem hEntryMode1_eq :
    hEntryModeSparseQ 1 = hEntry0Mode1ExpectedQ := by
  rw [hEntryMode_split 1 (by norm_num), hEntryMode1Part0_eq,
    hEntryMode1Part1_eq, hEntryMode1Part2_eq]
  norm_num (config := { maxSteps := 1000000 })
    [hEntry0Mode1Part0ExpectedQ, hEntry0Mode1Part1ExpectedQ,
    hEntry0Mode1Part2ExpectedQ, hEntry0Mode1ExpectedQ,
    sumQ, addQ, normalizeQ, insertQ, sortWord, insertVar, insertSorted,
    compareWord, List.map_cons, List.map_nil]

#print axioms hEntryMode1_eq

end VOA.LatGen.WpTwoZhuSparseCompute

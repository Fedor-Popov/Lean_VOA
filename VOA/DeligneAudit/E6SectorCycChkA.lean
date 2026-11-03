/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorChecks
import VOA.DeligneAudit.E6SectorDefs

set_option linter.style.longLine false

/-!
# E₆ coadjoint cyclicity: Boolean word checks (light imports)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

theorem cycChk0 : zeroL (([([11, 73, 62], (4 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-5 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (4 : ℤ)), ([6, 74, 59], (-2 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(3)) [(0, 1)]) = true := by
  decide +kernel

theorem cycChk1 : zeroL (([([11, 73, 62], (1 : ℤ)), ([10, 77, 46], (-2 : ℤ)), ([9, 75, 56], (-2 : ℤ)), ([8, 76, 51], (-3 : ℤ)), ([7, 75, 55], (2 : ℤ)), ([6, 74, 59], (-1 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(1)) [(1, 1)]) = true := by
  decide +kernel

theorem cycChk2 : zeroL (([([11, 73, 62], (5 : ℤ)), ([10, 77, 46], (-6 : ℤ)), ([9, 75, 56], (-10 : ℤ)), ([8, 76, 51], (-12 : ℤ)), ([7, 75, 55], (8 : ℤ)), ([6, 74, 59], (-4 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(3)) [(2, 1)]) = true := by
  decide +kernel

theorem cycChk3 : zeroL (([([11, 73, 62], (2 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-4 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (4 : ℤ)), ([6, 74, 59], (-2 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(1)) [(3, 1)]) = true := by
  decide +kernel

theorem cycChk4 : zeroL (([([11, 73, 62], (4 : ℤ)), ([10, 77, 46], (-6 : ℤ)), ([9, 75, 56], (-8 : ℤ)), ([8, 76, 51], (-12 : ℤ)), ([7, 75, 55], (10 : ℤ)), ([6, 74, 59], (-5 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(3)) [(4, 1)]) = true := by
  decide +kernel

theorem cycChk5 : zeroL (([([11, 73, 62], (2 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-4 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (5 : ℤ)), ([6, 74, 59], (-4 : ℤ))] : List (List ℕ × ℤ)).flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
    scale (-(3)) [(5, 1)]) = true := by
  decide +kernel

theorem cycChk6 : zeroL (wordS e6T 78 [74, 59] [(77, 1)] ++ scale (-(-1)) [(6, 1)]) = true := by
  decide +kernel

theorem cycChk7 : zeroL (wordS e6T 78 [75, 55] [(77, 1)] ++ scale (-(1)) [(7, 1)]) = true := by
  decide +kernel

theorem cycChk8 : zeroL (wordS e6T 78 [76, 51] [(77, 1)] ++ scale (-(-1)) [(8, 1)]) = true := by
  decide +kernel

theorem cycChk9 : zeroL (wordS e6T 78 [75, 56] [(77, 1)] ++ scale (-(-1)) [(9, 1)]) = true := by
  decide +kernel

theorem cycChk10 : zeroL (wordS e6T 78 [77, 46] [(77, 1)] ++ scale (-(-1)) [(10, 1)]) = true := by
  decide +kernel

theorem cycChk11 : zeroL (wordS e6T 78 [73, 62] [(77, 1)] ++ scale (-(1)) [(11, 1)]) = true := by
  decide +kernel

theorem cycChk12 : zeroL (wordS e6T 78 [75, 59] [(77, 1)] ++ scale (-(1)) [(12, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6

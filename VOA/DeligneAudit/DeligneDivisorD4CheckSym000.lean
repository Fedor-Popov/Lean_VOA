/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly

/-! Four or fewer symmetric certificate pairs in row 0. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem pair0 :
    (List.range' 0 1).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  decide +kernel

private theorem pair1 :
    (List.range' 1 1).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  decide +kernel

private theorem pair2 :
    (List.range' 2 1).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  decide +kernel

private theorem pair3 :
    (List.range' 3 1).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  decide +kernel

theorem d4_sym_pairs_000 :
    (List.range' 0 4).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  exact check_range_join 0 1 1 3 4 (by decide) (by decide) pair0
    (check_range_join 1 1 2 2 3 (by decide) (by decide) pair1
    (check_range_join 2 1 3 1 2 (by decide) (by decide) pair2
    (pair3)))

end VOA.DeligneAudit.DeligneDivisor.D4

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4FusionCountChain0

/-! `F₄`: pinned intermediate Demazure characters of `C_1`, block 1 (one `decide` per operator). -/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

def f4P4 : LPoly :=
  [(([2, 3, 4, 2], -1), 1), (([1, 2, 3, 2], -1), 1), (([1, 1, 2, 2], -1), 1), (([1, 2, 2, 2], -1), 1), (([1, 2, 4, 2], -1), 1), (([1, 3, 4, 2], -1), 1), (([0, 0, 0, 0], 0), 1)]

theorem f4_s4 : demazureFin cartanF4 1 f4P3 = f4P4 := by
  decide +kernel

theorem f4_c4 : ([1, 2, 1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P4 :=
  foldr_step cartanF4 1 [2, 1, 0] _ _ _ f4_c3 f4_s4

def f4P5 : LPoly :=
  [(([0, 0, 0, 0], 0), 1), (([1, 2, 4, 2], -1), 1), (([1, 2, 2, 2], -1), 1), (([0, 1, 2, 2], -1), 1), (([1, 1, 2, 2], -1), 1), (([1, 2, 3, 2], -1), 1), (([1, 3, 4, 2], -1), 1), (([2, 3, 4, 2], -1), 1)]

theorem f4_s5 : demazureFin cartanF4 0 f4P4 = f4P5 := by
  decide +kernel

theorem f4_c5 : ([0, 1, 2, 1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P5 :=
  foldr_step cartanF4 0 [1, 2, 1, 0] _ _ _ f4_c4 f4_s5

def f4P6 : LPoly :=
  [(([2, 3, 4, 2], -1), 1), (([1, 3, 4, 2], -1), 1), (([1, 2, 3, 1], -1), 1), (([1, 2, 3, 2], -1), 1), (([1, 1, 2, 0], -1), 1), (([1, 1, 2, 1], -1), 1), (([1, 1, 2, 2], -1), 1), (([0, 1, 2, 0], -1), 1), (([0, 1, 2, 1], -1), 1), (([0, 1, 2, 2], -1), 1), (([1, 2, 2, 0], -1), 1), (([1, 2, 2, 1], -1), 1), (([1, 2, 2, 2], -1), 1), (([1, 2, 4, 2], -1), 1), (([0, 0, 0, 0], 0), 1)]

theorem f4_s6 : demazureFin cartanF4 3 f4P5 = f4P6 := by
  decide +kernel

theorem f4_c6 : ([3, 0, 1, 2, 1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P6 :=
  foldr_step cartanF4 3 [0, 1, 2, 1, 0] _ _ _ f4_c5 f4_s6

def f4P7 : LPoly :=
  [(([0, 0, 0, 0], 0), 1), (([1, 2, 2, 2], -1), 1), (([1, 2, 3, 2], -1), 1), (([1, 2, 4, 2], -1), 1), (([1, 2, 2, 0], -1), 1), (([0, 1, 2, 2], -1), 1), (([0, 1, 1, 1], -1), 1), (([0, 1, 2, 1], -1), 1), (([0, 1, 0, 0], -1), 1), (([0, 1, 1, 0], -1), 1), (([0, 1, 2, 0], -1), 1), (([1, 1, 2, 2], -1), 1), (([1, 1, 1, 1], -1), 1), (([1, 1, 2, 1], -1), 1), (([1, 1, 0, 0], -1), 1), (([1, 1, 1, 0], -1), 1), (([1, 1, 2, 0], -1), 1), (([1, 2, 2, 1], -1), 1), (([1, 2, 3, 1], -1), 1), (([1, 3, 4, 2], -1), 1), (([2, 3, 4, 2], -1), 1)]

theorem f4_s7 : demazureFin cartanF4 2 f4P6 = f4P7 := by
  decide +kernel

theorem f4_c7 : ([2, 3, 0, 1, 2, 1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P7 :=
  foldr_step cartanF4 2 [3, 0, 1, 2, 1, 0] _ _ _ f4_c6 f4_s7

end VOA.DeligneAudit.DeligneCharacter.DemCount

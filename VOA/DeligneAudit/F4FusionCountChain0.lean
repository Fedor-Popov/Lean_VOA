/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.DeligneCharacterExceptional

/-! `F₄`: pinned intermediate Demazure characters of `C_1`, block 0 (one `decide` per operator). -/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

def f4P0 : LPoly :=
  [(([2, 3, 4, 2], -1), 1), (([0, 0, 0, 0], 0), 1)]

theorem f4_s0 : demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)] = f4P0 := by
  decide +kernel

theorem f4_c0 : ([] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P0 := f4_s0

def f4P1 : LPoly :=
  [(([0, 0, 0, 0], 0), 1), (([1, 3, 4, 2], -1), 1), (([2, 3, 4, 2], -1), 1)]

theorem f4_s1 : demazureFin cartanF4 0 f4P0 = f4P1 := by
  decide +kernel

theorem f4_c1 : ([0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P1 :=
  foldr_step cartanF4 0 [] _ _ _ f4_c0 f4_s1

def f4P2 : LPoly :=
  [(([2, 3, 4, 2], -1), 1), (([1, 2, 4, 2], -1), 1), (([1, 3, 4, 2], -1), 1), (([0, 0, 0, 0], 0), 1)]

theorem f4_s2 : demazureFin cartanF4 1 f4P1 = f4P2 := by
  decide +kernel

theorem f4_c2 : ([1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P2 :=
  foldr_step cartanF4 1 [0] _ _ _ f4_c1 f4_s2

def f4P3 : LPoly :=
  [(([0, 0, 0, 0], 0), 1), (([1, 3, 4, 2], -1), 1), (([1, 2, 2, 2], -1), 1), (([1, 2, 3, 2], -1), 1), (([1, 2, 4, 2], -1), 1), (([2, 3, 4, 2], -1), 1)]

theorem f4_s3 : demazureFin cartanF4 2 f4P2 = f4P3 := by
  decide +kernel

theorem f4_c3 : ([2, 1, 0] : List ℕ).foldr (fun i g => demazureFin cartanF4 i g)
    (demazureZero cartanF4 thetaF4 [((List.replicate thetaF4.length 0, 0), 1)]) = f4P3 :=
  foldr_step cartanF4 2 [1, 0] _ _ _ f4_c2 f4_s3

end VOA.DeligneAudit.DeligneCharacter.DemCount

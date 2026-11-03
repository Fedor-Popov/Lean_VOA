/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.DeligneCharacterExceptional

/-! `E₇`: pinned intermediate Demazure characters `P_0`…`P_11` of `C_1` (one `decide` per operator). -/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

set_option maxHeartbeats 4000000 in
def e7P0 : LPoly :=
  [(([2, 2, 3, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s0 : demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)] = e7P0 := by
  decide +kernel

theorem e7_c0 : ([] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P0 := e7_s0

set_option maxHeartbeats 4000000 in
def e7P1 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s1 : demazureFin cartanE7 0 e7P0 = e7P1 := by
  decide +kernel

theorem e7_c1 : ([0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P1 :=
  foldr_step cartanE7 0 [] _ _ _ e7_c0 e7_s1

set_option maxHeartbeats 4000000 in
def e7P2 : LPoly :=
  [(([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s2 : demazureFin cartanE7 2 e7P1 = e7P2 := by
  decide +kernel

theorem e7_c2 : ([2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P2 :=
  foldr_step cartanE7 2 [0] _ _ _ e7_c1 e7_s2

set_option maxHeartbeats 4000000 in
def e7P3 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s3 : demazureFin cartanE7 3 e7P2 = e7P3 := by
  decide +kernel

theorem e7_c3 : ([3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P3 :=
  foldr_step cartanE7 3 [2, 0] _ _ _ e7_c2 e7_s3

set_option maxHeartbeats 4000000 in
def e7P4 : LPoly :=
  [(([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s4 : demazureFin cartanE7 1 e7P3 = e7P4 := by
  decide +kernel

theorem e7_c4 : ([1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P4 :=
  foldr_step cartanE7 1 [3, 2, 0] _ _ _ e7_c3 e7_s4

set_option maxHeartbeats 4000000 in
def e7P5 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s5 : demazureFin cartanE7 4 e7P4 = e7P5 := by
  decide +kernel

theorem e7_c5 : ([4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P5 :=
  foldr_step cartanE7 4 [1, 3, 2, 0] _ _ _ e7_c4 e7_s5

set_option maxHeartbeats 4000000 in
def e7P6 : LPoly :=
  [(([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s6 : demazureFin cartanE7 3 e7P5 = e7P6 := by
  decide +kernel

theorem e7_c6 : ([3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P6 :=
  foldr_step cartanE7 3 [4, 1, 3, 2, 0] _ _ _ e7_c5 e7_s6

set_option maxHeartbeats 4000000 in
def e7P7 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s7 : demazureFin cartanE7 2 e7P6 = e7P7 := by
  decide +kernel

theorem e7_c7 : ([2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P7 :=
  foldr_step cartanE7 2 [3, 4, 1, 3, 2, 0] _ _ _ e7_c6 e7_s7

set_option maxHeartbeats 4000000 in
def e7P8 : LPoly :=
  [(([1, 2, 3, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([0, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s8 : demazureFin cartanE7 0 e7P7 = e7P8 := by
  decide +kernel

theorem e7_c8 : ([0, 2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P8 :=
  foldr_step cartanE7 0 [2, 3, 4, 1, 3, 2, 0] _ _ _ e7_c7 e7_s8

set_option maxHeartbeats 4000000 in
def e7P9 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 1, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 1, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 1, 2, 2, 1, 1], -1), 1), (([1, 1, 1, 2, 2, 2, 1], -1), 1), (([0, 1, 1, 2, 2, 1, 1], -1), 1), (([0, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 1, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s9 : demazureFin cartanE7 5 e7P8 = e7P9 := by
  decide +kernel

theorem e7_c9 : ([5, 0, 2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P9 :=
  foldr_step cartanE7 5 [0, 2, 3, 4, 1, 3, 2, 0] _ _ _ e7_c8 e7_s9

set_option maxHeartbeats 4000000 in
def e7P10 : LPoly :=
  [(([1, 2, 3, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 2, 1, 1, 1], -1), 1), (([1, 1, 2, 2, 2, 1, 1], -1), 1), (([0, 1, 1, 2, 2, 2, 1], -1), 1), (([0, 1, 1, 2, 1, 1, 1], -1), 1), (([0, 1, 1, 2, 2, 1, 1], -1), 1), (([1, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 1, 2, 1, 1, 1], -1), 1), (([1, 1, 1, 2, 2, 1, 1], -1), 1), (([1, 1, 2, 3, 2, 1, 1], -1), 1), (([1, 2, 2, 3, 2, 1, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s10 : demazureFin cartanE7 4 e7P9 = e7P10 := by
  decide +kernel

theorem e7_c10 : ([4, 5, 0, 2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P10 :=
  foldr_step cartanE7 4 [5, 0, 2, 3, 4, 1, 3, 2, 0] _ _ _ e7_c9 e7_s10

set_option maxHeartbeats 4000000 in
def e7P11 : LPoly :=
  [(([0, 0, 0, 0, 0, 0, 0], 0), 1), (([1, 2, 2, 3, 3, 2, 1], -1), 1), (([1, 2, 2, 4, 3, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 1, 1], -1), 1), (([1, 1, 2, 2, 2, 1, 1], -1), 1), (([1, 1, 2, 3, 2, 1, 1], -1), 1), (([1, 1, 1, 2, 2, 1, 1], -1), 1), (([1, 1, 1, 1, 1, 1, 1], -1), 1), (([1, 1, 1, 2, 1, 1, 1], -1), 1), (([1, 1, 1, 2, 2, 2, 1], -1), 1), (([0, 1, 1, 2, 2, 1, 1], -1), 1), (([0, 1, 1, 1, 1, 1, 1], -1), 1), (([0, 1, 1, 2, 1, 1, 1], -1), 1), (([0, 1, 1, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 2, 1, 1, 1], -1), 1), (([1, 1, 2, 3, 3, 2, 1], -1), 1), (([1, 1, 2, 2, 2, 2, 1], -1), 1), (([1, 1, 2, 3, 2, 2, 1], -1), 1), (([1, 2, 2, 3, 2, 2, 1], -1), 1), (([2, 2, 3, 4, 3, 2, 1], -1), 1), (([1, 2, 3, 4, 3, 2, 1], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e7_s11 : demazureFin cartanE7 3 e7P10 = e7P11 := by
  decide +kernel

theorem e7_c11 : ([3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr (fun i g => demazureFin cartanE7 i g)
    (demazureZero cartanE7 thetaE7 [((List.replicate thetaE7.length 0, 0), 1)]) = e7P11 :=
  foldr_step cartanE7 3 [4, 5, 0, 2, 3, 4, 1, 3, 2, 0] _ _ _ e7_c10 e7_s11

end VOA.DeligneAudit.DeligneCharacter.DemCount

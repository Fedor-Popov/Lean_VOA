/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF400
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF401
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF402
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF403
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF404
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF405
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF406
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF407
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF408
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF409
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF410
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF411
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF412
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF413
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF414
import VOA.DeligneAudit.DeligneCharacterExceptionalStepF415

/-! Certified full algorithm outputs assembled opaquely from single-operator facts. -/
namespace VOA.DeligneAudit.DeligneCharacter

private theorem exceptional_f4_fold_0_15 :
    ([]).foldr (demazureFin cartanF4)
      exceptionalF4State16 = exceptionalF4State16 := by
  rfl

private theorem exceptional_f4_fold_0_14 :
    ([0]).foldr (demazureFin cartanF4)
      exceptionalF4State15 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0]) ([]) 0
    exceptionalF4State15 exceptionalF4State16 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_15
    exceptional_f4_fold_0_15

private theorem exceptional_f4_fold_0_13 :
    ([0, 1]).foldr (demazureFin cartanF4)
      exceptionalF4State14 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1]) ([0]) 1
    exceptionalF4State14 exceptionalF4State15 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_14
    exceptional_f4_fold_0_14

private theorem exceptional_f4_fold_0_12 :
    ([0, 1, 2]).foldr (demazureFin cartanF4)
      exceptionalF4State13 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2]) ([0, 1]) 2
    exceptionalF4State13 exceptionalF4State14 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_13
    exceptional_f4_fold_0_13

private theorem exceptional_f4_fold_0_11 :
    ([0, 1, 2, 3]).foldr (demazureFin cartanF4)
      exceptionalF4State12 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3]) ([0, 1, 2]) 3
    exceptionalF4State12 exceptionalF4State13 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_12
    exceptional_f4_fold_0_12

private theorem exceptional_f4_fold_0_10 :
    ([0, 1, 2, 3, 1]).foldr (demazureFin cartanF4)
      exceptionalF4State11 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1]) ([0, 1, 2, 3]) 1
    exceptionalF4State11 exceptionalF4State12 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_11
    exceptional_f4_fold_0_11

private theorem exceptional_f4_fold_0_9 :
    ([0, 1, 2, 3, 1, 2]).foldr (demazureFin cartanF4)
      exceptionalF4State10 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2]) ([0, 1, 2, 3, 1]) 2
    exceptionalF4State10 exceptionalF4State11 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_10
    exceptional_f4_fold_0_10

private theorem exceptional_f4_fold_0_8 :
    ([0, 1, 2, 3, 1, 2, 0]).foldr (demazureFin cartanF4)
      exceptionalF4State9 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0]) ([0, 1, 2, 3, 1, 2]) 0
    exceptionalF4State9 exceptionalF4State10 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_09
    exceptional_f4_fold_0_9

private theorem exceptional_f4_fold_0_7 :
    ([0, 1, 2, 3, 1, 2, 0, 1]).foldr (demazureFin cartanF4)
      exceptionalF4State8 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1]) ([0, 1, 2, 3, 1, 2, 0]) 1
    exceptionalF4State8 exceptionalF4State9 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_08
    exceptional_f4_fold_0_8

private theorem exceptional_f4_fold_0_6 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2]).foldr (demazureFin cartanF4)
      exceptionalF4State7 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2]) ([0, 1, 2, 3, 1, 2, 0, 1]) 2
    exceptionalF4State7 exceptionalF4State8 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_07
    exceptional_f4_fold_0_7

private theorem exceptional_f4_fold_0_5 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3]).foldr (demazureFin cartanF4)
      exceptionalF4State6 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3]) ([0, 1, 2, 3, 1, 2, 0, 1, 2]) 3
    exceptionalF4State6 exceptionalF4State7 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_06
    exceptional_f4_fold_0_6

private theorem exceptional_f4_fold_0_4 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0]).foldr (demazureFin cartanF4)
      exceptionalF4State5 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0]) ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3]) 0
    exceptionalF4State5 exceptionalF4State6 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_05
    exceptional_f4_fold_0_5

private theorem exceptional_f4_fold_0_3 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1]).foldr (demazureFin cartanF4)
      exceptionalF4State4 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1]) ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0]) 1
    exceptionalF4State4 exceptionalF4State5 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_04
    exceptional_f4_fold_0_4

private theorem exceptional_f4_fold_0_2 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2]).foldr (demazureFin cartanF4)
      exceptionalF4State3 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2]) ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1]) 2
    exceptionalF4State3 exceptionalF4State4 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_03
    exceptional_f4_fold_0_3

private theorem exceptional_f4_fold_0_1 :
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1]).foldr (demazureFin cartanF4)
      exceptionalF4State2 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1]) ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2]) 1
    exceptionalF4State2 exceptionalF4State3 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_02
    exceptional_f4_fold_0_2

private theorem exceptional_f4_fold_0_0 :
    (wordF4).foldr (demazureFin cartanF4)
      exceptionalF4State1 = exceptionalF4State16 := by
  exact exceptional_fold_join (demazureFin cartanF4)
    (wordF4) ([0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1]) 0
    exceptionalF4State1 exceptionalF4State2 exceptionalF4State16
    (by decide +kernel) exceptional_f4_step_01
    exceptional_f4_fold_0_1

theorem exceptional_f4_cycle_0 :
    demazureStep cartanF4 thetaF4 wordF4 (exceptionalSeed thetaF4) = exceptionalF4State16 := by
  exact exceptional_step_of_fold cartanF4 thetaF4 wordF4
    (exceptionalSeed thetaF4) exceptionalF4State1 exceptionalF4State16
    exceptional_f4_step_00 exceptional_f4_fold_0_0

theorem exceptional_f4_char_one :
    demazureChar cartanF4 thetaF4 wordF4 1 = exceptionalF4State16 :=
  exceptional_character_one cartanF4 thetaF4 wordF4 _ exceptional_f4_cycle_0

end VOA.DeligneAudit.DeligneCharacter

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE600
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE601
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE602
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE603
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE604
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE605
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE606
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE607
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE608
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE609
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE610
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE611
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE612
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE613
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE614
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE615
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE616
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE617
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE618
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE619
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE620
import VOA.DeligneAudit.DeligneCharacterExceptionalStepE621

/-! Certified full algorithm outputs assembled opaquely from single-operator facts. -/
namespace VOA.DeligneAudit.DeligneCharacter

private theorem exceptional_e6_fold_0_21 :
    ([]).foldr (demazureFin cartanE6)
      exceptionalE6State22 = exceptionalE6State22 := by
  rfl

private theorem exceptional_e6_fold_0_20 :
    ([1]).foldr (demazureFin cartanE6)
      exceptionalE6State21 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1]) ([]) 1
    exceptionalE6State21 exceptionalE6State22 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_21
    exceptional_e6_fold_0_21

private theorem exceptional_e6_fold_0_19 :
    ([1, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State20 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3]) ([1]) 3
    exceptionalE6State20 exceptionalE6State21 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_20
    exceptional_e6_fold_0_20

private theorem exceptional_e6_fold_0_18 :
    ([1, 3, 4]).foldr (demazureFin cartanE6)
      exceptionalE6State19 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4]) ([1, 3]) 4
    exceptionalE6State19 exceptionalE6State20 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_19
    exceptional_e6_fold_0_19

private theorem exceptional_e6_fold_0_17 :
    ([1, 3, 4, 2]).foldr (demazureFin cartanE6)
      exceptionalE6State18 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2]) ([1, 3, 4]) 2
    exceptionalE6State18 exceptionalE6State19 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_18
    exceptional_e6_fold_0_18

private theorem exceptional_e6_fold_0_16 :
    ([1, 3, 4, 2, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State17 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3]) ([1, 3, 4, 2]) 3
    exceptionalE6State17 exceptionalE6State18 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_17
    exceptional_e6_fold_0_17

private theorem exceptional_e6_fold_0_15 :
    ([1, 3, 4, 2, 3, 0]).foldr (demazureFin cartanE6)
      exceptionalE6State16 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0]) ([1, 3, 4, 2, 3]) 0
    exceptionalE6State16 exceptionalE6State17 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_16
    exceptional_e6_fold_0_16

private theorem exceptional_e6_fold_0_14 :
    ([1, 3, 4, 2, 3, 0, 2]).foldr (demazureFin cartanE6)
      exceptionalE6State15 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2]) ([1, 3, 4, 2, 3, 0]) 2
    exceptionalE6State15 exceptionalE6State16 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_15
    exceptional_e6_fold_0_15

private theorem exceptional_e6_fold_0_13 :
    ([1, 3, 4, 2, 3, 0, 2, 1]).foldr (demazureFin cartanE6)
      exceptionalE6State14 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1]) ([1, 3, 4, 2, 3, 0, 2]) 1
    exceptionalE6State14 exceptionalE6State15 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_14
    exceptional_e6_fold_0_14

private theorem exceptional_e6_fold_0_12 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State13 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3]) ([1, 3, 4, 2, 3, 0, 2, 1]) 3
    exceptionalE6State13 exceptionalE6State14 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_13
    exceptional_e6_fold_0_13

private theorem exceptional_e6_fold_0_11 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4]).foldr (demazureFin cartanE6)
      exceptionalE6State12 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4]) ([1, 3, 4, 2, 3, 0, 2, 1, 3]) 4
    exceptionalE6State12 exceptionalE6State13 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_12
    exceptional_e6_fold_0_12

private theorem exceptional_e6_fold_0_10 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]).foldr (demazureFin cartanE6)
      exceptionalE6State11 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4]) 5
    exceptionalE6State11 exceptionalE6State12 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_11
    exceptional_e6_fold_0_11

private theorem exceptional_e6_fold_0_9 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4]).foldr (demazureFin cartanE6)
      exceptionalE6State10 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4]) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]) 4
    exceptionalE6State10 exceptionalE6State11 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_10
    exceptional_e6_fold_0_10

private theorem exceptional_e6_fold_0_8 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State9 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3]) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4]) 3
    exceptionalE6State9 exceptionalE6State10 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_09
    exceptional_e6_fold_0_9

private theorem exceptional_e6_fold_0_7 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2]).foldr (demazureFin cartanE6)
      exceptionalE6State8 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2]) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3]) 2
    exceptionalE6State8 exceptionalE6State9 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_08
    exceptional_e6_fold_0_8

private theorem exceptional_e6_fold_0_6 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1]).foldr (demazureFin cartanE6)
      exceptionalE6State7 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1]) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2]) 1
    exceptionalE6State7 exceptionalE6State8 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_07
    exceptional_e6_fold_0_7

private theorem exceptional_e6_fold_0_5 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State6 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3])
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1]) 3
    exceptionalE6State6 exceptionalE6State7 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_06
    exceptional_e6_fold_0_6

private theorem exceptional_e6_fold_0_4 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4]).foldr (demazureFin cartanE6)
      exceptionalE6State5 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4])
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3]) 4
    exceptionalE6State5 exceptionalE6State6 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_05
    exceptional_e6_fold_0_5

private theorem exceptional_e6_fold_0_3 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0]).foldr (demazureFin cartanE6)
      exceptionalE6State4 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0])
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4]) 0
    exceptionalE6State4 exceptionalE6State5 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_04
    exceptional_e6_fold_0_4

private theorem exceptional_e6_fold_0_2 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2]).foldr (demazureFin cartanE6)
      exceptionalE6State3 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2])
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0]) 2
    exceptionalE6State3 exceptionalE6State4 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_03
    exceptional_e6_fold_0_3

private theorem exceptional_e6_fold_0_1 :
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]).foldr (demazureFin cartanE6)
      exceptionalE6State2 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3])
    ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2]) 3
    exceptionalE6State2 exceptionalE6State3 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_02
    exceptional_e6_fold_0_2

private theorem exceptional_e6_fold_0_0 :
    (wordE6).foldr (demazureFin cartanE6)
      exceptionalE6State1 = exceptionalE6State22 := by
  exact exceptional_fold_join (demazureFin cartanE6)
    (wordE6) ([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]) 1
    exceptionalE6State1 exceptionalE6State2 exceptionalE6State22
    (by decide +kernel) exceptional_e6_step_01
    exceptional_e6_fold_0_1

theorem exceptional_e6_cycle_0 :
    demazureStep cartanE6 thetaE6 wordE6 (exceptionalSeed thetaE6) = exceptionalE6State22 := by
  exact exceptional_step_of_fold cartanE6 thetaE6 wordE6
    (exceptionalSeed thetaE6) exceptionalE6State1 exceptionalE6State22
    exceptional_e6_step_00 exceptional_e6_fold_0_0

theorem exceptional_e6_char_one :
    demazureChar cartanE6 thetaE6 wordE6 1 = exceptionalE6State22 :=
  exceptional_character_one cartanE6 thetaE6 wordE6 _ exceptional_e6_cycle_0

end VOA.DeligneAudit.DeligneCharacter

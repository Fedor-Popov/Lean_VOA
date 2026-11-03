/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG200
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG201
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG202
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG203
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG204
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG205
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG206
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG207
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG208
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG209
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG210
import VOA.DeligneAudit.DeligneCharacterExceptionalStepG211

/-! Certified full algorithm outputs assembled opaquely from single-operator facts. -/
namespace VOA.DeligneAudit.DeligneCharacter

private theorem exceptional_g2_fold_0_5 :
    ([]).foldr (demazureFin cartanG2)
      exceptionalG2State6 = exceptionalG2State6 := by
  rfl

private theorem exceptional_g2_fold_0_4 :
    ([1]).foldr (demazureFin cartanG2)
      exceptionalG2State5 = exceptionalG2State6 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1]) ([]) 1
    exceptionalG2State5 exceptionalG2State6 exceptionalG2State6
    (by decide +kernel) exceptional_g2_step_05
    exceptional_g2_fold_0_5

private theorem exceptional_g2_fold_0_3 :
    ([1, 0]).foldr (demazureFin cartanG2)
      exceptionalG2State4 = exceptionalG2State6 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0]) ([1]) 0
    exceptionalG2State4 exceptionalG2State5 exceptionalG2State6
    (by decide +kernel) exceptional_g2_step_04
    exceptional_g2_fold_0_4

private theorem exceptional_g2_fold_0_2 :
    ([1, 0, 1]).foldr (demazureFin cartanG2)
      exceptionalG2State3 = exceptionalG2State6 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0, 1]) ([1, 0]) 1
    exceptionalG2State3 exceptionalG2State4 exceptionalG2State6
    (by decide +kernel) exceptional_g2_step_03
    exceptional_g2_fold_0_3

private theorem exceptional_g2_fold_0_1 :
    ([1, 0, 1, 0]).foldr (demazureFin cartanG2)
      exceptionalG2State2 = exceptionalG2State6 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0, 1, 0]) ([1, 0, 1]) 0
    exceptionalG2State2 exceptionalG2State3 exceptionalG2State6
    (by decide +kernel) exceptional_g2_step_02
    exceptional_g2_fold_0_2

private theorem exceptional_g2_fold_0_0 :
    (wordG2).foldr (demazureFin cartanG2)
      exceptionalG2State1 = exceptionalG2State6 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    (wordG2) ([1, 0, 1, 0]) 1
    exceptionalG2State1 exceptionalG2State2 exceptionalG2State6
    (by decide +kernel) exceptional_g2_step_01
    exceptional_g2_fold_0_1

theorem exceptional_g2_cycle_0 :
    demazureStep cartanG2 thetaG2 wordG2 (exceptionalSeed thetaG2) = exceptionalG2State6 := by
  exact exceptional_step_of_fold cartanG2 thetaG2 wordG2
    (exceptionalSeed thetaG2) exceptionalG2State1 exceptionalG2State6
    exceptional_g2_step_00 exceptional_g2_fold_0_0

private theorem exceptional_g2_fold_1_5 :
    ([]).foldr (demazureFin cartanG2)
      exceptionalG2State12 = exceptionalG2State12 := by
  rfl

private theorem exceptional_g2_fold_1_4 :
    ([1]).foldr (demazureFin cartanG2)
      exceptionalG2State11 = exceptionalG2State12 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1]) ([]) 1
    exceptionalG2State11 exceptionalG2State12 exceptionalG2State12
    (by decide +kernel) exceptional_g2_step_11
    exceptional_g2_fold_1_5

private theorem exceptional_g2_fold_1_3 :
    ([1, 0]).foldr (demazureFin cartanG2)
      exceptionalG2State10 = exceptionalG2State12 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0]) ([1]) 0
    exceptionalG2State10 exceptionalG2State11 exceptionalG2State12
    (by decide +kernel) exceptional_g2_step_10
    exceptional_g2_fold_1_4

private theorem exceptional_g2_fold_1_2 :
    ([1, 0, 1]).foldr (demazureFin cartanG2)
      exceptionalG2State9 = exceptionalG2State12 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0, 1]) ([1, 0]) 1
    exceptionalG2State9 exceptionalG2State10 exceptionalG2State12
    (by decide +kernel) exceptional_g2_step_09
    exceptional_g2_fold_1_3

private theorem exceptional_g2_fold_1_1 :
    ([1, 0, 1, 0]).foldr (demazureFin cartanG2)
      exceptionalG2State8 = exceptionalG2State12 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    ([1, 0, 1, 0]) ([1, 0, 1]) 0
    exceptionalG2State8 exceptionalG2State9 exceptionalG2State12
    (by decide +kernel) exceptional_g2_step_08
    exceptional_g2_fold_1_2

private theorem exceptional_g2_fold_1_0 :
    (wordG2).foldr (demazureFin cartanG2)
      exceptionalG2State7 = exceptionalG2State12 := by
  exact exceptional_fold_join (demazureFin cartanG2)
    (wordG2) ([1, 0, 1, 0]) 1
    exceptionalG2State7 exceptionalG2State8 exceptionalG2State12
    (by decide +kernel) exceptional_g2_step_07
    exceptional_g2_fold_1_1

theorem exceptional_g2_cycle_1 :
    demazureStep cartanG2 thetaG2 wordG2 exceptionalG2State6 = exceptionalG2State12 := by
  exact exceptional_step_of_fold cartanG2 thetaG2 wordG2
    exceptionalG2State6 exceptionalG2State7 exceptionalG2State12
    exceptional_g2_step_06 exceptional_g2_fold_1_0

theorem exceptional_g2_char_one :
    demazureChar cartanG2 thetaG2 wordG2 1 = exceptionalG2State6 :=
  exceptional_character_one cartanG2 thetaG2 wordG2 _ exceptional_g2_cycle_0

theorem exceptional_g2_char_two :
    demazureChar cartanG2 thetaG2 wordG2 2 = exceptionalG2State12 :=
  exceptional_character_two cartanG2 thetaG2 wordG2 _ _
    exceptional_g2_cycle_0 exceptional_g2_cycle_1

end VOA.DeligneAudit.DeligneCharacter

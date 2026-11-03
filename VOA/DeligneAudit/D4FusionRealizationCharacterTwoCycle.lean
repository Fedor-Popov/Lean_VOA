import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep00
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep01
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep02
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep03
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep04
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep05
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep06
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep07
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep08
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoStep09
import VOA.DeligneAudit.DeligneCharacterExceptionalComputation

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Opaque fold composition avoids recomputing the closed Demazure algorithm. -/
theorem first_step_of_char (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (middle : LPoly) (h : demazureChar A theta word 1 = middle) :
    demazureStep A theta word (exceptionalSeed theta) = middle := h

private theorem fold10 :
    ([] : List ℕ).foldr (demazureFin cartan) state10 = state10 := rfl

private theorem fold09 :
    ([1]).foldr (demazureFin cartan) state09 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1]) ([]) 1
    state09 state10 state10 (by decide +kernel) step09 fold10

private theorem fold08 :
    ([1, 0]).foldr (demazureFin cartan) state08 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0]) ([1]) 0
    state08 state09 state10 (by decide +kernel) step08 fold09

private theorem fold07 :
    ([1, 0, 2]).foldr (demazureFin cartan) state07 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2]) ([1, 0]) 2
    state07 state08 state10 (by decide +kernel) step07 fold08

private theorem fold06 :
    ([1, 0, 2, 1]).foldr (demazureFin cartan) state06 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2, 1]) ([1, 0, 2]) 1
    state06 state07 state10 (by decide +kernel) step06 fold07

private theorem fold05 :
    ([1, 0, 2, 1, 3]).foldr (demazureFin cartan) state05 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2, 1, 3]) ([1, 0, 2, 1]) 3
    state05 state06 state10 (by decide +kernel) step05 fold06

private theorem fold04 :
    ([1, 0, 2, 1, 3, 1]).foldr (demazureFin cartan) state04 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2, 1, 3, 1]) ([1, 0, 2, 1, 3]) 1
    state04 state05 state10 (by decide +kernel) step04 fold05

private theorem fold03 :
    ([1, 0, 2, 1, 3, 1, 2]).foldr (demazureFin cartan) state03 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2, 1, 3, 1, 2]) ([1, 0, 2, 1, 3, 1]) 2
    state03 state04 state10 (by decide +kernel) step03 fold04

private theorem fold02 :
    ([1, 0, 2, 1, 3, 1, 2, 0]).foldr (demazureFin cartan) state02 = state10 :=
  exceptional_fold_join (demazureFin cartan) ([1, 0, 2, 1, 3, 1, 2, 0]) ([1, 0, 2, 1, 3, 1, 2]) 0
    state02 state03 state10 (by decide +kernel) step02 fold03

private theorem fold01 :
    (word).foldr (demazureFin cartan) state01 = state10 :=
  exceptional_fold_join (demazureFin cartan) (word) ([1, 0, 2, 1, 3, 1, 2, 0]) 1
    state01 state02 state10 (by decide +kernel) step01 fold02

theorem cycle_two : demazureStep cartan theta word state00 = state10 :=
  exceptional_step_of_fold cartan theta word state00 state01 state10 step00 fold01

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.cycle_two

import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0600
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0601
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0602
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0603
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0604
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0605
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0606
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0607

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix06_29 :
    rawPush op06 rest06_29 [] = acc06_29 := rfl

private theorem suffix06_28 :
    rawPush op06 rest06_28 [] = acc06_28 := by
  rw [rest06_28, rawPush_append, suffix06_29, push06_28]

private theorem suffix06_27 :
    rawPush op06 rest06_27 [] = acc06_27 := by
  rw [rest06_27, rawPush_append, suffix06_28, push06_27]

private theorem suffix06_26 :
    rawPush op06 rest06_26 [] = acc06_26 := by
  rw [rest06_26, rawPush_append, suffix06_27, push06_26]

private theorem suffix06_25 :
    rawPush op06 rest06_25 [] = acc06_25 := by
  rw [rest06_25, rawPush_append, suffix06_26, push06_25]

private theorem suffix06_24 :
    rawPush op06 rest06_24 [] = acc06_24 := by
  rw [rest06_24, rawPush_append, suffix06_25, push06_24]

private theorem suffix06_23 :
    rawPush op06 rest06_23 [] = acc06_23 := by
  rw [rest06_23, rawPush_append, suffix06_24, push06_23]

private theorem suffix06_22 :
    rawPush op06 rest06_22 [] = acc06_22 := by
  rw [rest06_22, rawPush_append, suffix06_23, push06_22]

private theorem suffix06_21 :
    rawPush op06 rest06_21 [] = acc06_21 := by
  rw [rest06_21, rawPush_append, suffix06_22, push06_21]

private theorem suffix06_20 :
    rawPush op06 rest06_20 [] = acc06_20 := by
  rw [rest06_20, rawPush_append, suffix06_21, push06_20]

private theorem suffix06_19 :
    rawPush op06 rest06_19 [] = acc06_19 := by
  rw [rest06_19, rawPush_append, suffix06_20, push06_19]

private theorem suffix06_18 :
    rawPush op06 rest06_18 [] = acc06_18 := by
  rw [rest06_18, rawPush_append, suffix06_19, push06_18]

private theorem suffix06_17 :
    rawPush op06 rest06_17 [] = acc06_17 := by
  rw [rest06_17, rawPush_append, suffix06_18, push06_17]

private theorem suffix06_16 :
    rawPush op06 rest06_16 [] = acc06_16 := by
  rw [rest06_16, rawPush_append, suffix06_17, push06_16]

private theorem suffix06_15 :
    rawPush op06 rest06_15 [] = acc06_15 := by
  rw [rest06_15, rawPush_append, suffix06_16, push06_15]

private theorem suffix06_14 :
    rawPush op06 rest06_14 [] = acc06_14 := by
  rw [rest06_14, rawPush_append, suffix06_15, push06_14]

private theorem suffix06_13 :
    rawPush op06 rest06_13 [] = acc06_13 := by
  rw [rest06_13, rawPush_append, suffix06_14, push06_13]

private theorem suffix06_12 :
    rawPush op06 rest06_12 [] = acc06_12 := by
  rw [rest06_12, rawPush_append, suffix06_13, push06_12]

private theorem suffix06_11 :
    rawPush op06 rest06_11 [] = acc06_11 := by
  rw [rest06_11, rawPush_append, suffix06_12, push06_11]

private theorem suffix06_10 :
    rawPush op06 rest06_10 [] = acc06_10 := by
  rw [rest06_10, rawPush_append, suffix06_11, push06_10]

private theorem suffix06_09 :
    rawPush op06 rest06_09 [] = acc06_09 := by
  rw [rest06_09, rawPush_append, suffix06_10, push06_09]

private theorem suffix06_08 :
    rawPush op06 rest06_08 [] = acc06_08 := by
  rw [rest06_08, rawPush_append, suffix06_09, push06_08]

private theorem suffix06_07 :
    rawPush op06 rest06_07 [] = acc06_07 := by
  rw [rest06_07, rawPush_append, suffix06_08, push06_07]

private theorem suffix06_06 :
    rawPush op06 rest06_06 [] = acc06_06 := by
  rw [rest06_06, rawPush_append, suffix06_07, push06_06]

private theorem suffix06_05 :
    rawPush op06 rest06_05 [] = acc06_05 := by
  rw [rest06_05, rawPush_append, suffix06_06, push06_05]

private theorem suffix06_04 :
    rawPush op06 rest06_04 [] = acc06_04 := by
  rw [rest06_04, rawPush_append, suffix06_05, push06_04]

private theorem suffix06_03 :
    rawPush op06 rest06_03 [] = acc06_03 := by
  rw [rest06_03, rawPush_append, suffix06_04, push06_03]

private theorem suffix06_02 :
    rawPush op06 rest06_02 [] = acc06_02 := by
  rw [rest06_02, rawPush_append, suffix06_03, push06_02]

private theorem suffix06_01 :
    rawPush op06 rest06_01 [] = acc06_01 := by
  rw [rest06_01, rawPush_append, suffix06_02, push06_01]

private theorem suffix06_00 :
    rawPush op06 rest06_00 [] = acc06_00 := by
  rw [rest06_00, rawPush_append, suffix06_01, push06_00]

private theorem raw06 : rawPush op06 state06 [] = acc06_00 := by
  change rawPush op06 rest06_00 [] = acc06_00
  exact suffix06_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter06 : acc06_00.filter (fun t => t.2 ≠ 0) = state07 := by
  decide +kernel

theorem step06 : demazureFin cartan 1 state06 = state07 :=
  finish_fin cartan 1 _ _ _ raw06 filter06

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step06

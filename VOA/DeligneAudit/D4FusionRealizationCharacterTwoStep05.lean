import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0500
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0501
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0502
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0503
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0504

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix05_17 :
    rawPush op05 rest05_17 [] = acc05_17 := rfl

private theorem suffix05_16 :
    rawPush op05 rest05_16 [] = acc05_16 := by
  rw [rest05_16, rawPush_append, suffix05_17, push05_16]

private theorem suffix05_15 :
    rawPush op05 rest05_15 [] = acc05_15 := by
  rw [rest05_15, rawPush_append, suffix05_16, push05_15]

private theorem suffix05_14 :
    rawPush op05 rest05_14 [] = acc05_14 := by
  rw [rest05_14, rawPush_append, suffix05_15, push05_14]

private theorem suffix05_13 :
    rawPush op05 rest05_13 [] = acc05_13 := by
  rw [rest05_13, rawPush_append, suffix05_14, push05_13]

private theorem suffix05_12 :
    rawPush op05 rest05_12 [] = acc05_12 := by
  rw [rest05_12, rawPush_append, suffix05_13, push05_12]

private theorem suffix05_11 :
    rawPush op05 rest05_11 [] = acc05_11 := by
  rw [rest05_11, rawPush_append, suffix05_12, push05_11]

private theorem suffix05_10 :
    rawPush op05 rest05_10 [] = acc05_10 := by
  rw [rest05_10, rawPush_append, suffix05_11, push05_10]

private theorem suffix05_09 :
    rawPush op05 rest05_09 [] = acc05_09 := by
  rw [rest05_09, rawPush_append, suffix05_10, push05_09]

private theorem suffix05_08 :
    rawPush op05 rest05_08 [] = acc05_08 := by
  rw [rest05_08, rawPush_append, suffix05_09, push05_08]

private theorem suffix05_07 :
    rawPush op05 rest05_07 [] = acc05_07 := by
  rw [rest05_07, rawPush_append, suffix05_08, push05_07]

private theorem suffix05_06 :
    rawPush op05 rest05_06 [] = acc05_06 := by
  rw [rest05_06, rawPush_append, suffix05_07, push05_06]

private theorem suffix05_05 :
    rawPush op05 rest05_05 [] = acc05_05 := by
  rw [rest05_05, rawPush_append, suffix05_06, push05_05]

private theorem suffix05_04 :
    rawPush op05 rest05_04 [] = acc05_04 := by
  rw [rest05_04, rawPush_append, suffix05_05, push05_04]

private theorem suffix05_03 :
    rawPush op05 rest05_03 [] = acc05_03 := by
  rw [rest05_03, rawPush_append, suffix05_04, push05_03]

private theorem suffix05_02 :
    rawPush op05 rest05_02 [] = acc05_02 := by
  rw [rest05_02, rawPush_append, suffix05_03, push05_02]

private theorem suffix05_01 :
    rawPush op05 rest05_01 [] = acc05_01 := by
  rw [rest05_01, rawPush_append, suffix05_02, push05_01]

private theorem suffix05_00 :
    rawPush op05 rest05_00 [] = acc05_00 := by
  rw [rest05_00, rawPush_append, suffix05_01, push05_00]

private theorem raw05 : rawPush op05 state05 [] = acc05_00 := by
  change rawPush op05 rest05_00 [] = acc05_00
  exact suffix05_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter05 : acc05_00.filter (fun t => t.2 ≠ 0) = state06 := by
  decide +kernel

theorem step05 : demazureFin cartan 3 state05 = state06 :=
  finish_fin cartan 3 _ _ _ raw05 filter05

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step05

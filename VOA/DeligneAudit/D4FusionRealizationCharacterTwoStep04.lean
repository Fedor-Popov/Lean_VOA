import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0400
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0401
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0402
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0403

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix04_15 :
    rawPush op04 rest04_15 [] = acc04_15 := rfl

private theorem suffix04_14 :
    rawPush op04 rest04_14 [] = acc04_14 := by
  rw [rest04_14, rawPush_append, suffix04_15, push04_14]

private theorem suffix04_13 :
    rawPush op04 rest04_13 [] = acc04_13 := by
  rw [rest04_13, rawPush_append, suffix04_14, push04_13]

private theorem suffix04_12 :
    rawPush op04 rest04_12 [] = acc04_12 := by
  rw [rest04_12, rawPush_append, suffix04_13, push04_12]

private theorem suffix04_11 :
    rawPush op04 rest04_11 [] = acc04_11 := by
  rw [rest04_11, rawPush_append, suffix04_12, push04_11]

private theorem suffix04_10 :
    rawPush op04 rest04_10 [] = acc04_10 := by
  rw [rest04_10, rawPush_append, suffix04_11, push04_10]

private theorem suffix04_09 :
    rawPush op04 rest04_09 [] = acc04_09 := by
  rw [rest04_09, rawPush_append, suffix04_10, push04_09]

private theorem suffix04_08 :
    rawPush op04 rest04_08 [] = acc04_08 := by
  rw [rest04_08, rawPush_append, suffix04_09, push04_08]

private theorem suffix04_07 :
    rawPush op04 rest04_07 [] = acc04_07 := by
  rw [rest04_07, rawPush_append, suffix04_08, push04_07]

private theorem suffix04_06 :
    rawPush op04 rest04_06 [] = acc04_06 := by
  rw [rest04_06, rawPush_append, suffix04_07, push04_06]

private theorem suffix04_05 :
    rawPush op04 rest04_05 [] = acc04_05 := by
  rw [rest04_05, rawPush_append, suffix04_06, push04_05]

private theorem suffix04_04 :
    rawPush op04 rest04_04 [] = acc04_04 := by
  rw [rest04_04, rawPush_append, suffix04_05, push04_04]

private theorem suffix04_03 :
    rawPush op04 rest04_03 [] = acc04_03 := by
  rw [rest04_03, rawPush_append, suffix04_04, push04_03]

private theorem suffix04_02 :
    rawPush op04 rest04_02 [] = acc04_02 := by
  rw [rest04_02, rawPush_append, suffix04_03, push04_02]

private theorem suffix04_01 :
    rawPush op04 rest04_01 [] = acc04_01 := by
  rw [rest04_01, rawPush_append, suffix04_02, push04_01]

private theorem suffix04_00 :
    rawPush op04 rest04_00 [] = acc04_00 := by
  rw [rest04_00, rawPush_append, suffix04_01, push04_00]

private theorem raw04 : rawPush op04 state04 [] = acc04_00 := by
  change rawPush op04 rest04_00 [] = acc04_00
  exact suffix04_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter04 : acc04_00.filter (fun t => t.2 ≠ 0) = state05 := by
  decide +kernel

theorem step04 : demazureFin cartan 1 state04 = state05 :=
  finish_fin cartan 1 _ _ _ raw04 filter04

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step04

import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0300
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0301
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0302

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix03_11 :
    rawPush op03 rest03_11 [] = acc03_11 := rfl

private theorem suffix03_10 :
    rawPush op03 rest03_10 [] = acc03_10 := by
  rw [rest03_10, rawPush_append, suffix03_11, push03_10]

private theorem suffix03_09 :
    rawPush op03 rest03_09 [] = acc03_09 := by
  rw [rest03_09, rawPush_append, suffix03_10, push03_09]

private theorem suffix03_08 :
    rawPush op03 rest03_08 [] = acc03_08 := by
  rw [rest03_08, rawPush_append, suffix03_09, push03_08]

private theorem suffix03_07 :
    rawPush op03 rest03_07 [] = acc03_07 := by
  rw [rest03_07, rawPush_append, suffix03_08, push03_07]

private theorem suffix03_06 :
    rawPush op03 rest03_06 [] = acc03_06 := by
  rw [rest03_06, rawPush_append, suffix03_07, push03_06]

private theorem suffix03_05 :
    rawPush op03 rest03_05 [] = acc03_05 := by
  rw [rest03_05, rawPush_append, suffix03_06, push03_05]

private theorem suffix03_04 :
    rawPush op03 rest03_04 [] = acc03_04 := by
  rw [rest03_04, rawPush_append, suffix03_05, push03_04]

private theorem suffix03_03 :
    rawPush op03 rest03_03 [] = acc03_03 := by
  rw [rest03_03, rawPush_append, suffix03_04, push03_03]

private theorem suffix03_02 :
    rawPush op03 rest03_02 [] = acc03_02 := by
  rw [rest03_02, rawPush_append, suffix03_03, push03_02]

private theorem suffix03_01 :
    rawPush op03 rest03_01 [] = acc03_01 := by
  rw [rest03_01, rawPush_append, suffix03_02, push03_01]

private theorem suffix03_00 :
    rawPush op03 rest03_00 [] = acc03_00 := by
  rw [rest03_00, rawPush_append, suffix03_01, push03_00]

private theorem raw03 : rawPush op03 state03 [] = acc03_00 := by
  change rawPush op03 rest03_00 [] = acc03_00
  exact suffix03_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter03 : acc03_00.filter (fun t => t.2 ≠ 0) = state04 := by
  decide +kernel

theorem step03 : demazureFin cartan 2 state03 = state04 :=
  finish_fin cartan 2 _ _ _ raw03 filter03

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step03

import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0200
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0201
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0202

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix02_09 :
    rawPush op02 rest02_09 [] = acc02_09 := rfl

private theorem suffix02_08 :
    rawPush op02 rest02_08 [] = acc02_08 := by
  rw [rest02_08, rawPush_append, suffix02_09, push02_08]

private theorem suffix02_07 :
    rawPush op02 rest02_07 [] = acc02_07 := by
  rw [rest02_07, rawPush_append, suffix02_08, push02_07]

private theorem suffix02_06 :
    rawPush op02 rest02_06 [] = acc02_06 := by
  rw [rest02_06, rawPush_append, suffix02_07, push02_06]

private theorem suffix02_05 :
    rawPush op02 rest02_05 [] = acc02_05 := by
  rw [rest02_05, rawPush_append, suffix02_06, push02_05]

private theorem suffix02_04 :
    rawPush op02 rest02_04 [] = acc02_04 := by
  rw [rest02_04, rawPush_append, suffix02_05, push02_04]

private theorem suffix02_03 :
    rawPush op02 rest02_03 [] = acc02_03 := by
  rw [rest02_03, rawPush_append, suffix02_04, push02_03]

private theorem suffix02_02 :
    rawPush op02 rest02_02 [] = acc02_02 := by
  rw [rest02_02, rawPush_append, suffix02_03, push02_02]

private theorem suffix02_01 :
    rawPush op02 rest02_01 [] = acc02_01 := by
  rw [rest02_01, rawPush_append, suffix02_02, push02_01]

private theorem suffix02_00 :
    rawPush op02 rest02_00 [] = acc02_00 := by
  rw [rest02_00, rawPush_append, suffix02_01, push02_00]

private theorem raw02 : rawPush op02 state02 [] = acc02_00 := by
  change rawPush op02 rest02_00 [] = acc02_00
  exact suffix02_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter02 : acc02_00.filter (fun t => t.2 ≠ 0) = state03 := by
  decide +kernel

theorem step02 : demazureFin cartan 0 state02 = state03 :=
  finish_fin cartan 0 _ _ _ raw02 filter02

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step02

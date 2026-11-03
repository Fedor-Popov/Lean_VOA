import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0100
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0101

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix01_07 :
    rawPush op01 rest01_07 [] = acc01_07 := rfl

private theorem suffix01_06 :
    rawPush op01 rest01_06 [] = acc01_06 := by
  rw [rest01_06, rawPush_append, suffix01_07, push01_06]

private theorem suffix01_05 :
    rawPush op01 rest01_05 [] = acc01_05 := by
  rw [rest01_05, rawPush_append, suffix01_06, push01_05]

private theorem suffix01_04 :
    rawPush op01 rest01_04 [] = acc01_04 := by
  rw [rest01_04, rawPush_append, suffix01_05, push01_04]

private theorem suffix01_03 :
    rawPush op01 rest01_03 [] = acc01_03 := by
  rw [rest01_03, rawPush_append, suffix01_04, push01_03]

private theorem suffix01_02 :
    rawPush op01 rest01_02 [] = acc01_02 := by
  rw [rest01_02, rawPush_append, suffix01_03, push01_02]

private theorem suffix01_01 :
    rawPush op01 rest01_01 [] = acc01_01 := by
  rw [rest01_01, rawPush_append, suffix01_02, push01_01]

private theorem suffix01_00 :
    rawPush op01 rest01_00 [] = acc01_00 := by
  rw [rest01_00, rawPush_append, suffix01_01, push01_00]

private theorem raw01 : rawPush op01 state01 [] = acc01_00 := by
  change rawPush op01 rest01_00 [] = acc01_00
  exact suffix01_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter01 : acc01_00.filter (fun t => t.2 ≠ 0) = state02 := by
  decide +kernel

theorem step01 : demazureFin cartan 1 state01 = state02 :=
  finish_fin cartan 1 _ _ _ raw01 filter01

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step01

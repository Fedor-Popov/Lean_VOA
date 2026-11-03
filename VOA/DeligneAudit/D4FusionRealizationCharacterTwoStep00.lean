import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCheck0000

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

private theorem suffix00_04 :
    rawPush op00 rest00_04 [] = acc00_04 := rfl

private theorem suffix00_03 :
    rawPush op00 rest00_03 [] = acc00_03 := by
  rw [rest00_03, rawPush_append, suffix00_04, push00_03]

private theorem suffix00_02 :
    rawPush op00 rest00_02 [] = acc00_02 := by
  rw [rest00_02, rawPush_append, suffix00_03, push00_02]

private theorem suffix00_01 :
    rawPush op00 rest00_01 [] = acc00_01 := by
  rw [rest00_01, rawPush_append, suffix00_02, push00_01]

private theorem suffix00_00 :
    rawPush op00 rest00_00 [] = acc00_00 := by
  rw [rest00_00, rawPush_append, suffix00_01, push00_00]

private theorem raw00 : rawPush op00 state00 [] = acc00_00 := by
  change rawPush op00 rest00_00 [] = acc00_00
  exact suffix00_00

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
private theorem filter00 : acc00_00.filter (fun t => t.2 ≠ 0) = state01 := by
  decide +kernel

theorem step00 : demazureZero cartan theta state00 = state01 :=
  finish_zero cartan theta _ _ _ raw00 filter00

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.step00

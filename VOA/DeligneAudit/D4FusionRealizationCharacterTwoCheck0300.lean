import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData03

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_00 :
    rawPush op03 chunk03_00 acc03_01 = acc03_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_01 :
    rawPush op03 chunk03_01 acc03_02 = acc03_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_02 :
    rawPush op03 chunk03_02 acc03_03 = acc03_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_03 :
    rawPush op03 chunk03_03 acc03_04 = acc03_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

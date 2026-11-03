import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData03

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_08 :
    rawPush op03 chunk03_08 acc03_09 = acc03_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_09 :
    rawPush op03 chunk03_09 acc03_10 = acc03_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_10 :
    rawPush op03 chunk03_10 acc03_11 = acc03_10 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

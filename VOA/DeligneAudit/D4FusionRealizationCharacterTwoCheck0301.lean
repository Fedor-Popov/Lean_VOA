import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData03

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_04 :
    rawPush op03 chunk03_04 acc03_05 = acc03_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_05 :
    rawPush op03 chunk03_05 acc03_06 = acc03_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_06 :
    rawPush op03 chunk03_06 acc03_07 = acc03_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push03_07 :
    rawPush op03 chunk03_07 acc03_08 = acc03_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

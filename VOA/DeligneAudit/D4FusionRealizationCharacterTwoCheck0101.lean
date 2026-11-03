import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData01

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_04 :
    rawPush op01 chunk01_04 acc01_05 = acc01_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_05 :
    rawPush op01 chunk01_05 acc01_06 = acc01_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_06 :
    rawPush op01 chunk01_06 acc01_07 = acc01_06 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

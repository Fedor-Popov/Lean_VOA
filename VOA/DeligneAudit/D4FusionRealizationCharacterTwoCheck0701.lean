import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_04 :
    rawPush op07 chunk07_04 acc07_05 = acc07_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_05 :
    rawPush op07 chunk07_05 acc07_06 = acc07_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_06 :
    rawPush op07 chunk07_06 acc07_07 = acc07_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_07 :
    rawPush op07 chunk07_07 acc07_08 = acc07_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

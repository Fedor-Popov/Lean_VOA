import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_08 :
    rawPush op07 chunk07_08 acc07_09 = acc07_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_09 :
    rawPush op07 chunk07_09 acc07_10 = acc07_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_10 :
    rawPush op07 chunk07_10 acc07_11 = acc07_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_11 :
    rawPush op07 chunk07_11 acc07_12 = acc07_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

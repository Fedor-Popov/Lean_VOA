import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_20 :
    rawPush op07 chunk07_20 acc07_21 = acc07_20 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_21 :
    rawPush op07 chunk07_21 acc07_22 = acc07_21 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_22 :
    rawPush op07 chunk07_22 acc07_23 = acc07_22 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_23 :
    rawPush op07 chunk07_23 acc07_24 = acc07_23 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

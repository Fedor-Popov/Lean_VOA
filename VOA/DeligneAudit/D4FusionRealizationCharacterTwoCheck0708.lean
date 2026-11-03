import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_32 :
    rawPush op07 chunk07_32 acc07_33 = acc07_32 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_33 :
    rawPush op07 chunk07_33 acc07_34 = acc07_33 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_34 :
    rawPush op07 chunk07_34 acc07_35 = acc07_34 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_35 :
    rawPush op07 chunk07_35 acc07_36 = acc07_35 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

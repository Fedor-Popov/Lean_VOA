import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_24 :
    rawPush op07 chunk07_24 acc07_25 = acc07_24 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_25 :
    rawPush op07 chunk07_25 acc07_26 = acc07_25 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_26 :
    rawPush op07 chunk07_26 acc07_27 = acc07_26 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_27 :
    rawPush op07 chunk07_27 acc07_28 = acc07_27 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

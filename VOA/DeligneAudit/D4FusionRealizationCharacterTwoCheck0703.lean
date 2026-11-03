import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_12 :
    rawPush op07 chunk07_12 acc07_13 = acc07_12 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_13 :
    rawPush op07 chunk07_13 acc07_14 = acc07_13 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_14 :
    rawPush op07 chunk07_14 acc07_15 = acc07_14 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_15 :
    rawPush op07 chunk07_15 acc07_16 = acc07_15 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

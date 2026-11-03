import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_16 :
    rawPush op07 chunk07_16 acc07_17 = acc07_16 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_17 :
    rawPush op07 chunk07_17 acc07_18 = acc07_17 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_18 :
    rawPush op07 chunk07_18 acc07_19 = acc07_18 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_19 :
    rawPush op07 chunk07_19 acc07_20 = acc07_19 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

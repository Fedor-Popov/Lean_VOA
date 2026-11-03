import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData07

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_00 :
    rawPush op07 chunk07_00 acc07_01 = acc07_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_01 :
    rawPush op07 chunk07_01 acc07_02 = acc07_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_02 :
    rawPush op07 chunk07_02 acc07_03 = acc07_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push07_03 :
    rawPush op07 chunk07_03 acc07_04 = acc07_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

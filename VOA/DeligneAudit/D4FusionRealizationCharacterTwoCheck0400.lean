import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData04

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_00 :
    rawPush op04 chunk04_00 acc04_01 = acc04_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_01 :
    rawPush op04 chunk04_01 acc04_02 = acc04_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_02 :
    rawPush op04 chunk04_02 acc04_03 = acc04_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_03 :
    rawPush op04 chunk04_03 acc04_04 = acc04_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

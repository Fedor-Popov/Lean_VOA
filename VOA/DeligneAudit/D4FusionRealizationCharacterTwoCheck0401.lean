import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData04

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_04 :
    rawPush op04 chunk04_04 acc04_05 = acc04_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_05 :
    rawPush op04 chunk04_05 acc04_06 = acc04_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_06 :
    rawPush op04 chunk04_06 acc04_07 = acc04_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_07 :
    rawPush op04 chunk04_07 acc04_08 = acc04_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

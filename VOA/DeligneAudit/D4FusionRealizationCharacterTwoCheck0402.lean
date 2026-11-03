import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData04

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_08 :
    rawPush op04 chunk04_08 acc04_09 = acc04_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_09 :
    rawPush op04 chunk04_09 acc04_10 = acc04_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_10 :
    rawPush op04 chunk04_10 acc04_11 = acc04_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_11 :
    rawPush op04 chunk04_11 acc04_12 = acc04_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

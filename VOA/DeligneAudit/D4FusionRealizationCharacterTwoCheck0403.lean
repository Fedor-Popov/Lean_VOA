import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData04

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_12 :
    rawPush op04 chunk04_12 acc04_13 = acc04_12 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_13 :
    rawPush op04 chunk04_13 acc04_14 = acc04_13 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push04_14 :
    rawPush op04 chunk04_14 acc04_15 = acc04_14 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_08 :
    rawPush op06 chunk06_08 acc06_09 = acc06_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_09 :
    rawPush op06 chunk06_09 acc06_10 = acc06_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_10 :
    rawPush op06 chunk06_10 acc06_11 = acc06_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_11 :
    rawPush op06 chunk06_11 acc06_12 = acc06_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

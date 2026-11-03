import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_20 :
    rawPush op06 chunk06_20 acc06_21 = acc06_20 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_21 :
    rawPush op06 chunk06_21 acc06_22 = acc06_21 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_22 :
    rawPush op06 chunk06_22 acc06_23 = acc06_22 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_23 :
    rawPush op06 chunk06_23 acc06_24 = acc06_23 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

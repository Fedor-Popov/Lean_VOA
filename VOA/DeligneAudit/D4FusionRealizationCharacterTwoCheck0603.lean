import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_12 :
    rawPush op06 chunk06_12 acc06_13 = acc06_12 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_13 :
    rawPush op06 chunk06_13 acc06_14 = acc06_13 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_14 :
    rawPush op06 chunk06_14 acc06_15 = acc06_14 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_15 :
    rawPush op06 chunk06_15 acc06_16 = acc06_15 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

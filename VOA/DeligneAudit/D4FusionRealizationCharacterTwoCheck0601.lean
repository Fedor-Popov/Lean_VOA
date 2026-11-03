import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_04 :
    rawPush op06 chunk06_04 acc06_05 = acc06_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_05 :
    rawPush op06 chunk06_05 acc06_06 = acc06_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_06 :
    rawPush op06 chunk06_06 acc06_07 = acc06_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_07 :
    rawPush op06 chunk06_07 acc06_08 = acc06_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

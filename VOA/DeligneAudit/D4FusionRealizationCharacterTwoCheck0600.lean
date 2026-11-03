import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_00 :
    rawPush op06 chunk06_00 acc06_01 = acc06_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_01 :
    rawPush op06 chunk06_01 acc06_02 = acc06_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_02 :
    rawPush op06 chunk06_02 acc06_03 = acc06_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_03 :
    rawPush op06 chunk06_03 acc06_04 = acc06_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_24 :
    rawPush op06 chunk06_24 acc06_25 = acc06_24 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_25 :
    rawPush op06 chunk06_25 acc06_26 = acc06_25 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_26 :
    rawPush op06 chunk06_26 acc06_27 = acc06_26 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_27 :
    rawPush op06 chunk06_27 acc06_28 = acc06_27 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

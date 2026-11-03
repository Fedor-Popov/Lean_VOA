import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData06

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_16 :
    rawPush op06 chunk06_16 acc06_17 = acc06_16 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_17 :
    rawPush op06 chunk06_17 acc06_18 = acc06_17 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_18 :
    rawPush op06 chunk06_18 acc06_19 = acc06_18 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push06_19 :
    rawPush op06 chunk06_19 acc06_20 = acc06_19 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

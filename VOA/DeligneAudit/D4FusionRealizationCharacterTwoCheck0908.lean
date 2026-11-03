import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData09

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_32 :
    rawPush op09 chunk09_32 acc09_33 = acc09_32 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_33 :
    rawPush op09 chunk09_33 acc09_34 = acc09_33 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_34 :
    rawPush op09 chunk09_34 acc09_35 = acc09_34 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_35 :
    rawPush op09 chunk09_35 acc09_36 = acc09_35 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

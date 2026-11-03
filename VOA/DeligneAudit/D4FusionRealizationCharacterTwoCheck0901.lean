import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData09

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_04 :
    rawPush op09 chunk09_04 acc09_05 = acc09_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_05 :
    rawPush op09 chunk09_05 acc09_06 = acc09_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_06 :
    rawPush op09 chunk09_06 acc09_07 = acc09_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_07 :
    rawPush op09 chunk09_07 acc09_08 = acc09_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

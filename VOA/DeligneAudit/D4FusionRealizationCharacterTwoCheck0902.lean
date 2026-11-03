import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData09

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_08 :
    rawPush op09 chunk09_08 acc09_09 = acc09_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_09 :
    rawPush op09 chunk09_09 acc09_10 = acc09_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_10 :
    rawPush op09 chunk09_10 acc09_11 = acc09_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_11 :
    rawPush op09 chunk09_11 acc09_12 = acc09_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

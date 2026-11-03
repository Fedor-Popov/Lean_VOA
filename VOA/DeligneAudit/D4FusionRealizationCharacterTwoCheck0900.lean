import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData09

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_00 :
    rawPush op09 chunk09_00 acc09_01 = acc09_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_01 :
    rawPush op09 chunk09_01 acc09_02 = acc09_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_02 :
    rawPush op09 chunk09_02 acc09_03 = acc09_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push09_03 :
    rawPush op09 chunk09_03 acc09_04 = acc09_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

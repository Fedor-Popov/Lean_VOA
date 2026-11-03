import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData00

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push00_00 :
    rawPush op00 chunk00_00 acc00_01 = acc00_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push00_01 :
    rawPush op00 chunk00_01 acc00_02 = acc00_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push00_02 :
    rawPush op00 chunk00_02 acc00_03 = acc00_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push00_03 :
    rawPush op00 chunk00_03 acc00_04 = acc00_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

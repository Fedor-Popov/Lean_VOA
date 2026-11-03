import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData01

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_00 :
    rawPush op01 chunk01_00 acc01_01 = acc01_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_01 :
    rawPush op01 chunk01_01 acc01_02 = acc01_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_02 :
    rawPush op01 chunk01_02 acc01_03 = acc01_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push01_03 :
    rawPush op01 chunk01_03 acc01_04 = acc01_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

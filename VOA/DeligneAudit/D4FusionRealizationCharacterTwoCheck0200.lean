import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData02

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_00 :
    rawPush op02 chunk02_00 acc02_01 = acc02_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_01 :
    rawPush op02 chunk02_01 acc02_02 = acc02_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_02 :
    rawPush op02 chunk02_02 acc02_03 = acc02_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_03 :
    rawPush op02 chunk02_03 acc02_04 = acc02_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

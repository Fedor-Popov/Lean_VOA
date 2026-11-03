import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData02

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_04 :
    rawPush op02 chunk02_04 acc02_05 = acc02_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_05 :
    rawPush op02 chunk02_05 acc02_06 = acc02_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_06 :
    rawPush op02 chunk02_06 acc02_07 = acc02_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push02_07 :
    rawPush op02 chunk02_07 acc02_08 = acc02_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

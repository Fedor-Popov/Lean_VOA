import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData05

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_04 :
    rawPush op05 chunk05_04 acc05_05 = acc05_04 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_05 :
    rawPush op05 chunk05_05 acc05_06 = acc05_05 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_06 :
    rawPush op05 chunk05_06 acc05_07 = acc05_06 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_07 :
    rawPush op05 chunk05_07 acc05_08 = acc05_07 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

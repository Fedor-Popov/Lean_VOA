import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData05

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_00 :
    rawPush op05 chunk05_00 acc05_01 = acc05_00 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_01 :
    rawPush op05 chunk05_01 acc05_02 = acc05_01 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_02 :
    rawPush op05 chunk05_02 acc05_03 = acc05_02 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_03 :
    rawPush op05 chunk05_03 acc05_04 = acc05_03 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

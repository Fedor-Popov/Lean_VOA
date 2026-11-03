import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData05

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_08 :
    rawPush op05 chunk05_08 acc05_09 = acc05_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_09 :
    rawPush op05 chunk05_09 acc05_10 = acc05_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_10 :
    rawPush op05 chunk05_10 acc05_11 = acc05_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_11 :
    rawPush op05 chunk05_11 acc05_12 = acc05_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

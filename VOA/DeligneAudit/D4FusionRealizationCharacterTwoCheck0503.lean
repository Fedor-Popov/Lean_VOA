import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData05

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_12 :
    rawPush op05 chunk05_12 acc05_13 = acc05_12 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_13 :
    rawPush op05 chunk05_13 acc05_14 = acc05_13 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_14 :
    rawPush op05 chunk05_14 acc05_15 = acc05_14 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push05_15 :
    rawPush op05 chunk05_15 acc05_16 = acc05_15 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

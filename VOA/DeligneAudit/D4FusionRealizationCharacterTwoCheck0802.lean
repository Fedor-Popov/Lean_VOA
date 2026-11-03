import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_08 :
    rawPush op08 chunk08_08 acc08_09 = acc08_08 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_09 :
    rawPush op08 chunk08_09 acc08_10 = acc08_09 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_10 :
    rawPush op08 chunk08_10 acc08_11 = acc08_10 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_11 :
    rawPush op08 chunk08_11 acc08_12 = acc08_11 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

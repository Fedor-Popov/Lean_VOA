import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_20 :
    rawPush op08 chunk08_20 acc08_21 = acc08_20 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_21 :
    rawPush op08 chunk08_21 acc08_22 = acc08_21 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_22 :
    rawPush op08 chunk08_22 acc08_23 = acc08_22 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_23 :
    rawPush op08 chunk08_23 acc08_24 = acc08_23 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

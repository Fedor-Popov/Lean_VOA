import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_32 :
    rawPush op08 chunk08_32 acc08_33 = acc08_32 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_33 :
    rawPush op08 chunk08_33 acc08_34 = acc08_33 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_34 :
    rawPush op08 chunk08_34 acc08_35 = acc08_34 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_35 :
    rawPush op08 chunk08_35 acc08_36 = acc08_35 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

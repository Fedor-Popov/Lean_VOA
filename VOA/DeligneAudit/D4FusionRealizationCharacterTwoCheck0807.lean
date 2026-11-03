import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_28 :
    rawPush op08 chunk08_28 acc08_29 = acc08_28 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_29 :
    rawPush op08 chunk08_29 acc08_30 = acc08_29 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_30 :
    rawPush op08 chunk08_30 acc08_31 = acc08_30 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_31 :
    rawPush op08 chunk08_31 acc08_32 = acc08_31 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

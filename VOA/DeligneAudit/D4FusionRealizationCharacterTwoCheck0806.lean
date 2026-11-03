import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_24 :
    rawPush op08 chunk08_24 acc08_25 = acc08_24 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_25 :
    rawPush op08 chunk08_25 acc08_26 = acc08_25 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_26 :
    rawPush op08 chunk08_26 acc08_27 = acc08_26 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_27 :
    rawPush op08 chunk08_27 acc08_28 = acc08_27 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

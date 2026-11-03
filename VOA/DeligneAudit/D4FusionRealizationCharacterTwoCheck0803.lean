import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_12 :
    rawPush op08 chunk08_12 acc08_13 = acc08_12 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_13 :
    rawPush op08 chunk08_13 acc08_14 = acc08_13 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_14 :
    rawPush op08 chunk08_14 acc08_15 = acc08_14 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_15 :
    rawPush op08 chunk08_15 acc08_16 = acc08_15 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

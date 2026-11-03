import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoData08

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_16 :
    rawPush op08 chunk08_16 acc08_17 = acc08_16 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_17 :
    rawPush op08 chunk08_17 acc08_18 = acc08_17 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_18 :
    rawPush op08 chunk08_18 acc08_19 = acc08_18 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact literal/certificate, kept small to bound kernel memory.
theorem push08_19 :
    rawPush op08 chunk08_19 acc08_20 = acc08_19 := by
  decide +kernel


end VOA.DeligneAudit.D4CharacterTwo

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotCheck

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

set_option maxHeartbeats 4000000 in
-- Small fixed relation batches need additional reduction steps.
theorem batchPilot_part16 :
    (List.range' 16 8).all
      (fun i => batchPilotCheck (batchPilotCases.getD i default)) = true := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate

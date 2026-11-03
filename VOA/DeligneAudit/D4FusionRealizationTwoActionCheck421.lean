/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheckData
import VOA.DeligneAudit.D4FusionRealizationTwoActionTable

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

set_option maxHeartbeats 4000000 in
-- This fixed range is bounded by measured sorting and lookup work.
theorem full_action_r82654_n031 :
    (List.range' 82654 31).all (fullActionCheck actionCase) = true := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate

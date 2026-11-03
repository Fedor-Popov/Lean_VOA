/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheckData

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

set_option maxHeartbeats 4000000 in
-- Fixed integer range, including source lookup and sparse sorting.
theorem sionrealizationtwocolumncheck_008_004 :
    (List.range' 8 4).all (columnCheck) = true := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate

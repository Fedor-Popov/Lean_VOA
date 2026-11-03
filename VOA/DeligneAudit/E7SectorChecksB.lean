/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecks
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E₇` sector: diagonal, ranges and index bounds (chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem diag_q_ok : qQ.all (fun t => !(t.1 == 132 && t.2.1 == 132)) = true := by decide +kernel

theorem diag_rel_ok : (List.range 1539).all (fun b => (relQ b).all (fun t => !(t.1 == 132 && t.2.1 == 132))) = true := by
  decide +kernel

theorem Pq_inRange : (List.range 1540).all (fun s => qInRange 133 (Pq s)) = true := by decide +kernel

theorem e7_bound0 : boundChunk e7T 133 0 19 = true := by decide +kernel
theorem e7_bound1 : boundChunk e7T 133 19 38 = true := by decide +kernel
theorem e7_bound2 : boundChunk e7T 133 38 57 = true := by decide +kernel
theorem e7_bound3 : boundChunk e7T 133 57 76 = true := by decide +kernel
theorem e7_bound4 : boundChunk e7T 133 76 95 = true := by decide +kernel
theorem e7_bound5 : boundChunk e7T 133 95 114 = true := by decide +kernel
theorem e7_bound6 : boundChunk e7T 133 114 133 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

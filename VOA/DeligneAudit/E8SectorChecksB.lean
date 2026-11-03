/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorChecks

/-!
# `E₈` sector: diagonal, ranges and index bounds (chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem diag_q_ok : qQ.all (fun t => !(t.1 == 247 && t.2.1 == 247)) = true := by decide +kernel

theorem diag_rel_ok : (List.range 3875).all (fun b => (relQ b).all (fun t => !(t.1 == 247 && t.2.1 == 247))) = true := by
  decide +kernel

theorem Pq_inRange : (List.range 3876).all (fun s => qInRange 248 (Pq s)) = true := by decide +kernel


end VOA.DeligneAudit.DeligneCarrier.E8

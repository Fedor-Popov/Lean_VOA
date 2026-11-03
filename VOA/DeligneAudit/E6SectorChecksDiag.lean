/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorChecks

set_option linter.style.longLine false

/-!
# E₆ sector data: Boolean table checks (light imports)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.DeligneAudit.E6Sparse VOA.AffineGeneral.SCLie

theorem diag_q_ok : qQ.all (fun t => !(t.1 == 77 && t.2.1 == 77)) = true := by decide +kernel

theorem diag_rel_ok : (List.range 650).all (fun b => (relQ b).all (fun t => !(t.1 == 77 && t.2.1 == 77))) = true := by
  decide +kernel


end VOA.DeligneAudit.DeligneCarrier.E6

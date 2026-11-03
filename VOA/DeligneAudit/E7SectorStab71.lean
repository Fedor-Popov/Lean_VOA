/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab71Quarter0
import VOA.DeligneAudit.E7SectorStab71Quarter1
import VOA.DeligneAudit.E7SectorStab71Quarter2
import VOA.DeligneAudit.E7SectorStab71Quarter3

/-! E7 generator 71 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab71_p0 : stabPart 71 stab71 0 385 = true :=
  stab71_quarter0

theorem stab71_p1 : stabPart 71 stab71 385 770 = true :=
  stab71_quarter1

theorem stab71_p2 : stabPart 71 stab71 770 1155 = true :=
  stab71_quarter2

theorem stab71_p3 : stabPart 71 stab71 1155 1540 = true :=
  stab71_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

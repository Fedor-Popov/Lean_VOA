/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab75Quarter0
import VOA.DeligneAudit.E7SectorStab75Quarter1
import VOA.DeligneAudit.E7SectorStab75Quarter2
import VOA.DeligneAudit.E7SectorStab75Quarter3

/-! E7 generator 75 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab75_p0 : stabPart 75 stab75 0 385 = true :=
  stab75_quarter0

theorem stab75_p1 : stabPart 75 stab75 385 770 = true :=
  stab75_quarter1

theorem stab75_p2 : stabPart 75 stab75 770 1155 = true :=
  stab75_quarter2

theorem stab75_p3 : stabPart 75 stab75 1155 1540 = true :=
  stab75_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

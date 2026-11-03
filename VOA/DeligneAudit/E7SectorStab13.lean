/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab13Quarter0
import VOA.DeligneAudit.E7SectorStab13Quarter1
import VOA.DeligneAudit.E7SectorStab13Quarter2
import VOA.DeligneAudit.E7SectorStab13Quarter3

/-! E7 generator 13 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab13_p0 : stabPart 13 stab13 0 385 = true :=
  stab13_quarter0

theorem stab13_p1 : stabPart 13 stab13 385 770 = true :=
  stab13_quarter1

theorem stab13_p2 : stabPart 13 stab13 770 1155 = true :=
  stab13_quarter2

theorem stab13_p3 : stabPart 13 stab13 1155 1540 = true :=
  stab13_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

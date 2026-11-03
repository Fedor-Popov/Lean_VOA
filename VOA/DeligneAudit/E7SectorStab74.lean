/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab74Quarter0
import VOA.DeligneAudit.E7SectorStab74Quarter1
import VOA.DeligneAudit.E7SectorStab74Quarter2
import VOA.DeligneAudit.E7SectorStab74Quarter3

/-! E7 generator 74 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab74_p0 : stabPart 74 stab74 0 385 = true :=
  stab74_quarter0

theorem stab74_p1 : stabPart 74 stab74 385 770 = true :=
  stab74_quarter1

theorem stab74_p2 : stabPart 74 stab74 770 1155 = true :=
  stab74_quarter2

theorem stab74_p3 : stabPart 74 stab74 1155 1540 = true :=
  stab74_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab72Quarter0
import VOA.DeligneAudit.E7SectorStab72Quarter1
import VOA.DeligneAudit.E7SectorStab72Quarter2
import VOA.DeligneAudit.E7SectorStab72Quarter3

/-! E7 generator 72 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab72_p0 : stabPart 72 stab72 0 385 = true :=
  stab72_quarter0

theorem stab72_p1 : stabPart 72 stab72 385 770 = true :=
  stab72_quarter1

theorem stab72_p2 : stabPart 72 stab72 770 1155 = true :=
  stab72_quarter2

theorem stab72_p3 : stabPart 72 stab72 1155 1540 = true :=
  stab72_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

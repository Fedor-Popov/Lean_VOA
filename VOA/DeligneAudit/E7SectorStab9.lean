/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab9Quarter0
import VOA.DeligneAudit.E7SectorStab9Quarter1
import VOA.DeligneAudit.E7SectorStab9Quarter2
import VOA.DeligneAudit.E7SectorStab9Quarter3

/-! E7 generator 9 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab9_p0 : stabPart 9 stab9 0 385 = true :=
  stab9_quarter0

theorem stab9_p1 : stabPart 9 stab9 385 770 = true :=
  stab9_quarter1

theorem stab9_p2 : stabPart 9 stab9 770 1155 = true :=
  stab9_quarter2

theorem stab9_p3 : stabPart 9 stab9 1155 1540 = true :=
  stab9_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

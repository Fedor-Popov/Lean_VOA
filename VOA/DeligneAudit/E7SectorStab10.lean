/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab10Quarter0
import VOA.DeligneAudit.E7SectorStab10Quarter1
import VOA.DeligneAudit.E7SectorStab10Quarter2
import VOA.DeligneAudit.E7SectorStab10Quarter3

/-! E7 generator 10 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab10_p0 : stabPart 10 stab10 0 385 = true :=
  stab10_quarter0

theorem stab10_p1 : stabPart 10 stab10 385 770 = true :=
  stab10_quarter1

theorem stab10_p2 : stabPart 10 stab10 770 1155 = true :=
  stab10_quarter2

theorem stab10_p3 : stabPart 10 stab10 1155 1540 = true :=
  stab10_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

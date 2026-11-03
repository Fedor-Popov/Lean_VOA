/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab76Quarter0
import VOA.DeligneAudit.E7SectorStab76Quarter1
import VOA.DeligneAudit.E7SectorStab76Quarter2
import VOA.DeligneAudit.E7SectorStab76Quarter3

/-! E7 generator 76 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab76_p0 : stabPart 76 stab76 0 385 = true :=
  stab76_quarter0

theorem stab76_p1 : stabPart 76 stab76 385 770 = true :=
  stab76_quarter1

theorem stab76_p2 : stabPart 76 stab76 770 1155 = true :=
  stab76_quarter2

theorem stab76_p3 : stabPart 76 stab76 1155 1540 = true :=
  stab76_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

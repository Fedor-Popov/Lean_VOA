/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab11Quarter0
import VOA.DeligneAudit.E7SectorStab11Quarter1
import VOA.DeligneAudit.E7SectorStab11Quarter2
import VOA.DeligneAudit.E7SectorStab11Quarter3

/-! E7 generator 11 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab11_p0 : stabPart 11 stab11 0 385 = true :=
  stab11_quarter0

theorem stab11_p1 : stabPart 11 stab11 385 770 = true :=
  stab11_quarter1

theorem stab11_p2 : stabPart 11 stab11 770 1155 = true :=
  stab11_quarter2

theorem stab11_p3 : stabPart 11 stab11 1155 1540 = true :=
  stab11_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

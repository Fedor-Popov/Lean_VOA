/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorDefs
import VOA.DeligneAudit.E7SectorStab73Quarter0
import VOA.DeligneAudit.E7SectorStab73Quarter1
import VOA.DeligneAudit.E7SectorStab73Quarter2
import VOA.DeligneAudit.E7SectorStab73Quarter3

/-! E7 generator 73 stability. The original four range statements are assembled
from the checked smaller ranges; literal data and length facts are imported unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab73_p0 : stabPart 73 stab73 0 385 = true :=
  stab73_quarter0

theorem stab73_p1 : stabPart 73 stab73 385 770 = true :=
  stab73_quarter1

theorem stab73_p2 : stabPart 73 stab73 770 1155 = true :=
  stab73_quarter2

theorem stab73_p3 : stabPart 73 stab73 1155 1540 = true :=
  stab73_quarter3

end VOA.DeligneAudit.DeligneCarrier.E7

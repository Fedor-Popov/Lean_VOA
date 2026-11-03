/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorD4Table
import VOA.DeligneAudit.DeligneSectorD4RelCheck00
import VOA.DeligneAudit.DeligneSectorD4RelCheck01
import VOA.DeligneAudit.DeligneSectorD4RelCheck02
import VOA.DeligneAudit.DeligneSectorD4RelCheck03
import VOA.DeligneAudit.DeligneSectorD4RelCheck04
import VOA.DeligneAudit.DeligneSectorD4RelCheck05
import VOA.DeligneAudit.DeligneSectorD4RelCheck06
import VOA.DeligneAudit.DeligneSectorD4RelCheck07
import VOA.DeligneAudit.DeligneSectorD4RelCheck08
import VOA.DeligneAudit.DeligneSectorD4RelCheck09
import VOA.DeligneAudit.DeligneSectorD4RelCheck10
import VOA.DeligneAudit.DeligneSectorD4RelCheck11
import VOA.DeligneAudit.DeligneSectorD4RelCheck12
import VOA.DeligneAudit.DeligneSectorD4RelCheck13
import VOA.DeligneAudit.DeligneSectorD4RelCheck14
import VOA.DeligneAudit.DeligneSectorD4RelCheck15
import VOA.DeligneAudit.DeligneSectorD4RelCheck16
import VOA.DeligneAudit.DeligneSectorD4RelCheck17
import VOA.DeligneAudit.DeligneSectorD4RelCheck18
import VOA.DeligneAudit.DeligneSectorD4RelCheck19
import VOA.DeligneAudit.DeligneSectorD4RelCheck20
import VOA.DeligneAudit.DeligneSectorD4RelCheck21
import VOA.DeligneAudit.DeligneSectorD4RelCheck22
import VOA.DeligneAudit.DeligneSectorD4RelCheck23
import VOA.DeligneAudit.DeligneSectorD4RelCheck24
import VOA.DeligneAudit.DeligneSectorD4RelCheck25
import VOA.DeligneAudit.DeligneSectorD4RelCheck26
import VOA.DeligneAudit.DeligneSectorD4RelCheck27
import VOA.DeligneAudit.DeligneSectorD4RelCheck28

/-!
# D₄ relations as integer sparse forms, and ad-stability certificates

`relT` transcribes `DeligneCarrierD4.relTable` (indices `0..104`) and `casEntries` (index `105`)
with integer coefficients; `certT` lists, for every current `x` and relation `r`, an integer
`N ≠ 0` and coefficients `μ_s` with `N · ad_x(rel r) = Σ_s μ_s rel s` (found by exact
elimination; `1380` of the `28 · 106` pairs are nonzero, the others have `ad_x(rel r) = 0`).
`d4_stabCheck` checks all of them by `decide +kernel`.
-/

namespace VOA.DeligneAudit.DeligneSector.D4

open VOA.DeligneAudit.DeligneSector.Sparse

set_option linter.style.longLine false

set_option maxHeartbeats 4000000 in
theorem d4_stabCheck (x : Fin 28) : stabCheckX x = true := by
  fin_cases x
  · exact d4_stab_0
  · exact d4_stab_1
  · exact d4_stab_2
  · exact d4_stab_3
  · exact d4_stab_4
  · exact d4_stab_5
  · exact d4_stab_6
  · exact d4_stab_7
  · exact d4_stab_8
  · exact d4_stab_9
  · exact d4_stab_10
  · exact d4_stab_11
  · exact d4_stab_12
  · exact d4_stab_13
  · exact d4_stab_14
  · exact d4_stab_15
  · exact d4_stab_16
  · exact d4_stab_17
  · exact d4_stab_18
  · exact d4_stab_19
  · exact d4_stab_20
  · exact d4_stab_21
  · exact d4_stab_22
  · exact d4_stab_23
  · exact d4_stab_24
  · exact d4_stab_25
  · exact d4_stab_26
  · exact d4_stab_27

end VOA.DeligneAudit.DeligneSector.D4

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.D4.d4_stabCheck
end AxiomAudit

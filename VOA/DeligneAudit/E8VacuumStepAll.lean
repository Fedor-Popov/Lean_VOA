/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8VacuumStepCheck00
import VOA.DeligneAudit.E8VacuumStepCheck01
import VOA.DeligneAudit.E8VacuumStepCheck02
import VOA.DeligneAudit.E8VacuumStepCheck03
import VOA.DeligneAudit.E8VacuumStepCheck04
import VOA.DeligneAudit.E8VacuumStepCheck05
import VOA.DeligneAudit.E8VacuumStepCheck06
import VOA.DeligneAudit.E8VacuumStepCheck07
import VOA.DeligneAudit.E8VacuumStepCheck08
import VOA.DeligneAudit.E8VacuumStepCheck09
import VOA.DeligneAudit.E8VacuumStepCheck10
import VOA.DeligneAudit.E8VacuumStepCheck11
import VOA.DeligneAudit.E8VacuumStepCheck12
import VOA.DeligneAudit.E8VacuumStepCheck13
import VOA.DeligneAudit.E8VacuumStepCheck14
import VOA.DeligneAudit.E8VacuumStepCheck15
import VOA.DeligneAudit.E8VacuumStepCheck16
import VOA.DeligneAudit.E8VacuumStepCheck17
import VOA.DeligneAudit.E8VacuumStepCheck18
import VOA.DeligneAudit.E8VacuumStepCheck19
import VOA.DeligneAudit.E8VacuumStepCheck20
import VOA.DeligneAudit.E8VacuumStepCheck21
import VOA.DeligneAudit.E8VacuumStepCheck22
import VOA.DeligneAudit.E8VacuumStepCheck23
import VOA.DeligneAudit.E8VacuumStepCheck24
import VOA.DeligneAudit.E8VacuumStepCheck25
import VOA.DeligneAudit.E8VacuumStepCheck26
import VOA.DeligneAudit.E8VacuumStepCheck27
import VOA.DeligneAudit.E8VacuumStepCheck28
import VOA.DeligneAudit.E8VacuumStepCheck29
import VOA.DeligneAudit.E8VacuumStepCheck30

/-!
# All `E₈` propagation steps pass `stepOK`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem stepOK_all (s : ℕ) (h1 : 1 ≤ s) (h2 : s < 3875) : stepOK s = true := by
  by_cases h00 : s < 126; · exact stepOK_00 s h00 (by omega)
  by_cases h01 : s < 251; · exact stepOK_01 s h01 (by omega)
  by_cases h02 : s < 376; · exact stepOK_02 s h02 (by omega)
  by_cases h03 : s < 501; · exact stepOK_03 s h03 (by omega)
  by_cases h04 : s < 626; · exact stepOK_04 s h04 (by omega)
  by_cases h05 : s < 751; · exact stepOK_05 s h05 (by omega)
  by_cases h06 : s < 876; · exact stepOK_06 s h06 (by omega)
  by_cases h07 : s < 1001; · exact stepOK_07 s h07 (by omega)
  by_cases h08 : s < 1126; · exact stepOK_08 s h08 (by omega)
  by_cases h09 : s < 1251; · exact stepOK_09 s h09 (by omega)
  by_cases h10 : s < 1376; · exact stepOK_10 s h10 (by omega)
  by_cases h11 : s < 1501; · exact stepOK_11 s h11 (by omega)
  by_cases h12 : s < 1626; · exact stepOK_12 s h12 (by omega)
  by_cases h13 : s < 1751; · exact stepOK_13 s h13 (by omega)
  by_cases h14 : s < 1876; · exact stepOK_14 s h14 (by omega)
  by_cases h15 : s < 2001; · exact stepOK_15 s h15 (by omega)
  by_cases h16 : s < 2126; · exact stepOK_16 s h16 (by omega)
  by_cases h17 : s < 2251; · exact stepOK_17 s h17 (by omega)
  by_cases h18 : s < 2376; · exact stepOK_18 s h18 (by omega)
  by_cases h19 : s < 2501; · exact stepOK_19 s h19 (by omega)
  by_cases h20 : s < 2626; · exact stepOK_20 s h20 (by omega)
  by_cases h21 : s < 2751; · exact stepOK_21 s h21 (by omega)
  by_cases h22 : s < 2876; · exact stepOK_22 s h22 (by omega)
  by_cases h23 : s < 3001; · exact stepOK_23 s h23 (by omega)
  by_cases h24 : s < 3126; · exact stepOK_24 s h24 (by omega)
  by_cases h25 : s < 3251; · exact stepOK_25 s h25 (by omega)
  by_cases h26 : s < 3376; · exact stepOK_26 s h26 (by omega)
  by_cases h27 : s < 3501; · exact stepOK_27 s h27 (by omega)
  by_cases h28 : s < 3626; · exact stepOK_28 s h28 (by omega)
  by_cases h29 : s < 3751; · exact stepOK_29 s h29 (by omega)
  exact stepOK_30 s h2 (by omega)

end VOA.DeligneAudit.DeligneCarrier.E8

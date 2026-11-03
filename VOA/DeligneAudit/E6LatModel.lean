/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.E6LatModelA
import VOA.DeligneAudit.E6LatModelB
import VOA.DeligneAudit.E6LatModelC
import VOA.DeligneAudit.E6LatModelD
import VOA.DeligneAudit.E6LatModelE
import VOA.DeligneAudit.E6LatModelF
import VOA.DeligneAudit.E6LatModelG
import VOA.DeligneAudit.E6LatModelH
import VOA.DeligneAudit.E6LatModelI
import VOA.DeligneAudit.E6LatModelJ
import VOA.DeligneAudit.E6LatModelK
import VOA.DeligneAudit.E6LatModelL

/-!
# All pairs of the `E₆` cert basis pass `pairOK`
-/

namespace VOA.DeligneAudit.E6Lat

theorem pairOK_all (a b : Fin 78) : pairOK a b = true := by
  revert b
  fin_cases a
  · exact row_ok0
  · exact row_ok1
  · exact row_ok2
  · exact row_ok3
  · exact row_ok4
  · exact row_ok5
  · exact row_ok6
  · exact row_ok7
  · exact row_ok8
  · exact row_ok9
  · exact row_ok10
  · exact row_ok11
  · exact row_ok12
  · exact row_ok13
  · exact row_ok14
  · exact row_ok15
  · exact row_ok16
  · exact row_ok17
  · exact row_ok18
  · exact row_ok19
  · exact row_ok20
  · exact row_ok21
  · exact row_ok22
  · exact row_ok23
  · exact row_ok24
  · exact row_ok25
  · exact row_ok26
  · exact row_ok27
  · exact row_ok28
  · exact row_ok29
  · exact row_ok30
  · exact row_ok31
  · exact row_ok32
  · exact row_ok33
  · exact row_ok34
  · exact row_ok35
  · exact row_ok36
  · exact row_ok37
  · exact row_ok38
  · exact row_ok39
  · exact row_ok40
  · exact row_ok41
  · exact row_ok42
  · exact row_ok43
  · exact row_ok44
  · exact row_ok45
  · exact row_ok46
  · exact row_ok47
  · exact row_ok48
  · exact row_ok49
  · exact row_ok50
  · exact row_ok51
  · exact row_ok52
  · exact row_ok53
  · exact row_ok54
  · exact row_ok55
  · exact row_ok56
  · exact row_ok57
  · exact row_ok58
  · exact row_ok59
  · exact row_ok60
  · exact row_ok61
  · exact row_ok62
  · exact row_ok63
  · exact row_ok64
  · exact row_ok65
  · exact row_ok66
  · exact row_ok67
  · exact row_ok68
  · exact row_ok69
  · exact row_ok70
  · exact row_ok71
  · exact row_ok72
  · exact row_ok73
  · exact row_ok74
  · exact row_ok75
  · exact row_ok76
  · exact row_ok77

end VOA.DeligneAudit.E6Lat

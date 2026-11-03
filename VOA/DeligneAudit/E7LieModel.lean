/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.E7LieModelA
import VOA.DeligneAudit.E7LieModelB
import VOA.DeligneAudit.E7LieModelC
import VOA.DeligneAudit.E7LieModelD
import VOA.DeligneAudit.E7LieModelE
import VOA.DeligneAudit.E7LieModelF
import VOA.DeligneAudit.E7LieModelG
import VOA.DeligneAudit.E7LieModelH
import VOA.DeligneAudit.E7LieModelI
import VOA.DeligneAudit.E7LieModelJ
import VOA.DeligneAudit.E7LieModelK
import VOA.DeligneAudit.E7LieModelL
import VOA.DeligneAudit.E7LieModelM
import VOA.DeligneAudit.E7LieModelN
import VOA.DeligneAudit.E7LieModelO
import VOA.DeligneAudit.E7LieModelP
import VOA.DeligneAudit.E7LieModelQ
import VOA.DeligneAudit.E7LieModelR
import VOA.DeligneAudit.E7LieModelS

/-!
# All pairs of the `E₇` cert basis pass `pairOK`
-/

namespace VOA.DeligneAudit.E7Lie

theorem pairOK_all (a b : Fin 133) : pairOK a b = true := by
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
  · exact row_ok78
  · exact row_ok79
  · exact row_ok80
  · exact row_ok81
  · exact row_ok82
  · exact row_ok83
  · exact row_ok84
  · exact row_ok85
  · exact row_ok86
  · exact row_ok87
  · exact row_ok88
  · exact row_ok89
  · exact row_ok90
  · exact row_ok91
  · exact row_ok92
  · exact row_ok93
  · exact row_ok94
  · exact row_ok95
  · exact row_ok96
  · exact row_ok97
  · exact row_ok98
  · exact row_ok99
  · exact row_ok100
  · exact row_ok101
  · exact row_ok102
  · exact row_ok103
  · exact row_ok104
  · exact row_ok105
  · exact row_ok106
  · exact row_ok107
  · exact row_ok108
  · exact row_ok109
  · exact row_ok110
  · exact row_ok111
  · exact row_ok112
  · exact row_ok113
  · exact row_ok114
  · exact row_ok115
  · exact row_ok116
  · exact row_ok117
  · exact row_ok118
  · exact row_ok119
  · exact row_ok120
  · exact row_ok121
  · exact row_ok122
  · exact row_ok123
  · exact row_ok124
  · exact row_ok125
  · exact row_ok126
  · exact row_ok127
  · exact row_ok128
  · exact row_ok129
  · exact row_ok130
  · exact row_ok131
  · exact row_ok132

end VOA.DeligneAudit.E7Lie

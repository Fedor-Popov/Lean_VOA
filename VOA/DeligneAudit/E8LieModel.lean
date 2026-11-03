/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.E8LieModel00
import VOA.DeligneAudit.E8LieModel01
import VOA.DeligneAudit.E8LieModel02
import VOA.DeligneAudit.E8LieModel03
import VOA.DeligneAudit.E8LieModel04
import VOA.DeligneAudit.E8LieModel05
import VOA.DeligneAudit.E8LieModel06
import VOA.DeligneAudit.E8LieModel07
import VOA.DeligneAudit.E8LieModel08
import VOA.DeligneAudit.E8LieModel09
import VOA.DeligneAudit.E8LieModel10
import VOA.DeligneAudit.E8LieModel11
import VOA.DeligneAudit.E8LieModel12
import VOA.DeligneAudit.E8LieModel13
import VOA.DeligneAudit.E8LieModel14
import VOA.DeligneAudit.E8LieModel15
import VOA.DeligneAudit.E8LieModel16
import VOA.DeligneAudit.E8LieModel17
import VOA.DeligneAudit.E8LieModel18
import VOA.DeligneAudit.E8LieModel19
import VOA.DeligneAudit.E8LieModel20
import VOA.DeligneAudit.E8LieModel21
import VOA.DeligneAudit.E8LieModel22
import VOA.DeligneAudit.E8LieModel23
import VOA.DeligneAudit.E8LieModel24
import VOA.DeligneAudit.E8LieModel25
import VOA.DeligneAudit.E8LieModel26
import VOA.DeligneAudit.E8LieModel27
import VOA.DeligneAudit.E8LieModel28
import VOA.DeligneAudit.E8LieModel29
import VOA.DeligneAudit.E8LieModel30

/-!
# All pairs of the `E₈` cert basis pass `pairOK`
-/

namespace VOA.DeligneAudit.E8Lie

theorem pairOK_all (a b : Fin 248) : pairOK a b = true := by
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
  · exact row_ok133
  · exact row_ok134
  · exact row_ok135
  · exact row_ok136
  · exact row_ok137
  · exact row_ok138
  · exact row_ok139
  · exact row_ok140
  · exact row_ok141
  · exact row_ok142
  · exact row_ok143
  · exact row_ok144
  · exact row_ok145
  · exact row_ok146
  · exact row_ok147
  · exact row_ok148
  · exact row_ok149
  · exact row_ok150
  · exact row_ok151
  · exact row_ok152
  · exact row_ok153
  · exact row_ok154
  · exact row_ok155
  · exact row_ok156
  · exact row_ok157
  · exact row_ok158
  · exact row_ok159
  · exact row_ok160
  · exact row_ok161
  · exact row_ok162
  · exact row_ok163
  · exact row_ok164
  · exact row_ok165
  · exact row_ok166
  · exact row_ok167
  · exact row_ok168
  · exact row_ok169
  · exact row_ok170
  · exact row_ok171
  · exact row_ok172
  · exact row_ok173
  · exact row_ok174
  · exact row_ok175
  · exact row_ok176
  · exact row_ok177
  · exact row_ok178
  · exact row_ok179
  · exact row_ok180
  · exact row_ok181
  · exact row_ok182
  · exact row_ok183
  · exact row_ok184
  · exact row_ok185
  · exact row_ok186
  · exact row_ok187
  · exact row_ok188
  · exact row_ok189
  · exact row_ok190
  · exact row_ok191
  · exact row_ok192
  · exact row_ok193
  · exact row_ok194
  · exact row_ok195
  · exact row_ok196
  · exact row_ok197
  · exact row_ok198
  · exact row_ok199
  · exact row_ok200
  · exact row_ok201
  · exact row_ok202
  · exact row_ok203
  · exact row_ok204
  · exact row_ok205
  · exact row_ok206
  · exact row_ok207
  · exact row_ok208
  · exact row_ok209
  · exact row_ok210
  · exact row_ok211
  · exact row_ok212
  · exact row_ok213
  · exact row_ok214
  · exact row_ok215
  · exact row_ok216
  · exact row_ok217
  · exact row_ok218
  · exact row_ok219
  · exact row_ok220
  · exact row_ok221
  · exact row_ok222
  · exact row_ok223
  · exact row_ok224
  · exact row_ok225
  · exact row_ok226
  · exact row_ok227
  · exact row_ok228
  · exact row_ok229
  · exact row_ok230
  · exact row_ok231
  · exact row_ok232
  · exact row_ok233
  · exact row_ok234
  · exact row_ok235
  · exact row_ok236
  · exact row_ok237
  · exact row_ok238
  · exact row_ok239
  · exact row_ok240
  · exact row_ok241
  · exact row_ok242
  · exact row_ok243
  · exact row_ok244
  · exact row_ok245
  · exact row_ok246
  · exact row_ok247

end VOA.DeligneAudit.E8Lie

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.LatticeRealizationE8RowsA
import VOA.DeligneAudit.LatticeRealizationE8RowsB
import VOA.DeligneAudit.LatticeRealizationE8RowsC
import VOA.DeligneAudit.LatticeRealizationE8RowsD
import VOA.DeligneAudit.LatticeRealizationE8RowsE
import VOA.DeligneAudit.LatticeRealizationE8RowsF
import VOA.DeligneAudit.LatticeRealizationE8RowsG
import VOA.DeligneAudit.LatticeRealizationE8RowsH
import VOA.DeligneAudit.LatticeRealizationE8RowsI
import VOA.DeligneAudit.LatticeRealizationE8RowsJ
import VOA.DeligneAudit.LatticeRealizationE8RowsK
import VOA.DeligneAudit.LatticeRealizationE8RowsL
import VOA.DeligneAudit.LatticeRealizationE8RowsM
import VOA.DeligneAudit.LatticeRealizationE8RowsN
import VOA.DeligneAudit.LatticeRealizationE8RowsO
import VOA.DeligneAudit.LatticeRealizationE8RowsP
import VOA.DeligneAudit.LatticeRealizationE8RowsQ
import VOA.DeligneAudit.LatticeRealizationE8RowsR
import VOA.DeligneAudit.LatticeRealizationE8RowsS
import VOA.DeligneAudit.LatticeRealizationE8RowsT
import VOA.DeligneAudit.LatticeRealizationE8RowsU
import VOA.DeligneAudit.LatticeRealizationE8RowsV
import VOA.DeligneAudit.LatticeRealizationE8RowsW
import VOA.DeligneAudit.LatticeRealizationE8RowsX
import VOA.DeligneAudit.LatticeRealizationE8RowsY
import VOA.DeligneAudit.LatticeRealizationE8RowsZ
import VOA.DeligneAudit.LatticeRealizationE8RowsZA
import VOA.DeligneAudit.LatticeRealizationE8RowsZB
import VOA.DeligneAudit.LatticeRealizationE8RowsZC
import VOA.DeligneAudit.LatticeRealizationE8RowsZD
import VOA.DeligneAudit.LatticeRealizationE8RowsZE

/-!
# `E8`: the sector table is the lattice-model cert table (all rows)
-/

set_option linter.style.longLine false

namespace VOA.DeligneAudit.LatticeRealization.E8

theorem table_eq_sL (a b : Fin 248) :
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T a b = (VOA.DeligneAudit.E8Lie.sL a b).map (fun t => ((t.1 : ℕ), t.2)) := by
  revert b
  fin_cases a
  · exact bridgeRow0
  · exact bridgeRow1
  · exact bridgeRow2
  · exact bridgeRow3
  · exact bridgeRow4
  · exact bridgeRow5
  · exact bridgeRow6
  · exact bridgeRow7
  · exact bridgeRow8
  · exact bridgeRow9
  · exact bridgeRow10
  · exact bridgeRow11
  · exact bridgeRow12
  · exact bridgeRow13
  · exact bridgeRow14
  · exact bridgeRow15
  · exact bridgeRow16
  · exact bridgeRow17
  · exact bridgeRow18
  · exact bridgeRow19
  · exact bridgeRow20
  · exact bridgeRow21
  · exact bridgeRow22
  · exact bridgeRow23
  · exact bridgeRow24
  · exact bridgeRow25
  · exact bridgeRow26
  · exact bridgeRow27
  · exact bridgeRow28
  · exact bridgeRow29
  · exact bridgeRow30
  · exact bridgeRow31
  · exact bridgeRow32
  · exact bridgeRow33
  · exact bridgeRow34
  · exact bridgeRow35
  · exact bridgeRow36
  · exact bridgeRow37
  · exact bridgeRow38
  · exact bridgeRow39
  · exact bridgeRow40
  · exact bridgeRow41
  · exact bridgeRow42
  · exact bridgeRow43
  · exact bridgeRow44
  · exact bridgeRow45
  · exact bridgeRow46
  · exact bridgeRow47
  · exact bridgeRow48
  · exact bridgeRow49
  · exact bridgeRow50
  · exact bridgeRow51
  · exact bridgeRow52
  · exact bridgeRow53
  · exact bridgeRow54
  · exact bridgeRow55
  · exact bridgeRow56
  · exact bridgeRow57
  · exact bridgeRow58
  · exact bridgeRow59
  · exact bridgeRow60
  · exact bridgeRow61
  · exact bridgeRow62
  · exact bridgeRow63
  · exact bridgeRow64
  · exact bridgeRow65
  · exact bridgeRow66
  · exact bridgeRow67
  · exact bridgeRow68
  · exact bridgeRow69
  · exact bridgeRow70
  · exact bridgeRow71
  · exact bridgeRow72
  · exact bridgeRow73
  · exact bridgeRow74
  · exact bridgeRow75
  · exact bridgeRow76
  · exact bridgeRow77
  · exact bridgeRow78
  · exact bridgeRow79
  · exact bridgeRow80
  · exact bridgeRow81
  · exact bridgeRow82
  · exact bridgeRow83
  · exact bridgeRow84
  · exact bridgeRow85
  · exact bridgeRow86
  · exact bridgeRow87
  · exact bridgeRow88
  · exact bridgeRow89
  · exact bridgeRow90
  · exact bridgeRow91
  · exact bridgeRow92
  · exact bridgeRow93
  · exact bridgeRow94
  · exact bridgeRow95
  · exact bridgeRow96
  · exact bridgeRow97
  · exact bridgeRow98
  · exact bridgeRow99
  · exact bridgeRow100
  · exact bridgeRow101
  · exact bridgeRow102
  · exact bridgeRow103
  · exact bridgeRow104
  · exact bridgeRow105
  · exact bridgeRow106
  · exact bridgeRow107
  · exact bridgeRow108
  · exact bridgeRow109
  · exact bridgeRow110
  · exact bridgeRow111
  · exact bridgeRow112
  · exact bridgeRow113
  · exact bridgeRow114
  · exact bridgeRow115
  · exact bridgeRow116
  · exact bridgeRow117
  · exact bridgeRow118
  · exact bridgeRow119
  · exact bridgeRow120
  · exact bridgeRow121
  · exact bridgeRow122
  · exact bridgeRow123
  · exact bridgeRow124
  · exact bridgeRow125
  · exact bridgeRow126
  · exact bridgeRow127
  · exact bridgeRow128
  · exact bridgeRow129
  · exact bridgeRow130
  · exact bridgeRow131
  · exact bridgeRow132
  · exact bridgeRow133
  · exact bridgeRow134
  · exact bridgeRow135
  · exact bridgeRow136
  · exact bridgeRow137
  · exact bridgeRow138
  · exact bridgeRow139
  · exact bridgeRow140
  · exact bridgeRow141
  · exact bridgeRow142
  · exact bridgeRow143
  · exact bridgeRow144
  · exact bridgeRow145
  · exact bridgeRow146
  · exact bridgeRow147
  · exact bridgeRow148
  · exact bridgeRow149
  · exact bridgeRow150
  · exact bridgeRow151
  · exact bridgeRow152
  · exact bridgeRow153
  · exact bridgeRow154
  · exact bridgeRow155
  · exact bridgeRow156
  · exact bridgeRow157
  · exact bridgeRow158
  · exact bridgeRow159
  · exact bridgeRow160
  · exact bridgeRow161
  · exact bridgeRow162
  · exact bridgeRow163
  · exact bridgeRow164
  · exact bridgeRow165
  · exact bridgeRow166
  · exact bridgeRow167
  · exact bridgeRow168
  · exact bridgeRow169
  · exact bridgeRow170
  · exact bridgeRow171
  · exact bridgeRow172
  · exact bridgeRow173
  · exact bridgeRow174
  · exact bridgeRow175
  · exact bridgeRow176
  · exact bridgeRow177
  · exact bridgeRow178
  · exact bridgeRow179
  · exact bridgeRow180
  · exact bridgeRow181
  · exact bridgeRow182
  · exact bridgeRow183
  · exact bridgeRow184
  · exact bridgeRow185
  · exact bridgeRow186
  · exact bridgeRow187
  · exact bridgeRow188
  · exact bridgeRow189
  · exact bridgeRow190
  · exact bridgeRow191
  · exact bridgeRow192
  · exact bridgeRow193
  · exact bridgeRow194
  · exact bridgeRow195
  · exact bridgeRow196
  · exact bridgeRow197
  · exact bridgeRow198
  · exact bridgeRow199
  · exact bridgeRow200
  · exact bridgeRow201
  · exact bridgeRow202
  · exact bridgeRow203
  · exact bridgeRow204
  · exact bridgeRow205
  · exact bridgeRow206
  · exact bridgeRow207
  · exact bridgeRow208
  · exact bridgeRow209
  · exact bridgeRow210
  · exact bridgeRow211
  · exact bridgeRow212
  · exact bridgeRow213
  · exact bridgeRow214
  · exact bridgeRow215
  · exact bridgeRow216
  · exact bridgeRow217
  · exact bridgeRow218
  · exact bridgeRow219
  · exact bridgeRow220
  · exact bridgeRow221
  · exact bridgeRow222
  · exact bridgeRow223
  · exact bridgeRow224
  · exact bridgeRow225
  · exact bridgeRow226
  · exact bridgeRow227
  · exact bridgeRow228
  · exact bridgeRow229
  · exact bridgeRow230
  · exact bridgeRow231
  · exact bridgeRow232
  · exact bridgeRow233
  · exact bridgeRow234
  · exact bridgeRow235
  · exact bridgeRow236
  · exact bridgeRow237
  · exact bridgeRow238
  · exact bridgeRow239
  · exact bridgeRow240
  · exact bridgeRow241
  · exact bridgeRow242
  · exact bridgeRow243
  · exact bridgeRow244
  · exact bridgeRow245
  · exact bridgeRow246
  · exact bridgeRow247

end VOA.DeligneAudit.LatticeRealization.E8

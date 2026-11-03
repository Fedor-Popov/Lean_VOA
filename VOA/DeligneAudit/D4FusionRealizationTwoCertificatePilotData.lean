/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoIntegerData

namespace VOA.DeligneAudit.D4Two.Certificate

def pilotCoordinates : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88,
  89, 90, 115, 132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558,
  588, 618, 648, 678, 708, 738, 768, 798, 812, 813, 814, 815, 840]

def pilotSource : SV := [(15, Int.negSucc 3), (44, Int.ofNat 12), (73, Int.negSucc 7), (102,
  Int.negSucc 7), (188, Int.ofNat 8), (245, Int.ofNat 2), (273, Int.ofNat 2), (357, Int.ofNat 2),
  (385, Int.ofNat 2), (412, Int.ofNat 8), (435, Int.negSucc 3), (436, Int.ofNat 12), (437,
  Int.negSucc 7), (438, Int.negSucc 7)]

def pilotTarget : SV :=
  [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat 288), (132,
  Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 24), (3, Int.negSucc 47), (29, Int.ofNat
  24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59, Int.ofNat 24), (61,
  Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89, Int.negSucc 47), (90,
  Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252, Int.ofNat 24), (468, Int.ofNat
  72), (528, Int.ofNat 24), (588, Int.ofNat 24), (30, Int.negSucc 7), (31, Int.ofNat 8), (32,
  Int.ofNat 8), (59, Int.ofNat 8), (61, Int.negSucc 15), (88, Int.ofNat 8), (89, Int.negSucc 15),
  (192, Int.ofNat 4), (252, Int.ofNat 4), (282, Int.ofNat 4), (342, Int.negSucc 3), (528,
  Int.ofNat 4), (588, Int.ofNat 4), (618, Int.ofNat 4), (678, Int.negSucc 3), (0, Int.ofNat 8),
  (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16), (29, Int.negSucc 19), (30, Int.ofNat
  48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58, Int.ofNat 8), (59, Int.negSucc 19), (60,
  Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16), (88, Int.negSucc 35), (89, Int.ofNat 16),
  (90, Int.ofNat 24), (132, Int.negSucc 3), (192, Int.negSucc 11), (252, Int.negSucc 3), (468,
  Int.negSucc 3), (528, Int.negSucc 11), (588, Int.negSucc 3), (0, Int.ofNat 24), (1, Int.negSucc
  71), (2, Int.ofNat 48), (3, Int.ofNat 48), (29, Int.negSucc 71), (30, Int.ofNat 192), (31,
  Int.negSucc 119), (32, Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 119), (60,
  Int.ofNat 72), (61, Int.ofNat 72), (87, Int.ofNat 48), (88, Int.negSucc 119), (89, Int.ofNat
  72), (90, Int.ofNat 72), (132, Int.negSucc 11), (162, Int.negSucc 11), (192, Int.negSucc 47),
  (252, Int.negSucc 11), (282, Int.negSucc 11), (468, Int.negSucc 11), (498, Int.negSucc 11),
  (528, Int.negSucc 47), (588, Int.negSucc 11), (618, Int.negSucc 11), (1, Int.ofNat 4), (2,
  Int.negSucc 7), (29, Int.ofNat 4), (30, Int.negSucc 23), (31, Int.ofNat 36), (32, Int.ofNat 4),
  (58, Int.negSucc 7), (59, Int.ofNat 36), (60, Int.negSucc 47), (61, Int.negSucc 7), (88,
  Int.ofNat 4), (89, Int.negSucc 7), (162, Int.ofNat 12), (192, Int.ofNat 4), (282, Int.ofNat 4),
  (498, Int.ofNat 12), (528, Int.ofNat 4), (618, Int.ofNat 4), (1, Int.ofNat 8), (3, Int.negSucc
  15), (29, Int.ofNat 8), (30, Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88,
  Int.ofNat 8), (192, Int.ofNat 4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3),
  (528, Int.ofNat 4), (588, Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192,
  Int.negSucc 7), (252, Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342,
  Int.ofNat 8), (372, Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc
  7), (588, Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
  Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 80),
  (2, Int.negSucc 31), (3, Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31,
  Int.ofNat 48), (32, Int.ofNat 80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc
  15), (61, Int.negSucc 31), (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90,
  Int.negSucc 47), (132, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat
  8), (312, Int.ofNat 8), (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588,
  Int.ofNat 8), (648, Int.ofNat 8), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat 16),
  (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58, Int.negSucc 31), (59,
  Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc
  31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat 4), (282, Int.ofNat 16), (312,
  Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498, Int.ofNat 8), (528, Int.ofNat
  16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat 4), (678, Int.negSucc 3), (738,
  Int.negSucc 3), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48),
  (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
  Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat 48),
  (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23), (162,
  Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23), (282,
  Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
  Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
  Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
  Int.ofNat 8), (528, Int.ofNat 72), (588, Int.ofNat 72), (618, Int.ofNat 72), (648, Int.ofNat
  72), (678, Int.negSucc 71), (708, Int.negSucc 71), (738, Int.negSucc 71), (768, Int.ofNat 72),
  (30, Int.ofNat 20), (57, Int.negSucc 19), (88, Int.negSucc 39), (115, Int.ofNat 40), (528,
  Int.negSucc 19), (588, Int.negSucc 19), (738, Int.ofNat 20), (768, Int.negSucc 19), (813,
  Int.negSucc 19), (815, Int.ofNat 40), (1, Int.negSucc 7), (28, Int.ofNat 8), (30, Int.ofNat 16),
  (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88, Int.negSucc 7), (115,
  Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.ofNat
  8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (30, Int.ofNat 20), (57,
  Int.negSucc 19), (59, Int.negSucc 39), (86, Int.ofNat 40), (528, Int.negSucc 19), (618,
  Int.negSucc 19), (708, Int.ofNat 20), (768, Int.negSucc 19), (813, Int.negSucc 19), (814,
  Int.ofNat 40), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc 7),
  (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7), (812,
  Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 28), (30, Int.negSucc 27), (31, Int.ofNat
  28), (32, Int.ofNat 28), (57, Int.negSucc 27), (87, Int.negSucc 55), (88, Int.ofNat 56), (89,
  Int.negSucc 55), (90, Int.negSucc 55), (115, Int.ofNat 56), (468, Int.ofNat 28), (738, Int.ofNat
  28), (768, Int.negSucc 27), (813, Int.negSucc 27), (815, Int.ofNat 56), (0, Int.negSucc 55), (1,
  Int.ofNat 56), (2, Int.negSucc 55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.ofNat
  112), (30, Int.negSucc 111), (31, Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111),
  (58, Int.negSucc 55), (59, Int.ofNat 56), (60, Int.negSucc 55), (61, Int.negSucc 55), (86,
  Int.ofNat 56), (87, Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc
  55), (115, Int.ofNat 56), (468, Int.ofNat 56), (498, Int.ofNat 56), (558, Int.ofNat 56), (678,
  Int.ofNat 56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812, Int.ofNat
  56), (813, Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (29, Int.negSucc 3), (30,
  Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (57, Int.ofNat 4), (58, Int.ofNat 8),
  (59, Int.negSucc 7), (60, Int.ofNat 8), (61, Int.ofNat 8), (86, Int.negSucc 7), (498,
  Int.negSucc 3), (708, Int.negSucc 3), (768, Int.ofNat 4), (813, Int.ofNat 4), (814, Int.negSucc
  7), (0, Int.ofNat 32), (1, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28,
  Int.negSucc 31), (29, Int.negSucc 15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32,
  Int.negSucc 15), (57, Int.ofNat 16), (558, Int.negSucc 15), (678, Int.negSucc 15), (768,
  Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (29, Int.ofNat 12), (31, Int.negSucc
  11), (32, Int.negSucc 11), (57, Int.ofNat 12), (87, Int.negSucc 23), (89, Int.ofNat 24), (90,
  Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 11), (618, Int.negSucc 11), (678,
  Int.ofNat 12), (813, Int.ofNat 12), (815, Int.negSucc 23), (0, Int.negSucc 23), (2, Int.ofNat
  24), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32,
  Int.negSucc 47), (57, Int.ofNat 48), (58, Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat
  24), (86, Int.negSucc 23), (87, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115,
  Int.negSucc 23), (468, Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618,
  Int.negSucc 23), (812, Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815,
  Int.negSucc 23), (29, Int.ofNat 12), (31, Int.negSucc 11), (32, Int.negSucc 11), (57, Int.ofNat
  12), (58, Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (498,
  Int.negSucc 11), (588, Int.negSucc 11), (678, Int.ofNat 12), (813, Int.ofNat 12), (814,
  Int.negSucc 23), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8),
  (87, Int.ofNat 16), (89, Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
  Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc
  15), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.negSucc 31), (29,
  Int.negSucc 63), (31, Int.ofNat 64), (32, Int.negSucc 63), (57, Int.ofNat 64), (58, Int.ofNat
  32), (60, Int.negSucc 31), (61, Int.ofNat 32), (86, Int.negSucc 31), (87, Int.ofNat 32), (89,
  Int.negSucc 31), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 31), (558,
  Int.negSucc 31), (588, Int.negSucc 31), (648, Int.negSucc 31), (812, Int.negSucc 31), (813,
  Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (0, Int.ofNat 32), (2, Int.ofNat
  32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95), (32,
  Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61, Int.negSucc 31),
  (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90, Int.negSucc 95), (115,
  Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558, Int.negSucc 31), (618,
  Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768, Int.ofNat 32), (812,
  Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815, Int.negSucc 95), (29,
  Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (58, Int.ofNat 16),
  (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.negSucc 15), (498, Int.negSucc 7), (648,
  Int.negSucc 7), (738, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.negSucc
  7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.negSucc
  3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558, Int.ofNat 4), (588, Int.ofNat 4), (708,
  Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (0, Int.negSucc 7), (2, Int.negSucc
  7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc
  3), (57, Int.negSucc 3), (558, Int.ofNat 4), (618, Int.ofNat 4), (738, Int.negSucc 3), (812,
  Int.ofNat 8), (813, Int.negSucc 3), (798, Int.negSucc 39), (813, Int.ofNat 40), (840,
  Int.negSucc 39), (768, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (814,
  Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 32), (588, Int.ofNat 16), (798,
  Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
  Int.negSucc 15), (840, Int.ofNat 32), (618, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat
  16), (813, Int.negSucc 31), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32),
  (648, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814,
  Int.ofNat 16), (815, Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 24), (798, Int.negSucc
  23), (815, Int.ofNat 48), (840, Int.negSucc 47), (498, Int.ofNat 24), (798, Int.negSucc 23),
  (814, Int.ofNat 48), (840, Int.negSucc 47), (558, Int.ofNat 16), (798, Int.negSucc 15), (812,
  Int.ofNat 32), (840, Int.negSucc 31), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat
  8), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.ofNat 16), (90, Int.negSucc 15), (115,
  Int.negSucc 15), (738, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc
  7), (840, Int.ofNat 16), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
  Int.ofNat 8), (58, Int.ofNat 16), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.negSucc
  15), (708, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840,
  Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.ofNat 16), (814,
  Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 16), (798, Int.negSucc 3), (812,
  Int.ofNat 4), (814, Int.ofNat 4), (815, Int.negSucc 3), (840, Int.negSucc 3), (798, Int.negSucc
  3), (812, Int.ofNat 4), (814, Int.negSucc 3), (815, Int.ofNat 4), (840, Int.negSucc 3)]

def pilotColumns : List SV := [
  [(27, Int.ofNat 1)],
  [(27, Int.ofNat 2)],
  [(27, Int.ofNat 1)],
  [(27, Int.ofNat 1)],
  [],
  [],
  [(26, Int.negSucc 0)],
  [],
  [(25, Int.ofNat 1)],
  [(24, Int.ofNat 1)],
  [(23, Int.ofNat 1)],
  [(22, Int.negSucc 0)],
  [(21, Int.negSucc 0)],
  [(20, Int.negSucc 0)],
  [(18, Int.negSucc 0)],
  [(1, Int.ofNat 1)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

def pilotDenominator : ℤ := Int.ofNat 2

end VOA.DeligneAudit.D4Two.Certificate

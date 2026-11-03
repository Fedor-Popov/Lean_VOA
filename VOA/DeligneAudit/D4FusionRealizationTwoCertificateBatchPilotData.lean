/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoIntegerData

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

structure BatchPilotCase where
  color : ℕ
  mode : ℕ
  source : SV
  denominator : ℤ
  target : SV
  coordinates : List ℕ
  deriving Inhabited

def batchPilotColumns : List (List SV) := [
  [
    [],
    [],
    [],
    [],
    [],
    [],
    [(6, Int.ofNat 1)],
    [(7, Int.negSucc 1)],
    [(8, Int.ofNat 1)],
    [(9, Int.ofNat 1)],
    [(10, Int.negSucc 0)],
    [(11, Int.ofNat 1)],
    [(12, Int.negSucc 0)],
    [(13, Int.negSucc 0)],
    [(14, Int.negSucc 0)],
    [],
    [],
    [],
    [(18, Int.negSucc 0)],
    [(19, Int.ofNat 2)],
    [(20, Int.negSucc 0)],
    [(21, Int.negSucc 0)],
    [(22, Int.ofNat 1)],
    [(23, Int.negSucc 0)],
    [(24, Int.ofNat 1)],
    [(25, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [],
    []
  ],
  [
    [],
    [],
    [],
    [],
    [(4, Int.ofNat 1)],
    [(5, Int.ofNat 1)],
    [(6, Int.negSucc 1)],
    [(7, Int.ofNat 1)],
    [(8, Int.negSucc 0)],
    [(9, Int.negSucc 0)],
    [(10, Int.negSucc 0)],
    [],
    [],
    [],
    [(14, Int.ofNat 1)],
    [(15, Int.negSucc 0)],
    [(16, Int.negSucc 0)],
    [(17, Int.negSucc 0)],
    [(18, Int.ofNat 2)],
    [(19, Int.negSucc 0)],
    [(20, Int.ofNat 1)],
    [(21, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    [],
    [],
    [],
    [(26, Int.negSucc 0)],
    [(27, Int.ofNat 1)],
    []
  ],
  [
    [],
    [],
    [],
    [],
    [],
    [(5, Int.negSucc 1)],
    [(6, Int.ofNat 1)],
    [],
    [(8, Int.ofNat 1)],
    [(9, Int.negSucc 0)],
    [(10, Int.ofNat 1)],
    [(11, Int.negSucc 0)],
    [(12, Int.ofNat 1)],
    [(13, Int.negSucc 0)],
    [(14, Int.negSucc 0)],
    [],
    [],
    [(17, Int.ofNat 2)],
    [(18, Int.negSucc 0)],
    [],
    [(20, Int.negSucc 0)],
    [(21, Int.ofNat 1)],
    [(22, Int.negSucc 0)],
    [(23, Int.ofNat 1)],
    [(24, Int.negSucc 0)],
    [(25, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [],
    []
  ],
  [
    [],
    [],
    [],
    [],
    [(4, Int.negSucc 1)],
    [],
    [(6, Int.ofNat 1)],
    [],
    [(8, Int.negSucc 0)],
    [(9, Int.ofNat 1)],
    [(10, Int.ofNat 1)],
    [(11, Int.negSucc 0)],
    [(12, Int.negSucc 0)],
    [(13, Int.ofNat 1)],
    [(14, Int.negSucc 0)],
    [],
    [(16, Int.ofNat 2)],
    [],
    [(18, Int.negSucc 0)],
    [],
    [(20, Int.ofNat 1)],
    [(21, Int.negSucc 0)],
    [(22, Int.negSucc 0)],
    [(23, Int.ofNat 1)],
    [(24, Int.ofNat 1)],
    [(25, Int.negSucc 0)],
    [(26, Int.ofNat 1)],
    [],
    []
  ],
  [
    [],
    [],
    [],
    [(16, Int.negSucc 0)],
    [(1, Int.negSucc 0), (3, Int.ofNat 2)],
    [],
    [],
    [],
    [(6, Int.negSucc 0)],
    [],
    [],
    [(9, Int.negSucc 0)],
    [(10, Int.negSucc 0)],
    [],
    [(13, Int.negSucc 0)],
    [],
    [],
    [],
    [(20, Int.negSucc 0)],
    [],
    [],
    [(23, Int.ofNat 1)],
    [(24, Int.ofNat 1)],
    [],
    [],
    [(26, Int.ofNat 1)],
    [],
    [],
    []
  ],
  [
    [],
    [],
    [(17, Int.negSucc 0)],
    [],
    [],
    [(1, Int.negSucc 0), (2, Int.ofNat 2)],
    [],
    [],
    [],
    [(6, Int.negSucc 0)],
    [],
    [(8, Int.negSucc 0)],
    [],
    [(10, Int.negSucc 0)],
    [(12, Int.negSucc 0)],
    [],
    [],
    [],
    [(21, Int.negSucc 0)],
    [],
    [(23, Int.ofNat 1)],
    [],
    [(25, Int.ofNat 1)],
    [],
    [(26, Int.ofNat 1)],
    [],
    [],
    [],
    []
  ],
  [
    [],
    [(18, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [(0, Int.negSucc 0), (1, Int.ofNat 2), (2, Int.negSucc 0), (3, Int.negSucc 0)],
    [],
    [(4, Int.ofNat 1)],
    [(5, Int.ofNat 1)],
    [(7, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [(14, Int.ofNat 1)],
    [(20, Int.ofNat 1)],
    [(21, Int.ofNat 1)],
    [],
    [(22, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(27, Int.negSucc 0)],
    [],
    []
  ],
  [
    [(19, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, Int.ofNat 2), (1, Int.negSucc 0)],
    [],
    [],
    [(6, Int.ofNat 1)],
    [],
    [(8, Int.ofNat 1)],
    [(9, Int.ofNat 1)],
    [(11, Int.ofNat 1)],
    [],
    [],
    [],
    [(22, Int.ofNat 1)],
    [],
    [(24, Int.negSucc 0)],
    [(25, Int.negSucc 0)],
    [],
    [(26, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    []
  ],
  [
    [],
    [(20, Int.ofNat 1)],
    [],
    [(20, Int.ofNat 1)],
    [(18, Int.negSucc 0)],
    [],
    [(16, Int.ofNat 1)],
    [],
    [(0, Int.negSucc 0), (1, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.ofNat 1)],
    [],
    [],
    [(5, Int.ofNat 1)],
    [(7, Int.negSucc 0)],
    [],
    [],
    [(13, Int.negSucc 0)],
    [],
    [(23, Int.ofNat 1)],
    [],
    [(24, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [(27, Int.ofNat 1)],
    [],
    [],
    []
  ],
  [
    [],
    [(21, Int.ofNat 1)],
    [(21, Int.ofNat 1)],
    [],
    [],
    [(18, Int.negSucc 0)],
    [(17, Int.ofNat 1)],
    [],
    [],
    [(0, Int.negSucc 0), (1, Int.ofNat 1), (2, Int.ofNat 1), (3, Int.negSucc 0)],
    [],
    [(4, Int.ofNat 1)],
    [],
    [(7, Int.negSucc 0)],
    [],
    [(12, Int.negSucc 0)],
    [(23, Int.ofNat 1)],
    [],
    [],
    [(25, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [(27, Int.ofNat 1)],
    [],
    [],
    [],
    []
  ],
  [
    [(22, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [(19, Int.negSucc 0)],
    [(18, Int.ofNat 1)],
    [],
    [],
    [(0, Int.ofNat 1), (1, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.negSucc 0)],
    [],
    [(4, Int.ofNat 1)],
    [(5, Int.ofNat 1)],
    [],
    [(11, Int.negSucc 0)],
    [(24, Int.ofNat 1)],
    [(25, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [(27, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    []
  ],
  [
    [],
    [(23, Int.ofNat 1)],
    [(23, Int.ofNat 1)],
    [(23, Int.ofNat 1)],
    [(21, Int.ofNat 1)],
    [(20, Int.ofNat 1)],
    [],
    [],
    [(17, Int.ofNat 1)],
    [(16, Int.ofNat 1)],
    [],
    [(0, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.ofNat 1)],
    [],
    [],
    [(7, Int.negSucc 0)],
    [(10, Int.ofNat 1)],
    [],
    [],
    [],
    [(26, Int.negSucc 0)],
    [],
    [],
    [(27, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    []
  ],
  [
    [(24, Int.ofNat 1)],
    [(24, Int.ofNat 1)],
    [],
    [(24, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    [],
    [],
    [(20, Int.negSucc 0)],
    [(19, Int.negSucc 0)],
    [],
    [(16, Int.ofNat 1)],
    [],
    [(0, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.ofNat 1)],
    [],
    [(5, Int.ofNat 1)],
    [(9, Int.ofNat 1)],
    [],
    [(26, Int.ofNat 1)],
    [],
    [],
    [],
    [(27, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    []
  ],
  [
    [(25, Int.ofNat 1)],
    [(25, Int.ofNat 1)],
    [(25, Int.ofNat 1)],
    [],
    [],
    [(22, Int.ofNat 1)],
    [],
    [(21, Int.negSucc 0)],
    [],
    [(19, Int.negSucc 0)],
    [(17, Int.ofNat 1)],
    [],
    [],
    [(0, Int.ofNat 1), (2, Int.ofNat 1), (3, Int.negSucc 0)],
    [(4, Int.ofNat 1)],
    [(8, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [],
    [],
    [],
    [(27, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []
  ],
  [
    [(26, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [(26, Int.ofNat 1)],
    [(25, Int.ofNat 1)],
    [(24, Int.ofNat 1)],
    [],
    [(23, Int.negSucc 0)],
    [],
    [],
    [],
    [(19, Int.negSucc 0)],
    [(17, Int.ofNat 1)],
    [(16, Int.ofNat 1)],
    [(0, Int.ofNat 1), (1, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.ofNat 1)],
    [(6, Int.negSucc 0)],
    [],
    [],
    [(27, Int.negSucc 0)],
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
  ],
  [
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
  ],
  [
    [],
    [],
    [],
    [(4, Int.ofNat 1)],
    [],
    [],
    [(8, Int.negSucc 0)],
    [],
    [],
    [(11, Int.negSucc 0)],
    [(12, Int.negSucc 0)],
    [],
    [],
    [(14, Int.negSucc 0)],
    [],
    [],
    [(1, Int.ofNat 1), (3, Int.negSucc 1)],
    [],
    [],
    [],
    [(18, Int.negSucc 0)],
    [],
    [],
    [(21, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    [],
    [(25, Int.ofNat 1)],
    [],
    []
  ],
  [
    [],
    [],
    [(5, Int.ofNat 1)],
    [],
    [],
    [],
    [(9, Int.negSucc 0)],
    [],
    [(11, Int.negSucc 0)],
    [],
    [(13, Int.negSucc 0)],
    [],
    [(14, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [(1, Int.ofNat 1), (2, Int.negSucc 1)],
    [],
    [],
    [],
    [(18, Int.negSucc 0)],
    [],
    [(20, Int.ofNat 1)],
    [],
    [(22, Int.ofNat 1)],
    [(24, Int.ofNat 1)],
    [],
    []
  ],
  [
    [],
    [(6, Int.ofNat 1)],
    [],
    [],
    [(8, Int.ofNat 1)],
    [(9, Int.ofNat 1)],
    [],
    [(10, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(15, Int.ofNat 1)],
    [],
    [],
    [],
    [(0, Int.ofNat 1), (1, Int.negSucc 1), (2, Int.ofNat 1), (3, Int.ofNat 1)],
    [],
    [(16, Int.ofNat 1)],
    [(17, Int.ofNat 1)],
    [(19, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [(26, Int.negSucc 0)],
    []
  ],
  [
    [(7, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [(10, Int.ofNat 1)],
    [],
    [(12, Int.ofNat 1)],
    [(13, Int.ofNat 1)],
    [],
    [(14, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(0, Int.negSucc 1), (1, Int.ofNat 1)],
    [],
    [],
    [(18, Int.ofNat 1)],
    [],
    [(20, Int.negSucc 0)],
    [(21, Int.negSucc 0)],
    [(23, Int.negSucc 0)],
    [],
    []
  ],
  [
    [],
    [(8, Int.negSucc 0)],
    [],
    [(8, Int.negSucc 0)],
    [],
    [(11, Int.negSucc 0)],
    [],
    [(12, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [(15, Int.ofNat 1)],
    [],
    [],
    [(6, Int.negSucc 0)],
    [],
    [(4, Int.ofNat 1)],
    [],
    [(0, Int.ofNat 1), (1, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.negSucc 0)],
    [],
    [],
    [(17, Int.negSucc 0)],
    [(19, Int.ofNat 1)],
    [],
    [],
    [(25, Int.negSucc 0)],
    []
  ],
  [
    [],
    [(9, Int.negSucc 0)],
    [(9, Int.negSucc 0)],
    [],
    [(11, Int.negSucc 0)],
    [],
    [],
    [(13, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [(15, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [(6, Int.negSucc 0)],
    [(5, Int.ofNat 1)],
    [],
    [],
    [(0, Int.ofNat 1), (1, Int.negSucc 0), (2, Int.negSucc 0), (3, Int.ofNat 1)],
    [],
    [(16, Int.negSucc 0)],
    [],
    [(19, Int.ofNat 1)],
    [],
    [(24, Int.negSucc 0)],
    []
  ],
  [
    [(10, Int.negSucc 0)],
    [(10, Int.negSucc 0)],
    [],
    [],
    [(12, Int.negSucc 0)],
    [(13, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [(15, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(7, Int.negSucc 0)],
    [(6, Int.ofNat 1)],
    [],
    [],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.ofNat 1)],
    [],
    [(16, Int.negSucc 0)],
    [(17, Int.negSucc 0)],
    [],
    [(23, Int.negSucc 0)],
    []
  ],
  [
    [],
    [(11, Int.negSucc 0)],
    [(11, Int.negSucc 0)],
    [(11, Int.negSucc 0)],
    [],
    [],
    [],
    [(14, Int.ofNat 1)],
    [],
    [],
    [(15, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [(9, Int.negSucc 0)],
    [(8, Int.negSucc 0)],
    [],
    [],
    [(5, Int.negSucc 0)],
    [(4, Int.negSucc 0)],
    [],
    [(0, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.negSucc 0)],
    [],
    [],
    [(19, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    []
  ],
  [
    [(12, Int.negSucc 0)],
    [(12, Int.negSucc 0)],
    [],
    [(12, Int.negSucc 0)],
    [],
    [(14, Int.negSucc 0)],
    [],
    [],
    [],
    [(15, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [(10, Int.negSucc 0)],
    [],
    [],
    [(8, Int.ofNat 1)],
    [(7, Int.ofNat 1)],
    [],
    [(4, Int.negSucc 0)],
    [],
    [(0, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.negSucc 0)],
    [],
    [(17, Int.negSucc 0)],
    [(21, Int.ofNat 1)],
    []
  ],
  [
    [(13, Int.negSucc 0)],
    [(13, Int.negSucc 0)],
    [(13, Int.negSucc 0)],
    [],
    [(14, Int.negSucc 0)],
    [],
    [],
    [],
    [(15, Int.negSucc 0)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(10, Int.negSucc 0)],
    [],
    [(9, Int.ofNat 1)],
    [],
    [(7, Int.ofNat 1)],
    [(5, Int.negSucc 0)],
    [],
    [],
    [(0, Int.negSucc 0), (2, Int.negSucc 0), (3, Int.ofNat 1)],
    [(16, Int.negSucc 0)],
    [(20, Int.ofNat 1)],
    []
  ],
  [
    [(14, Int.negSucc 0)],
    [(14, Int.negSucc 0)],
    [(14, Int.negSucc 0)],
    [(14, Int.negSucc 0)],
    [],
    [],
    [(15, Int.ofNat 1)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(13, Int.negSucc 0)],
    [(12, Int.negSucc 0)],
    [],
    [(11, Int.ofNat 1)],
    [],
    [],
    [],
    [(7, Int.ofNat 1)],
    [(5, Int.negSucc 0)],
    [(4, Int.negSucc 0)],
    [(0, Int.negSucc 0), (1, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.negSucc 0)],
    [(18, Int.ofNat 1)],
    []
  ],
  [
    [(15, Int.negSucc 0)],
    [(15, Int.negSucc 1)],
    [(15, Int.negSucc 0)],
    [(15, Int.negSucc 0)],
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
    [],
    [],
    [(14, Int.ofNat 1)],
    [],
    [(13, Int.ofNat 1)],
    [(12, Int.ofNat 1)],
    [(11, Int.ofNat 1)],
    [(10, Int.negSucc 0)],
    [(9, Int.negSucc 0)],
    [(8, Int.negSucc 0)],
    [(6, Int.ofNat 1)],
    [(1, Int.negSucc 0)],
    []
  ]
]

set_option maxHeartbeats 4000000 in
-- The32 largest literal sparse relations need additional elaboration steps.
def batchPilotCases : List BatchPilotCase := [
  { color := 15, mode := 3, source := [(15, Int.negSucc 3), (44, Int.ofNat 12), (73, Int.negSucc
    7), (102, Int.negSucc 7), (188, Int.ofNat 8), (245, Int.ofNat 2), (273, Int.ofNat 2), (357,
    Int.ofNat 2), (385, Int.ofNat 2), (412, Int.ofNat 8), (435, Int.negSucc 3), (436, Int.ofNat
    12), (437, Int.negSucc 7), (438, Int.negSucc 7)],
    denominator := Int.ofNat 2,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 24), (3, Int.negSucc 47),
    (29, Int.ofNat 24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59,
    Int.ofNat 24), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89,
    Int.negSucc 47), (90, Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252,
    Int.ofNat 24), (468, Int.ofNat 72), (528, Int.ofNat 24), (588, Int.ofNat 24), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (59, Int.ofNat 8), (61, Int.negSucc 15), (88,
    Int.ofNat 8), (89, Int.negSucc 15), (192, Int.ofNat 4), (252, Int.ofNat 4), (282, Int.ofNat
    4), (342, Int.negSucc 3), (528, Int.ofNat 4), (588, Int.ofNat 4), (618, Int.ofNat 4), (678,
    Int.negSucc 3), (0, Int.ofNat 8), (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16),
    (29, Int.negSucc 19), (30, Int.ofNat 48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58,
    Int.ofNat 8), (59, Int.negSucc 19), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16),
    (88, Int.negSucc 35), (89, Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192,
    Int.negSucc 11), (252, Int.negSucc 3), (468, Int.negSucc 3), (528, Int.negSucc 11), (588,
    Int.negSucc 3), (0, Int.ofNat 24), (1, Int.negSucc 71), (2, Int.ofNat 48), (3, Int.ofNat 48),
    (29, Int.negSucc 71), (30, Int.ofNat 192), (31, Int.negSucc 119), (32, Int.negSucc 119), (58,
    Int.ofNat 48), (59, Int.negSucc 119), (60, Int.ofNat 72), (61, Int.ofNat 72), (87, Int.ofNat
    48), (88, Int.negSucc 119), (89, Int.ofNat 72), (90, Int.ofNat 72), (132, Int.negSucc 11),
    (162, Int.negSucc 11), (192, Int.negSucc 47), (252, Int.negSucc 11), (282, Int.negSucc 11),
    (468, Int.negSucc 11), (498, Int.negSucc 11), (528, Int.negSucc 47), (588, Int.negSucc 11),
    (618, Int.negSucc 11), (1, Int.ofNat 4), (2, Int.negSucc 7), (29, Int.ofNat 4), (30,
    Int.negSucc 23), (31, Int.ofNat 36), (32, Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat
    36), (60, Int.negSucc 47), (61, Int.negSucc 7), (88, Int.ofNat 4), (89, Int.negSucc 7), (162,
    Int.ofNat 12), (192, Int.ofNat 4), (282, Int.ofNat 4), (498, Int.ofNat 12), (528, Int.ofNat
    4), (618, Int.ofNat 4), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30,
    Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat
    4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588,
    Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 7), (252,
    Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372,
    Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat
    80), (2, Int.negSucc 31), (3, Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 31), (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31),
    (90, Int.negSucc 47), (132, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8),
    (588, Int.ofNat 8), (648, Int.ofNat 8), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat
    16), (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58, Int.negSucc 31), (59,
    Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88, Int.ofNat 16), (89,
    Int.negSucc 31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat 4), (282, Int.ofNat
    16), (312, Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498, Int.ofNat 8), (528,
    Int.ofNat 16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat 4), (678, Int.negSucc
    3), (738, Int.negSucc 3), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3,
    Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 72), (588, Int.ofNat 72), (618, Int.ofNat
    72), (648, Int.ofNat 72), (678, Int.negSucc 71), (708, Int.negSucc 71), (738, Int.negSucc 71),
    (768, Int.ofNat 72), (30, Int.ofNat 20), (57, Int.negSucc 19), (88, Int.negSucc 39), (115,
    Int.ofNat 40), (528, Int.negSucc 19), (588, Int.negSucc 19), (738, Int.ofNat 20), (768,
    Int.negSucc 19), (813, Int.negSucc 19), (815, Int.ofNat 40), (1, Int.negSucc 7), (28,
    Int.ofNat 8), (30, Int.ofNat 16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat
    8), (88, Int.negSucc 7), (115, Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (30, Int.ofNat 20), (57, Int.negSucc 19), (59, Int.negSucc 39), (86, Int.ofNat 40), (528,
    Int.negSucc 19), (618, Int.negSucc 19), (708, Int.ofNat 20), (768, Int.negSucc 19), (813,
    Int.negSucc 19), (814, Int.ofNat 40), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat
    8), (57, Int.negSucc 7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 28), (30,
    Int.negSucc 27), (31, Int.ofNat 28), (32, Int.ofNat 28), (57, Int.negSucc 27), (87,
    Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 28), (738, Int.ofNat 28), (768, Int.negSucc 27), (813,
    Int.negSucc 27), (815, Int.ofNat 56), (0, Int.negSucc 55), (1, Int.ofNat 56), (2, Int.negSucc
    55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.ofNat 112), (30, Int.negSucc 111), (31,
    Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111), (58, Int.negSucc 55), (59,
    Int.ofNat 56), (60, Int.negSucc 55), (61, Int.negSucc 55), (86, Int.ofNat 56), (87,
    Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 56), (498, Int.ofNat 56), (558, Int.ofNat 56), (678, Int.ofNat
    56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812, Int.ofNat 56),
    (813, Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (29, Int.negSucc 3), (30,
    Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (57, Int.ofNat 4), (58, Int.ofNat 8),
    (59, Int.negSucc 7), (60, Int.ofNat 8), (61, Int.ofNat 8), (86, Int.negSucc 7), (498,
    Int.negSucc 3), (708, Int.negSucc 3), (768, Int.ofNat 4), (813, Int.ofNat 4), (814,
    Int.negSucc 7), (0, Int.ofNat 32), (1, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32),
    (28, Int.negSucc 31), (29, Int.negSucc 15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (558, Int.negSucc 15), (678, Int.negSucc 15), (768,
    Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (29, Int.ofNat 12), (31,
    Int.negSucc 11), (32, Int.negSucc 11), (57, Int.ofNat 12), (87, Int.negSucc 23), (89,
    Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 11), (618,
    Int.negSucc 11), (678, Int.ofNat 12), (813, Int.ofNat 12), (815, Int.negSucc 23), (0,
    Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.ofNat
    48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.negSucc 23),
    (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.negSucc 23), (89,
    Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (498,
    Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812, Int.negSucc 23), (813,
    Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29, Int.ofNat 12), (31,
    Int.negSucc 11), (32, Int.negSucc 11), (57, Int.ofNat 12), (58, Int.negSucc 23), (60,
    Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (498, Int.negSucc 11), (588,
    Int.negSucc 11), (678, Int.ofNat 12), (813, Int.ofNat 12), (814, Int.negSucc 23), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16),
    (89, Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (648,
    Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat
    32), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc 63), (31,
    Int.ofNat 64), (32, Int.negSucc 63), (57, Int.ofNat 64), (58, Int.ofNat 32), (60, Int.negSucc
    31), (61, Int.ofNat 32), (86, Int.negSucc 31), (87, Int.ofNat 32), (89, Int.negSucc 31), (90,
    Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 31), (558, Int.negSucc 31), (588,
    Int.negSucc 31), (648, Int.negSucc 31), (812, Int.negSucc 31), (813, Int.ofNat 64), (814,
    Int.negSucc 31), (815, Int.negSucc 31), (0, Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc
    31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95), (32, Int.ofNat 96),
    (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61, Int.negSucc 31), (86,
    Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90, Int.negSucc 95), (115,
    Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558, Int.negSucc 31), (618,
    Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768, Int.ofNat 32), (812,
    Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815, Int.negSucc 95), (29,
    Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (58, Int.ofNat 16),
    (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.negSucc 15), (498, Int.negSucc 7), (648,
    Int.negSucc 7), (738, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.negSucc
    7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.ofNat 4), (31,
    Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558, Int.ofNat 4), (588, Int.ofNat
    4), (708, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (0, Int.negSucc 7), (2,
    Int.negSucc 7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.ofNat 4),
    (32, Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4), (618, Int.ofNat 4), (738,
    Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798, Int.negSucc 39), (813,
    Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 32), (588,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814, Int.negSucc 15), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (840,
    Int.ofNat 32), (468, Int.ofNat 24), (798, Int.negSucc 23), (815, Int.ofNat 48), (840,
    Int.negSucc 47), (498, Int.ofNat 24), (798, Int.negSucc 23), (814, Int.ofNat 48), (840,
    Int.negSucc 47), (558, Int.ofNat 16), (798, Int.negSucc 15), (812, Int.ofNat 32), (840,
    Int.negSucc 31), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat
    8), (87, Int.ofNat 16), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.negSucc 15), (738,
    Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat
    16), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (58,
    Int.ofNat 16), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.negSucc 15), (708,
    Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat
    16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.ofNat 16), (814, Int.negSucc 15),
    (815, Int.negSucc 15), (840, Int.ofNat 16), (798, Int.negSucc 3), (812, Int.ofNat 4), (814,
    Int.ofNat 4), (815, Int.negSucc 3), (840, Int.negSucc 3), (798, Int.negSucc 3), (812,
    Int.ofNat 4), (814, Int.negSucc 3), (815, Int.ofNat 4), (840, Int.negSucc 3)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 3, source := [(14, Int.negSucc 1), (43, Int.ofNat 8), (72, Int.negSucc
    5), (101, Int.negSucc 5), (129, Int.ofNat 2), (157, Int.ofNat 2), (353, Int.ofNat 2), (381,
    Int.ofNat 2), (406, Int.negSucc 1), (407, Int.ofNat 8), (408, Int.negSucc 5), (409,
    Int.negSucc 5), (453, Int.negSucc 1), (537, Int.negSucc 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 56), (32, Int.negSucc 111), (88, Int.negSucc 111), (90, Int.ofNat
    224), (132, Int.negSucc 55), (468, Int.negSucc 55), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (30, Int.negSucc
    15), (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.negSucc 23), (1, Int.ofNat 60), (2, Int.negSucc 23), (3, Int.negSucc
    47), (29, Int.ofNat 60), (30, Int.negSucc 143), (31, Int.ofNat 60), (32, Int.ofNat 108), (58,
    Int.negSucc 23), (59, Int.ofNat 60), (60, Int.negSucc 23), (61, Int.negSucc 47), (87,
    Int.negSucc 47), (88, Int.ofNat 108), (89, Int.negSucc 47), (90, Int.negSucc 71), (132,
    Int.ofNat 12), (192, Int.ofNat 36), (252, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat
    36), (588, Int.ofNat 12), (0, Int.ofNat 48), (1, Int.negSucc 143), (2, Int.ofNat 96), (3,
    Int.ofNat 96), (29, Int.negSucc 143), (30, Int.ofNat 384), (31, Int.negSucc 239), (32,
    Int.negSucc 239), (58, Int.ofNat 96), (59, Int.negSucc 239), (60, Int.ofNat 144), (61,
    Int.ofNat 144), (87, Int.ofNat 96), (88, Int.negSucc 239), (89, Int.ofNat 144), (90, Int.ofNat
    144), (132, Int.negSucc 23), (162, Int.negSucc 23), (192, Int.negSucc 95), (252, Int.negSucc
    23), (282, Int.negSucc 23), (468, Int.negSucc 23), (498, Int.negSucc 23), (528, Int.negSucc
    95), (588, Int.negSucc 23), (618, Int.negSucc 23), (1, Int.ofNat 8), (2, Int.negSucc 15), (29,
    Int.ofNat 8), (30, Int.negSucc 47), (31, Int.ofNat 72), (32, Int.ofNat 8), (58, Int.negSucc
    15), (59, Int.ofNat 72), (60, Int.negSucc 95), (61, Int.negSucc 15), (88, Int.ofNat 8), (89,
    Int.negSucc 15), (162, Int.ofNat 24), (192, Int.ofNat 8), (282, Int.ofNat 8), (498, Int.ofNat
    24), (528, Int.ofNat 8), (618, Int.ofNat 8), (1, Int.ofNat 16), (3, Int.negSucc 31), (29,
    Int.ofNat 16), (30, Int.negSucc 15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat
    16), (192, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528,
    Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc
    15), (252, Int.negSucc 15), (282, Int.negSucc 15), (312, Int.negSucc 15), (342, Int.ofNat 16),
    (372, Int.ofNat 16), (402, Int.ofNat 16), (432, Int.negSucc 15), (528, Int.negSucc 15), (588,
    Int.negSucc 15), (618, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (708,
    Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (0, Int.negSucc 47), (1, Int.ofNat
    80), (2, Int.negSucc 31), (3, Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 31), (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31),
    (90, Int.negSucc 47), (132, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8),
    (588, Int.ofNat 8), (648, Int.ofNat 8), (1, Int.ofNat 32), (2, Int.negSucc 63), (29, Int.ofNat
    32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58, Int.negSucc 63), (59,
    Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88, Int.ofNat 32), (89,
    Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat
    32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498, Int.ofNat 16),
    (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (738, Int.negSucc 7), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat
    16), (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 88), (588, Int.ofNat 88), (618, Int.ofNat
    88), (648, Int.ofNat 88), (678, Int.negSucc 87), (708, Int.negSucc 87), (738, Int.negSucc 87),
    (768, Int.ofNat 88), (30, Int.ofNat 32), (57, Int.negSucc 31), (88, Int.negSucc 63), (115,
    Int.ofNat 64), (528, Int.negSucc 31), (588, Int.negSucc 31), (738, Int.ofNat 32), (768,
    Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (1, Int.negSucc 7), (28,
    Int.ofNat 8), (30, Int.ofNat 16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat
    8), (88, Int.negSucc 7), (115, Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (30, Int.ofNat 32), (57, Int.negSucc 31), (59, Int.negSucc 63), (86, Int.ofNat 64), (528,
    Int.negSucc 31), (618, Int.negSucc 31), (708, Int.ofNat 32), (768, Int.negSucc 31), (813,
    Int.negSucc 31), (814, Int.ofNat 64), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat
    8), (57, Int.negSucc 7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 32), (30,
    Int.negSucc 31), (31, Int.ofNat 32), (32, Int.ofNat 32), (57, Int.negSucc 31), (87,
    Int.negSucc 63), (88, Int.ofNat 64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115,
    Int.ofNat 64), (468, Int.ofNat 32), (738, Int.ofNat 32), (768, Int.negSucc 31), (813,
    Int.negSucc 31), (815, Int.ofNat 64), (0, Int.negSucc 55), (1, Int.ofNat 56), (2, Int.negSucc
    55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.ofNat 112), (30, Int.negSucc 111), (31,
    Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111), (58, Int.negSucc 55), (59,
    Int.ofNat 56), (60, Int.negSucc 55), (61, Int.negSucc 55), (86, Int.ofNat 56), (87,
    Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 56), (498, Int.ofNat 56), (558, Int.ofNat 56), (678, Int.ofNat
    56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812, Int.ofNat 56),
    (813, Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (0, Int.ofNat 48), (1,
    Int.negSucc 47), (2, Int.ofNat 48), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.negSucc
    23), (30, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat 24), (558,
    Int.negSucc 23), (678, Int.negSucc 23), (768, Int.ofNat 24), (812, Int.negSucc 47), (813,
    Int.ofNat 24), (29, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat
    24), (87, Int.negSucc 47), (89, Int.ofNat 48), (90, Int.ofNat 48), (115, Int.negSucc 47),
    (468, Int.negSucc 23), (618, Int.negSucc 23), (678, Int.ofNat 24), (813, Int.ofNat 24), (815,
    Int.negSucc 47), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87,
    Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468,
    Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812,
    Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat 24), (58,
    Int.negSucc 47), (60, Int.ofNat 48), (61, Int.ofNat 48), (86, Int.negSucc 47), (498,
    Int.negSucc 23), (588, Int.negSucc 23), (678, Int.ofNat 24), (813, Int.ofNat 24), (814,
    Int.negSucc 47), (29, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.negSucc 15), (57,
    Int.ofNat 16), (87, Int.ofNat 32), (89, Int.negSucc 31), (90, Int.ofNat 32), (115, Int.negSucc
    31), (468, Int.negSucc 15), (648, Int.negSucc 15), (708, Int.ofNat 16), (813, Int.ofNat 16),
    (815, Int.negSucc 31), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.ofNat 32), (28,
    Int.negSucc 31), (29, Int.negSucc 63), (31, Int.ofNat 64), (32, Int.negSucc 63), (57,
    Int.ofNat 64), (58, Int.ofNat 32), (60, Int.negSucc 31), (61, Int.ofNat 32), (86, Int.negSucc
    31), (87, Int.ofNat 32), (89, Int.negSucc 31), (90, Int.ofNat 32), (115, Int.negSucc 31),
    (468, Int.negSucc 31), (558, Int.negSucc 31), (588, Int.negSucc 31), (648, Int.negSucc 31),
    (812, Int.negSucc 31), (813, Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (0,
    Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc
    95), (31, Int.negSucc 95), (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60,
    Int.ofNat 32), (61, Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat
    96), (90, Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31),
    (558, Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31),
    (768, Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57,
    Int.ofNat 16), (58, Int.ofNat 32), (60, Int.ofNat 32), (61, Int.negSucc 31), (86, Int.negSucc
    31), (498, Int.negSucc 15), (648, Int.negSucc 15), (738, Int.ofNat 16), (813, Int.ofNat 16),
    (814, Int.negSucc 31), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28,
    Int.ofNat 16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.negSucc 7),
    (558, Int.ofNat 8), (588, Int.ofNat 8), (708, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat
    16), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (558,
    Int.ofNat 8), (618, Int.ofNat 8), (738, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc
    7), (798, Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16),
    (798, Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15),
    (840, Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 32), (798, Int.negSucc 31), (815,
    Int.ofNat 64), (840, Int.negSucc 63), (498, Int.ofNat 32), (798, Int.negSucc 31), (814,
    Int.ofNat 64), (840, Int.negSucc 63), (558, Int.ofNat 16), (798, Int.negSucc 15), (812,
    Int.ofNat 32), (840, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32,
    Int.ofNat 16), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat 32), (90, Int.negSucc
    31), (115, Int.negSucc 31), (738, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16),
    (813, Int.negSucc 15), (840, Int.ofNat 32), (29, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 32), (60, Int.negSucc 31), (61, Int.ofNat
    32), (86, Int.negSucc 31), (708, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16),
    (813, Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 24), (812, Int.negSucc 23), (813,
    Int.ofNat 24), (814, Int.negSucc 23), (815, Int.negSucc 23), (840, Int.ofNat 24), (798,
    Int.negSucc 7), (812, Int.ofNat 8), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.negSucc 7), (798, Int.negSucc 7), (812, Int.ofNat 8), (814, Int.negSucc 7), (815,
    Int.ofNat 8), (840, Int.negSucc 7)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 3, source := [(14, Int.negSucc 2), (43, Int.ofNat 4), (72, Int.negSucc
    0), (101, Int.negSucc 2), (129, Int.ofNat 1), (214, Int.negSucc 0), (326, Int.negSucc 0),
    (381, Int.ofNat 1), (406, Int.negSucc 2), (407, Int.ofNat 4), (408, Int.negSucc 0), (409,
    Int.negSucc 2), (453, Int.negSucc 0), (537, Int.negSucc 0)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 56), (32, Int.negSucc 111), (88, Int.negSucc 111), (90, Int.ofNat
    224), (132, Int.negSucc 55), (468, Int.negSucc 55), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (0, Int.negSucc
    23), (1, Int.ofNat 60), (2, Int.negSucc 23), (3, Int.negSucc 47), (29, Int.ofNat 60), (30,
    Int.negSucc 143), (31, Int.ofNat 60), (32, Int.ofNat 108), (58, Int.negSucc 23), (59,
    Int.ofNat 60), (60, Int.negSucc 23), (61, Int.negSucc 47), (87, Int.negSucc 47), (88,
    Int.ofNat 108), (89, Int.negSucc 47), (90, Int.negSucc 71), (132, Int.ofNat 12), (192,
    Int.ofNat 36), (252, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat 36), (588, Int.ofNat
    12), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 32), (3, Int.ofNat 32), (29,
    Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 79), (32, Int.negSucc 79), (58,
    Int.ofNat 32), (59, Int.negSucc 79), (60, Int.ofNat 48), (61, Int.ofNat 48), (87, Int.ofNat
    32), (88, Int.negSucc 79), (89, Int.ofNat 48), (90, Int.ofNat 48), (132, Int.negSucc 7), (162,
    Int.negSucc 7), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 7), (468,
    Int.negSucc 7), (498, Int.negSucc 7), (528, Int.negSucc 31), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (1, Int.ofNat 32), (3, Int.negSucc 63), (29, Int.ofNat 32), (30, Int.negSucc
    31), (32, Int.ofNat 32), (87, Int.negSucc 63), (88, Int.ofNat 32), (192, Int.ofNat 16), (252,
    Int.ofNat 16), (312, Int.ofNat 16), (372, Int.negSucc 15), (528, Int.ofNat 16), (588,
    Int.ofNat 16), (648, Int.ofNat 16), (708, Int.negSucc 15), (192, Int.negSucc 15), (252,
    Int.negSucc 15), (282, Int.negSucc 15), (312, Int.negSucc 15), (342, Int.ofNat 16), (372,
    Int.ofNat 16), (402, Int.ofNat 16), (432, Int.negSucc 15), (528, Int.negSucc 15), (588,
    Int.negSucc 15), (618, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (708,
    Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (0, Int.ofNat 16), (1, Int.negSucc 47), (2,
    Int.ofNat 16), (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc
    47), (32, Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61,
    Int.ofNat 48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat
    80), (132, Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (0, Int.negSucc 95), (1, Int.ofNat 72), (2, Int.negSucc
    15), (3, Int.negSucc 15), (29, Int.ofNat 72), (30, Int.negSucc 47), (31, Int.ofNat 8), (32,
    Int.ofNat 8), (58, Int.negSucc 15), (59, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat
    8), (192, Int.ofNat 8), (222, Int.ofNat 24), (312, Int.ofNat 8), (528, Int.ofNat 8), (558,
    Int.ofNat 24), (648, Int.ofNat 8), (528, Int.ofNat 88), (588, Int.ofNat 88), (618, Int.ofNat
    88), (648, Int.ofNat 88), (678, Int.negSucc 87), (708, Int.negSucc 87), (738, Int.negSucc 87),
    (768, Int.ofNat 88), (30, Int.ofNat 32), (57, Int.negSucc 31), (88, Int.negSucc 63), (115,
    Int.ofNat 64), (528, Int.negSucc 31), (588, Int.negSucc 31), (738, Int.ofNat 32), (768,
    Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (1, Int.negSucc 7), (28,
    Int.ofNat 8), (30, Int.ofNat 16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat
    8), (88, Int.negSucc 7), (115, Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (30, Int.ofNat 8), (57, Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528,
    Int.negSucc 7), (618, Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813,
    Int.negSucc 7), (814, Int.ofNat 16), (1, Int.negSucc 63), (28, Int.ofNat 64), (30, Int.ofNat
    32), (57, Int.negSucc 31), (528, Int.negSucc 31), (648, Int.negSucc 31), (678, Int.ofNat 32),
    (768, Int.negSucc 31), (812, Int.ofNat 64), (813, Int.negSucc 31), (29, Int.ofNat 32), (30,
    Int.negSucc 31), (31, Int.ofNat 32), (32, Int.ofNat 32), (57, Int.negSucc 31), (87,
    Int.negSucc 63), (88, Int.ofNat 64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115,
    Int.ofNat 64), (468, Int.ofNat 32), (738, Int.ofNat 32), (768, Int.negSucc 31), (813,
    Int.negSucc 31), (815, Int.ofNat 64), (0, Int.negSucc 55), (1, Int.ofNat 56), (2, Int.negSucc
    55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.ofNat 112), (30, Int.negSucc 111), (31,
    Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111), (58, Int.negSucc 55), (59,
    Int.ofNat 56), (60, Int.negSucc 55), (61, Int.negSucc 55), (86, Int.ofNat 56), (87,
    Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 56), (498, Int.ofNat 56), (558, Int.ofNat 56), (678, Int.ofNat
    56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812, Int.ofNat 56),
    (813, Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (29, Int.negSucc 23), (30,
    Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat 24), (58, Int.ofNat
    48), (59, Int.negSucc 47), (60, Int.ofNat 48), (61, Int.ofNat 48), (86, Int.negSucc 47), (498,
    Int.negSucc 23), (708, Int.negSucc 23), (768, Int.ofNat 24), (813, Int.ofNat 24), (814,
    Int.negSucc 47), (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57,
    Int.ofNat 16), (87, Int.negSucc 31), (89, Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc
    31), (468, Int.negSucc 15), (618, Int.negSucc 15), (678, Int.ofNat 16), (813, Int.ofNat 16),
    (815, Int.negSucc 31), (0, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28,
    Int.negSucc 31), (29, Int.ofNat 64), (31, Int.negSucc 63), (32, Int.negSucc 63), (57,
    Int.ofNat 64), (58, Int.negSucc 31), (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc
    31), (87, Int.negSucc 31), (89, Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31),
    (468, Int.negSucc 31), (498, Int.negSucc 31), (588, Int.negSucc 31), (618, Int.negSucc 31),
    (812, Int.negSucc 31), (813, Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.ofNat 16),
    (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (588,
    Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (29,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.ofNat 24), (87, Int.ofNat
    48), (89, Int.negSucc 47), (90, Int.ofNat 48), (115, Int.negSucc 47), (468, Int.negSucc 23),
    (648, Int.negSucc 23), (708, Int.ofNat 24), (813, Int.ofNat 24), (815, Int.negSucc 47), (0,
    Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc
    47), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60,
    Int.negSucc 23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89,
    Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558,
    Int.negSucc 23), (588, Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813,
    Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 32), (2, Int.ofNat
    32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95),
    (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61,
    Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90,
    Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558,
    Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc
    7), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (498,
    Int.ofNat 8), (648, Int.ofNat 8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat
    16), (0, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.ofNat 48), (28, Int.negSucc 47), (29,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.ofNat 24), (558,
    Int.negSucc 23), (588, Int.negSucc 23), (708, Int.ofNat 24), (812, Int.negSucc 47), (813,
    Int.ofNat 24), (0, Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc 31), (28, Int.negSucc
    31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57, Int.ofNat 16), (558,
    Int.negSucc 15), (618, Int.negSucc 15), (738, Int.ofNat 16), (812, Int.negSucc 31), (813,
    Int.ofNat 16), (798, Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815,
    Int.negSucc 15), (840, Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840,
    Int.ofNat 32), (618, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 32), (798,
    Int.negSucc 31), (815, Int.ofNat 64), (840, Int.negSucc 63), (498, Int.ofNat 16), (798,
    Int.negSucc 15), (814, Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 32), (798,
    Int.negSucc 31), (812, Int.ofNat 64), (840, Int.negSucc 63), (29, Int.negSucc 15), (31,
    Int.negSucc 15), (32, Int.ofNat 16), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat
    32), (90, Int.negSucc 31), (115, Int.negSucc 31), (738, Int.negSucc 15), (768, Int.ofNat 16),
    (798, Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32), (0, Int.negSucc 31), (2,
    Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.ofNat 16), (31, Int.negSucc
    15), (32, Int.negSucc 15), (57, Int.ofNat 16), (678, Int.negSucc 15), (768, Int.ofNat 16),
    (798, Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 24), (812,
    Int.negSucc 23), (813, Int.ofNat 24), (814, Int.negSucc 23), (815, Int.negSucc 23), (840,
    Int.ofNat 24), (798, Int.negSucc 7), (812, Int.ofNat 8), (814, Int.ofNat 8), (815, Int.negSucc
    7), (840, Int.negSucc 7), (798, Int.negSucc 7), (812, Int.negSucc 7), (814, Int.ofNat 8),
    (815, Int.ofNat 8), (840, Int.negSucc 7)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 2, source := [(14, Int.negSucc 1), (43, Int.ofNat 8), (72, Int.negSucc
    5), (101, Int.negSucc 5), (129, Int.ofNat 2), (157, Int.ofNat 2), (353, Int.ofNat 2), (381,
    Int.ofNat 2), (406, Int.negSucc 1), (407, Int.ofNat 8), (408, Int.negSucc 5), (409,
    Int.negSucc 5), (453, Int.negSucc 1), (537, Int.negSucc 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 48), (32, Int.negSucc 95), (88, Int.negSucc 95), (90, Int.ofNat
    192), (132, Int.negSucc 47), (468, Int.negSucc 47), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (30, Int.negSucc
    15), (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.negSucc 23), (1, Int.ofNat 60), (2, Int.negSucc 23), (3, Int.negSucc
    47), (29, Int.ofNat 60), (30, Int.negSucc 143), (31, Int.ofNat 60), (32, Int.ofNat 108), (58,
    Int.negSucc 23), (59, Int.ofNat 60), (60, Int.negSucc 23), (61, Int.negSucc 47), (87,
    Int.negSucc 47), (88, Int.ofNat 108), (89, Int.negSucc 47), (90, Int.negSucc 71), (132,
    Int.ofNat 12), (192, Int.ofNat 36), (252, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat
    36), (588, Int.ofNat 12), (0, Int.ofNat 48), (1, Int.negSucc 143), (2, Int.ofNat 96), (3,
    Int.ofNat 96), (29, Int.negSucc 143), (30, Int.ofNat 384), (31, Int.negSucc 239), (32,
    Int.negSucc 239), (58, Int.ofNat 96), (59, Int.negSucc 239), (60, Int.ofNat 144), (61,
    Int.ofNat 144), (87, Int.ofNat 96), (88, Int.negSucc 239), (89, Int.ofNat 144), (90, Int.ofNat
    144), (132, Int.negSucc 23), (162, Int.negSucc 23), (192, Int.negSucc 95), (252, Int.negSucc
    23), (282, Int.negSucc 23), (468, Int.negSucc 23), (498, Int.negSucc 23), (528, Int.negSucc
    95), (588, Int.negSucc 23), (618, Int.negSucc 23), (1, Int.ofNat 8), (2, Int.negSucc 15), (29,
    Int.ofNat 8), (30, Int.negSucc 47), (31, Int.ofNat 72), (32, Int.ofNat 8), (58, Int.negSucc
    15), (59, Int.ofNat 72), (60, Int.negSucc 95), (61, Int.negSucc 15), (88, Int.ofNat 8), (89,
    Int.negSucc 15), (162, Int.ofNat 24), (192, Int.ofNat 8), (282, Int.ofNat 8), (498, Int.ofNat
    24), (528, Int.ofNat 8), (618, Int.ofNat 8), (1, Int.ofNat 16), (3, Int.negSucc 31), (29,
    Int.ofNat 16), (30, Int.negSucc 15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat
    16), (192, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528,
    Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc
    15), (252, Int.negSucc 15), (282, Int.negSucc 15), (312, Int.negSucc 15), (342, Int.ofNat 16),
    (372, Int.ofNat 16), (402, Int.ofNat 16), (432, Int.negSucc 15), (528, Int.negSucc 15), (588,
    Int.negSucc 15), (618, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (708,
    Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (0, Int.negSucc 47), (1, Int.ofNat
    80), (2, Int.negSucc 31), (3, Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 31), (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31),
    (90, Int.negSucc 47), (132, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8),
    (588, Int.ofNat 8), (648, Int.ofNat 8), (1, Int.ofNat 32), (2, Int.negSucc 63), (29, Int.ofNat
    32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58, Int.negSucc 63), (59,
    Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88, Int.ofNat 32), (89,
    Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat
    32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498, Int.ofNat 16),
    (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (738, Int.negSucc 7), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat
    16), (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 64), (588, Int.ofNat 64), (618, Int.ofNat
    64), (648, Int.ofNat 64), (678, Int.negSucc 63), (708, Int.negSucc 63), (738, Int.negSucc 63),
    (768, Int.ofNat 64), (30, Int.ofNat 24), (57, Int.negSucc 23), (88, Int.negSucc 47), (115,
    Int.ofNat 48), (528, Int.negSucc 23), (588, Int.negSucc 23), (738, Int.ofNat 24), (768,
    Int.negSucc 23), (813, Int.negSucc 23), (815, Int.ofNat 48), (30, Int.ofNat 24), (57,
    Int.negSucc 23), (59, Int.negSucc 47), (86, Int.ofNat 48), (528, Int.negSucc 23), (618,
    Int.negSucc 23), (708, Int.ofNat 24), (768, Int.negSucc 23), (813, Int.negSucc 23), (814,
    Int.ofNat 48), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7),
    (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 16), (30, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (87, Int.negSucc 31), (88, Int.ofNat
    32), (89, Int.negSucc 31), (90, Int.negSucc 31), (115, Int.ofNat 32), (468, Int.ofNat 16),
    (738, Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16), (59, Int.negSucc 15), (60, Int.ofNat
    16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (708, Int.negSucc 7),
    (768, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat 48), (1,
    Int.negSucc 47), (2, Int.ofNat 48), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.negSucc
    23), (30, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat 24), (558,
    Int.negSucc 23), (678, Int.negSucc 23), (768, Int.ofNat 24), (812, Int.negSucc 47), (813,
    Int.ofNat 24), (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat
    16), (87, Int.negSucc 31), (89, Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31),
    (468, Int.negSucc 15), (618, Int.negSucc 15), (678, Int.ofNat 16), (813, Int.ofNat 16), (815,
    Int.negSucc 31), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc
    15), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58,
    Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87,
    Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 15), (498, Int.negSucc 15), (588, Int.negSucc 15), (618, Int.negSucc 15), (812,
    Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (29,
    Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (58,
    Int.negSucc 31), (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc 31), (498,
    Int.negSucc 15), (588, Int.negSucc 15), (678, Int.ofNat 16), (813, Int.ofNat 16), (814,
    Int.negSucc 31), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat
    8), (87, Int.ofNat 16), (89, Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.negSucc 47), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.ofNat 24), (60, Int.negSucc 23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat
    24), (89, Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23),
    (558, Int.negSucc 23), (588, Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23),
    (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 24), (2,
    Int.ofNat 24), (3, Int.negSucc 23), (28, Int.negSucc 23), (29, Int.negSucc 71), (31,
    Int.negSucc 71), (32, Int.ofNat 72), (57, Int.ofNat 72), (58, Int.ofNat 24), (60, Int.ofNat
    24), (61, Int.negSucc 23), (86, Int.negSucc 23), (87, Int.ofNat 72), (89, Int.ofNat 72), (90,
    Int.negSucc 71), (115, Int.negSucc 71), (132, Int.ofNat 24), (498, Int.negSucc 23), (558,
    Int.negSucc 23), (618, Int.negSucc 23), (648, Int.negSucc 23), (738, Int.negSucc 23), (768,
    Int.ofNat 24), (812, Int.negSucc 23), (813, Int.ofNat 72), (814, Int.negSucc 23), (815,
    Int.negSucc 71), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat
    8), (58, Int.ofNat 16), (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.negSucc 15), (498,
    Int.negSucc 7), (648, Int.negSucc 7), (738, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.ofNat
    16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.negSucc 7), (558,
    Int.ofNat 8), (588, Int.ofNat 8), (708, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc
    7), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29,
    Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8),
    (618, Int.ofNat 8), (738, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798,
    Int.negSucc 15), (813, Int.ofNat 16), (840, Int.negSucc 15), (768, Int.ofNat 8), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (814, Int.negSucc 7), (815, Int.negSucc 7), (840,
    Int.ofNat 16), (588, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc
    15), (814, Int.ofNat 8), (815, Int.negSucc 7), (840, Int.ofNat 16), (618, Int.ofNat 8), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.negSucc 7), (815, Int.ofNat
    8), (840, Int.ofNat 16), (648, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813,
    Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (840, Int.ofNat 16), (468, Int.ofNat
    16), (798, Int.negSucc 15), (815, Int.ofNat 32), (840, Int.negSucc 31), (498, Int.ofNat 16),
    (798, Int.negSucc 15), (814, Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 8), (798,
    Int.negSucc 7), (812, Int.ofNat 16), (840, Int.negSucc 15), (29, Int.negSucc 7), (31,
    Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.ofNat 16),
    (90, Int.negSucc 15), (115, Int.negSucc 15), (738, Int.negSucc 7), (768, Int.ofNat 8), (798,
    Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat 16), (29, Int.negSucc 7), (31, Int.ofNat
    8), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.ofNat 16), (86, Int.negSucc 15), (708, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat
    8), (813, Int.negSucc 7), (840, Int.ofNat 16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 2, source := [(15, Int.negSucc 3), (44, Int.ofNat 12), (73, Int.negSucc
    7), (102, Int.negSucc 7), (188, Int.ofNat 8), (245, Int.ofNat 2), (273, Int.ofNat 2), (357,
    Int.ofNat 2), (385, Int.ofNat 2), (412, Int.ofNat 8), (435, Int.negSucc 3), (436, Int.ofNat
    12), (437, Int.negSucc 7), (438, Int.negSucc 7)],
    denominator := Int.ofNat 2,
    target := [(30, Int.ofNat 64), (32, Int.negSucc 127), (88, Int.negSucc 127), (90, Int.ofNat
    256), (132, Int.negSucc 63), (468, Int.negSucc 63), (1, Int.ofNat 24), (3, Int.negSucc 47),
    (29, Int.ofNat 24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59,
    Int.ofNat 24), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89,
    Int.negSucc 47), (90, Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252,
    Int.ofNat 24), (468, Int.ofNat 72), (528, Int.ofNat 24), (588, Int.ofNat 24), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (59, Int.ofNat 8), (61, Int.negSucc 15), (88,
    Int.ofNat 8), (89, Int.negSucc 15), (192, Int.ofNat 4), (252, Int.ofNat 4), (282, Int.ofNat
    4), (342, Int.negSucc 3), (528, Int.ofNat 4), (588, Int.ofNat 4), (618, Int.ofNat 4), (678,
    Int.negSucc 3), (0, Int.ofNat 8), (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16),
    (29, Int.negSucc 19), (30, Int.ofNat 48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58,
    Int.ofNat 8), (59, Int.negSucc 19), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16),
    (88, Int.negSucc 35), (89, Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192,
    Int.negSucc 11), (252, Int.negSucc 3), (468, Int.negSucc 3), (528, Int.negSucc 11), (588,
    Int.negSucc 3), (0, Int.ofNat 24), (1, Int.negSucc 71), (2, Int.ofNat 48), (3, Int.ofNat 48),
    (29, Int.negSucc 71), (30, Int.ofNat 192), (31, Int.negSucc 119), (32, Int.negSucc 119), (58,
    Int.ofNat 48), (59, Int.negSucc 119), (60, Int.ofNat 72), (61, Int.ofNat 72), (87, Int.ofNat
    48), (88, Int.negSucc 119), (89, Int.ofNat 72), (90, Int.ofNat 72), (132, Int.negSucc 11),
    (162, Int.negSucc 11), (192, Int.negSucc 47), (252, Int.negSucc 11), (282, Int.negSucc 11),
    (468, Int.negSucc 11), (498, Int.negSucc 11), (528, Int.negSucc 47), (588, Int.negSucc 11),
    (618, Int.negSucc 11), (1, Int.ofNat 4), (2, Int.negSucc 7), (29, Int.ofNat 4), (30,
    Int.negSucc 23), (31, Int.ofNat 36), (32, Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat
    36), (60, Int.negSucc 47), (61, Int.negSucc 7), (88, Int.ofNat 4), (89, Int.negSucc 7), (162,
    Int.ofNat 12), (192, Int.ofNat 4), (282, Int.ofNat 4), (498, Int.ofNat 12), (528, Int.ofNat
    4), (618, Int.ofNat 4), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30,
    Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat
    4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588,
    Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 7), (252,
    Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372,
    Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat
    80), (2, Int.negSucc 31), (3, Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 31), (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31),
    (90, Int.negSucc 47), (132, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8),
    (588, Int.ofNat 8), (648, Int.ofNat 8), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat
    16), (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58, Int.negSucc 31), (59,
    Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88, Int.ofNat 16), (89,
    Int.negSucc 31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat 4), (282, Int.ofNat
    16), (312, Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498, Int.ofNat 8), (528,
    Int.ofNat 16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat 4), (678, Int.negSucc
    3), (738, Int.negSucc 3), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3,
    Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 56), (588, Int.ofNat 56), (618, Int.ofNat
    56), (648, Int.ofNat 56), (678, Int.negSucc 55), (708, Int.negSucc 55), (738, Int.negSucc 55),
    (768, Int.ofNat 56), (30, Int.ofNat 16), (57, Int.negSucc 15), (88, Int.negSucc 31), (115,
    Int.ofNat 32), (528, Int.negSucc 15), (588, Int.negSucc 15), (738, Int.ofNat 16), (768,
    Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (30, Int.ofNat 16), (57,
    Int.negSucc 15), (59, Int.negSucc 31), (86, Int.ofNat 32), (528, Int.negSucc 15), (618,
    Int.negSucc 15), (708, Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15), (814,
    Int.ofNat 32), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7),
    (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 16), (30, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (87, Int.negSucc 31), (88, Int.ofNat
    32), (89, Int.negSucc 31), (90, Int.negSucc 31), (115, Int.ofNat 32), (468, Int.ofNat 16),
    (738, Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16), (59, Int.negSucc 15), (60, Int.ofNat
    16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (708, Int.negSucc 7),
    (768, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat 32), (1,
    Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc
    15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (558,
    Int.negSucc 15), (678, Int.negSucc 15), (768, Int.ofNat 16), (812, Int.negSucc 31), (813,
    Int.ofNat 16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8),
    (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 7), (618, Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc
    15), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58,
    Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87,
    Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 15), (498, Int.negSucc 15), (588, Int.negSucc 15), (618, Int.negSucc 15), (812,
    Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (29,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc
    15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588,
    Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (29,
    Int.negSucc 3), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.ofNat 4), (87, Int.ofNat 8),
    (89, Int.negSucc 7), (90, Int.ofNat 8), (115, Int.negSucc 7), (468, Int.negSucc 3), (648,
    Int.negSucc 3), (708, Int.ofNat 4), (813, Int.ofNat 4), (815, Int.negSucc 7), (0, Int.ofNat
    24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc 47), (31,
    Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60, Int.negSucc
    23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89, Int.negSucc 23), (90,
    Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558, Int.negSucc 23), (588,
    Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813, Int.ofNat 48), (814,
    Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 24), (2, Int.ofNat 24), (3, Int.negSucc
    23), (28, Int.negSucc 23), (29, Int.negSucc 71), (31, Int.negSucc 71), (32, Int.ofNat 72),
    (57, Int.ofNat 72), (58, Int.ofNat 24), (60, Int.ofNat 24), (61, Int.negSucc 23), (86,
    Int.negSucc 23), (87, Int.ofNat 72), (89, Int.ofNat 72), (90, Int.negSucc 71), (115,
    Int.negSucc 71), (132, Int.ofNat 24), (498, Int.negSucc 23), (558, Int.negSucc 23), (618,
    Int.negSucc 23), (648, Int.negSucc 23), (738, Int.negSucc 23), (768, Int.ofNat 24), (812,
    Int.negSucc 23), (813, Int.ofNat 72), (814, Int.negSucc 23), (815, Int.negSucc 71), (29,
    Int.negSucc 3), (31, Int.negSucc 3), (32, Int.ofNat 4), (57, Int.ofNat 4), (58, Int.ofNat 8),
    (60, Int.ofNat 8), (61, Int.negSucc 7), (86, Int.negSucc 7), (498, Int.negSucc 3), (648,
    Int.negSucc 3), (738, Int.ofNat 4), (813, Int.ofNat 4), (814, Int.negSucc 7), (0, Int.negSucc
    7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.ofNat 4), (31,
    Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558, Int.ofNat 4), (588, Int.ofNat
    4), (708, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (0, Int.negSucc 7), (2,
    Int.negSucc 7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.ofNat 4),
    (32, Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4), (618, Int.ofNat 4), (738,
    Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798, Int.negSucc 15), (813,
    Int.ofNat 16), (840, Int.negSucc 15), (768, Int.ofNat 8), (798, Int.ofNat 8), (812,
    Int.negSucc 7), (814, Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 16), (588,
    Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat
    8), (815, Int.negSucc 7), (840, Int.ofNat 16), (618, Int.ofNat 8), (798, Int.ofNat 8), (812,
    Int.ofNat 8), (813, Int.negSucc 15), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat
    16), (648, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813, Int.negSucc 15),
    (814, Int.ofNat 8), (815, Int.ofNat 8), (840, Int.ofNat 16), (468, Int.ofNat 12), (798,
    Int.negSucc 11), (815, Int.ofNat 24), (840, Int.negSucc 23), (498, Int.ofNat 12), (798,
    Int.negSucc 11), (814, Int.ofNat 24), (840, Int.negSucc 23), (558, Int.ofNat 8), (798,
    Int.negSucc 7), (812, Int.ofNat 16), (840, Int.negSucc 15), (29, Int.negSucc 3), (31,
    Int.negSucc 3), (32, Int.ofNat 4), (57, Int.ofNat 4), (87, Int.ofNat 8), (89, Int.ofNat 8),
    (90, Int.negSucc 7), (115, Int.negSucc 7), (738, Int.negSucc 3), (768, Int.ofNat 4), (798,
    Int.ofNat 4), (813, Int.negSucc 3), (840, Int.ofNat 8), (29, Int.negSucc 3), (31, Int.ofNat
    4), (32, Int.negSucc 3), (57, Int.ofNat 4), (58, Int.ofNat 8), (60, Int.negSucc 7), (61,
    Int.ofNat 8), (86, Int.negSucc 7), (708, Int.negSucc 3), (768, Int.ofNat 4), (798, Int.ofNat
    4), (813, Int.negSucc 3), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 2, source := [(14, Int.negSucc 2), (43, Int.ofNat 4), (72, Int.negSucc
    0), (101, Int.negSucc 2), (129, Int.ofNat 1), (214, Int.negSucc 0), (326, Int.negSucc 0),
    (381, Int.ofNat 1), (406, Int.negSucc 2), (407, Int.ofNat 4), (408, Int.negSucc 0), (409,
    Int.negSucc 2), (453, Int.negSucc 0), (537, Int.negSucc 0)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 48), (32, Int.negSucc 95), (88, Int.negSucc 95), (90, Int.ofNat
    192), (132, Int.negSucc 47), (468, Int.negSucc 47), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (0, Int.negSucc
    23), (1, Int.ofNat 60), (2, Int.negSucc 23), (3, Int.negSucc 47), (29, Int.ofNat 60), (30,
    Int.negSucc 143), (31, Int.ofNat 60), (32, Int.ofNat 108), (58, Int.negSucc 23), (59,
    Int.ofNat 60), (60, Int.negSucc 23), (61, Int.negSucc 47), (87, Int.negSucc 47), (88,
    Int.ofNat 108), (89, Int.negSucc 47), (90, Int.negSucc 71), (132, Int.ofNat 12), (192,
    Int.ofNat 36), (252, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat 36), (588, Int.ofNat
    12), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 32), (3, Int.ofNat 32), (29,
    Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 79), (32, Int.negSucc 79), (58,
    Int.ofNat 32), (59, Int.negSucc 79), (60, Int.ofNat 48), (61, Int.ofNat 48), (87, Int.ofNat
    32), (88, Int.negSucc 79), (89, Int.ofNat 48), (90, Int.ofNat 48), (132, Int.negSucc 7), (162,
    Int.negSucc 7), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 7), (468,
    Int.negSucc 7), (498, Int.negSucc 7), (528, Int.negSucc 31), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (1, Int.ofNat 32), (3, Int.negSucc 63), (29, Int.ofNat 32), (30, Int.negSucc
    31), (32, Int.ofNat 32), (87, Int.negSucc 63), (88, Int.ofNat 32), (192, Int.ofNat 16), (252,
    Int.ofNat 16), (312, Int.ofNat 16), (372, Int.negSucc 15), (528, Int.ofNat 16), (588,
    Int.ofNat 16), (648, Int.ofNat 16), (708, Int.negSucc 15), (192, Int.negSucc 15), (252,
    Int.negSucc 15), (282, Int.negSucc 15), (312, Int.negSucc 15), (342, Int.ofNat 16), (372,
    Int.ofNat 16), (402, Int.ofNat 16), (432, Int.negSucc 15), (528, Int.negSucc 15), (588,
    Int.negSucc 15), (618, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (708,
    Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (0, Int.ofNat 16), (1, Int.negSucc 47), (2,
    Int.ofNat 16), (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc
    47), (32, Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61,
    Int.ofNat 48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat
    80), (132, Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (0, Int.negSucc 95), (1, Int.ofNat 72), (2, Int.negSucc
    15), (3, Int.negSucc 15), (29, Int.ofNat 72), (30, Int.negSucc 47), (31, Int.ofNat 8), (32,
    Int.ofNat 8), (58, Int.negSucc 15), (59, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat
    8), (192, Int.ofNat 8), (222, Int.ofNat 24), (312, Int.ofNat 8), (528, Int.ofNat 8), (558,
    Int.ofNat 24), (648, Int.ofNat 8), (528, Int.ofNat 64), (588, Int.ofNat 64), (618, Int.ofNat
    64), (648, Int.ofNat 64), (678, Int.negSucc 63), (708, Int.negSucc 63), (738, Int.negSucc 63),
    (768, Int.ofNat 64), (30, Int.ofNat 24), (57, Int.negSucc 23), (88, Int.negSucc 47), (115,
    Int.ofNat 48), (528, Int.negSucc 23), (588, Int.negSucc 23), (738, Int.ofNat 24), (768,
    Int.negSucc 23), (813, Int.negSucc 23), (815, Int.ofNat 48), (30, Int.ofNat 8), (57,
    Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618,
    Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (1, Int.negSucc 47), (28, Int.ofNat 48), (30, Int.ofNat 24), (57, Int.negSucc
    23), (528, Int.negSucc 23), (648, Int.negSucc 23), (678, Int.ofNat 24), (768, Int.negSucc 23),
    (812, Int.ofNat 48), (813, Int.negSucc 23), (29, Int.ofNat 16), (30, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (87, Int.negSucc 31), (88, Int.ofNat
    32), (89, Int.negSucc 31), (90, Int.negSucc 31), (115, Int.ofNat 32), (468, Int.ofNat 16),
    (738, Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 23), (30, Int.ofNat 24), (31, Int.negSucc 23), (32,
    Int.negSucc 23), (57, Int.ofNat 24), (58, Int.ofNat 48), (59, Int.negSucc 47), (60, Int.ofNat
    48), (61, Int.ofNat 48), (86, Int.negSucc 47), (498, Int.negSucc 23), (708, Int.negSucc 23),
    (768, Int.ofNat 24), (813, Int.ofNat 24), (814, Int.negSucc 47), (0, Int.ofNat 16), (1,
    Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc
    7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8),
    (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 7), (618, Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87,
    Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468,
    Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812,
    Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.ofNat 16),
    (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (588,
    Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (29,
    Int.negSucc 15), (31, Int.ofNat 16), (32, Int.negSucc 15), (57, Int.ofNat 16), (87, Int.ofNat
    32), (89, Int.negSucc 31), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 15),
    (648, Int.negSucc 15), (708, Int.ofNat 16), (813, Int.ofNat 16), (815, Int.negSucc 31), (0,
    Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc
    31), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (60,
    Int.negSucc 15), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (89,
    Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15), (558,
    Int.negSucc 15), (588, Int.negSucc 15), (648, Int.negSucc 15), (812, Int.negSucc 15), (813,
    Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (0, Int.ofNat 24), (2, Int.ofNat
    24), (3, Int.negSucc 23), (28, Int.negSucc 23), (29, Int.negSucc 71), (31, Int.negSucc 71),
    (32, Int.ofNat 72), (57, Int.ofNat 72), (58, Int.ofNat 24), (60, Int.ofNat 24), (61,
    Int.negSucc 23), (86, Int.negSucc 23), (87, Int.ofNat 72), (89, Int.ofNat 72), (90,
    Int.negSucc 71), (115, Int.negSucc 71), (132, Int.ofNat 24), (498, Int.negSucc 23), (558,
    Int.negSucc 23), (618, Int.negSucc 23), (648, Int.negSucc 23), (738, Int.negSucc 23), (768,
    Int.ofNat 24), (812, Int.negSucc 23), (813, Int.ofNat 72), (814, Int.negSucc 23), (815,
    Int.negSucc 71), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc
    7), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (498,
    Int.ofNat 8), (648, Int.ofNat 8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat
    16), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.negSucc 31), (29,
    Int.negSucc 15), (31, Int.ofNat 16), (32, Int.negSucc 15), (57, Int.ofNat 16), (558,
    Int.negSucc 15), (588, Int.negSucc 15), (708, Int.ofNat 16), (812, Int.negSucc 31), (813,
    Int.ofNat 16), (0, Int.ofNat 16), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.negSucc
    15), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (618, Int.negSucc 7), (738, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (798, Int.negSucc 15), (813, Int.ofNat 16), (840, Int.negSucc 15), (768,
    Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (814, Int.negSucc 7), (815,
    Int.negSucc 7), (840, Int.ofNat 16), (588, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat
    8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.negSucc 7), (840, Int.ofNat 16),
    (618, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814,
    Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (648, Int.ofNat 8), (798, Int.ofNat
    8), (812, Int.negSucc 7), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (840,
    Int.ofNat 16), (468, Int.ofNat 16), (798, Int.negSucc 15), (815, Int.ofNat 32), (840,
    Int.negSucc 31), (498, Int.ofNat 8), (798, Int.negSucc 7), (814, Int.ofNat 16), (840,
    Int.negSucc 15), (558, Int.ofNat 16), (798, Int.negSucc 15), (812, Int.ofNat 32), (840,
    Int.negSucc 31), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat
    8), (87, Int.ofNat 16), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.negSucc 15), (738,
    Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat
    16), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (678, Int.negSucc
    7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat 16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 3, source := [(15, Int.negSucc 3), (44, Int.ofNat 6), (73, Int.negSucc
    1), (102, Int.negSucc 3), (188, Int.ofNat 4), (245, Int.ofNat 1), (301, Int.ofNat 1), (329,
    Int.ofNat 1), (385, Int.ofNat 1), (412, Int.ofNat 4), (435, Int.negSucc 3), (436, Int.ofNat
    6), (437, Int.negSucc 1), (438, Int.negSucc 3)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 24), (3, Int.negSucc 47),
    (29, Int.ofNat 24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59,
    Int.ofNat 24), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89,
    Int.negSucc 47), (90, Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252,
    Int.ofNat 24), (468, Int.ofNat 72), (528, Int.ofNat 24), (588, Int.ofNat 24), (0, Int.ofNat
    8), (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16), (29, Int.negSucc 19), (30,
    Int.ofNat 48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58, Int.ofNat 8), (59, Int.negSucc
    19), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16), (88, Int.negSucc 35), (89,
    Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192, Int.negSucc 11), (252,
    Int.negSucc 3), (468, Int.negSucc 3), (528, Int.negSucc 11), (588, Int.negSucc 3), (1,
    Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc 15), (32, Int.ofNat
    16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252, Int.ofNat 8), (312,
    Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat
    8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7), (282, Int.negSucc 7),
    (312, Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402, Int.ofNat 8), (432,
    Int.negSucc 7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618, Int.negSucc 7), (648,
    Int.negSucc 7), (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc
    7), (0, Int.ofNat 24), (1, Int.negSucc 39), (2, Int.ofNat 16), (3, Int.ofNat 24), (29,
    Int.negSucc 39), (30, Int.ofNat 64), (31, Int.negSucc 23), (32, Int.negSucc 39), (58,
    Int.ofNat 16), (59, Int.negSucc 23), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat
    24), (88, Int.negSucc 39), (89, Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192,
    Int.negSucc 15), (222, Int.negSucc 3), (252, Int.negSucc 3), (312, Int.negSucc 3), (468,
    Int.negSucc 3), (528, Int.negSucc 15), (558, Int.negSucc 3), (588, Int.negSucc 3), (648,
    Int.negSucc 3), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58, Int.negSucc 31), (59, Int.ofNat 56), (60,
    Int.negSucc 31), (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc 31), (162,
    Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat 4), (282, Int.ofNat 16), (312, Int.ofNat
    4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498, Int.ofNat 8), (528, Int.ofNat 16), (588,
    Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat 4), (678, Int.negSucc 3), (738, Int.negSucc
    3), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48), (29,
    Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
    Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23),
    (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
    Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
    Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc 7), (3, Int.negSucc 7),
    (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32, Int.ofNat 4), (58,
    Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4), (192, Int.ofNat 4),
    (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558, Int.ofNat 12), (648,
    Int.ofNat 4), (528, Int.ofNat 72), (588, Int.ofNat 72), (618, Int.ofNat 72), (648, Int.ofNat
    72), (678, Int.negSucc 71), (708, Int.negSucc 71), (738, Int.negSucc 71), (768, Int.ofNat 72),
    (30, Int.ofNat 20), (57, Int.negSucc 19), (88, Int.negSucc 39), (115, Int.ofNat 40), (528,
    Int.negSucc 19), (588, Int.negSucc 19), (738, Int.ofNat 20), (768, Int.negSucc 19), (813,
    Int.negSucc 19), (815, Int.ofNat 40), (1, Int.negSucc 7), (28, Int.ofNat 8), (30, Int.ofNat
    16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88, Int.negSucc 7), (115,
    Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.ofNat
    8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (30, Int.ofNat 8), (57,
    Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618,
    Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (1, Int.negSucc 39), (28, Int.ofNat 40), (30, Int.ofNat 20), (57, Int.negSucc
    19), (528, Int.negSucc 19), (648, Int.negSucc 19), (678, Int.ofNat 20), (768, Int.negSucc 19),
    (812, Int.ofNat 40), (813, Int.negSucc 19), (29, Int.ofNat 28), (30, Int.negSucc 27), (31,
    Int.ofNat 28), (32, Int.ofNat 28), (57, Int.negSucc 27), (87, Int.negSucc 55), (88, Int.ofNat
    56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115, Int.ofNat 56), (468, Int.ofNat 28),
    (738, Int.ofNat 28), (768, Int.negSucc 27), (813, Int.negSucc 27), (815, Int.ofNat 56), (0,
    Int.negSucc 55), (1, Int.ofNat 56), (2, Int.negSucc 55), (3, Int.negSucc 55), (28, Int.ofNat
    56), (29, Int.ofNat 112), (30, Int.negSucc 111), (31, Int.ofNat 112), (32, Int.ofNat 112),
    (57, Int.negSucc 111), (58, Int.negSucc 55), (59, Int.ofNat 56), (60, Int.negSucc 55), (61,
    Int.negSucc 55), (86, Int.ofNat 56), (87, Int.negSucc 55), (88, Int.ofNat 56), (89,
    Int.negSucc 55), (90, Int.negSucc 55), (115, Int.ofNat 56), (468, Int.ofNat 56), (498,
    Int.ofNat 56), (558, Int.ofNat 56), (678, Int.ofNat 56), (708, Int.ofNat 56), (738, Int.ofNat
    56), (768, Int.negSucc 55), (812, Int.ofNat 56), (813, Int.negSucc 111), (814, Int.ofNat 56),
    (815, Int.ofNat 56), (29, Int.negSucc 15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 32), (59, Int.negSucc 31), (60, Int.ofNat
    32), (61, Int.ofNat 32), (86, Int.negSucc 31), (498, Int.negSucc 15), (708, Int.negSucc 15),
    (768, Int.ofNat 16), (813, Int.ofNat 16), (814, Int.negSucc 31), (0, Int.ofNat 8), (1,
    Int.negSucc 7), (2, Int.ofNat 8), (3, Int.ofNat 8), (28, Int.negSucc 7), (29, Int.negSucc 3),
    (30, Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (57, Int.ofNat 4), (558,
    Int.negSucc 3), (678, Int.negSucc 3), (768, Int.ofNat 4), (812, Int.negSucc 7), (813,
    Int.ofNat 4), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8),
    (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 7), (618, Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc
    31), (29, Int.ofNat 64), (31, Int.negSucc 63), (32, Int.negSucc 63), (57, Int.ofNat 64), (58,
    Int.negSucc 31), (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc 31), (87,
    Int.negSucc 31), (89, Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468,
    Int.negSucc 31), (498, Int.negSucc 31), (588, Int.negSucc 31), (618, Int.negSucc 31), (812,
    Int.negSucc 31), (813, Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (29,
    Int.negSucc 3), (31, Int.ofNat 4), (32, Int.ofNat 4), (57, Int.negSucc 3), (58, Int.ofNat 8),
    (60, Int.negSucc 7), (61, Int.negSucc 7), (86, Int.ofNat 8), (498, Int.ofNat 4), (588,
    Int.ofNat 4), (678, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat 8), (29, Int.negSucc
    11), (31, Int.ofNat 12), (32, Int.negSucc 11), (57, Int.ofNat 12), (87, Int.ofNat 24), (89,
    Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 11), (648,
    Int.negSucc 11), (708, Int.ofNat 12), (813, Int.ofNat 12), (815, Int.negSucc 23), (0,
    Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc
    47), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60,
    Int.negSucc 23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89,
    Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558,
    Int.negSucc 23), (588, Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813,
    Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 32), (2, Int.ofNat
    32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95),
    (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61,
    Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90,
    Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558,
    Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc
    3), (58, Int.negSucc 7), (60, Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat 8), (498,
    Int.ofNat 4), (648, Int.ofNat 4), (738, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat
    8), (0, Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29,
    Int.negSucc 11), (31, Int.ofNat 12), (32, Int.negSucc 11), (57, Int.ofNat 12), (558,
    Int.negSucc 11), (588, Int.negSucc 11), (708, Int.ofNat 12), (812, Int.negSucc 23), (813,
    Int.ofNat 12), (0, Int.ofNat 16), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.negSucc
    15), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (618, Int.negSucc 7), (738, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (798, Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815,
    Int.negSucc 15), (840, Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840,
    Int.ofNat 32), (618, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 24), (798,
    Int.negSucc 23), (815, Int.ofNat 48), (840, Int.negSucc 47), (498, Int.ofNat 16), (798,
    Int.negSucc 15), (814, Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 24), (798,
    Int.negSucc 23), (812, Int.ofNat 48), (840, Int.negSucc 47), (29, Int.negSucc 7), (31,
    Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.ofNat 16),
    (90, Int.negSucc 15), (115, Int.negSucc 15), (738, Int.negSucc 7), (768, Int.ofNat 8), (798,
    Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat 16), (0, Int.negSucc 15), (2, Int.ofNat
    16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (678, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat
    8), (813, Int.negSucc 7), (840, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15),
    (813, Int.ofNat 16), (814, Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 16), (798,
    Int.negSucc 3), (812, Int.ofNat 4), (814, Int.ofNat 4), (815, Int.negSucc 3), (840,
    Int.negSucc 3), (798, Int.negSucc 3), (812, Int.negSucc 3), (814, Int.ofNat 4), (815,
    Int.ofNat 4), (840, Int.negSucc 3)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 1, mode := 3, source := [(0, Int.ofNat 2), (1, Int.negSucc 5), (2, Int.ofNat 2), (3,
    Int.ofNat 6), (29, Int.negSucc 5), (30, Int.ofNat 16), (31, Int.negSucc 5), (32, Int.negSucc
    13), (58, Int.ofNat 2), (59, Int.negSucc 5), (60, Int.ofNat 2), (61, Int.ofNat 6), (87,
    Int.ofNat 6), (88, Int.negSucc 13), (89, Int.ofNat 6), (90, Int.ofNat 10), (132, Int.negSucc
    2), (162, Int.negSucc 0), (192, Int.negSucc 3), (222, Int.negSucc 0), (252, Int.negSucc 2),
    (282, Int.negSucc 0), (312, Int.negSucc 0), (432, Int.negSucc 0), (462, Int.ofNat 1), (468,
    Int.negSucc 2), (498, Int.negSucc 0), (528, Int.negSucc 3), (558, Int.negSucc 0), (588,
    Int.negSucc 2), (618, Int.negSucc 0), (648, Int.negSucc 0), (768, Int.negSucc 0), (798,
    Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 96), (32, Int.negSucc 191), (88, Int.negSucc 191), (90, Int.ofNat
    384), (132, Int.negSucc 95), (468, Int.negSucc 95), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (0, Int.ofNat
    88), (1, Int.negSucc 219), (2, Int.ofNat 88), (3, Int.ofNat 176), (29, Int.negSucc 219), (30,
    Int.ofNat 528), (31, Int.negSucc 219), (32, Int.negSucc 395), (58, Int.ofNat 88), (59,
    Int.negSucc 219), (60, Int.ofNat 88), (61, Int.ofNat 176), (87, Int.ofNat 176), (88,
    Int.negSucc 395), (89, Int.ofNat 176), (90, Int.ofNat 264), (132, Int.negSucc 43), (192,
    Int.negSucc 131), (252, Int.negSucc 43), (468, Int.negSucc 43), (528, Int.negSucc 131), (588,
    Int.negSucc 43), (0, Int.negSucc 47), (1, Int.ofNat 144), (2, Int.negSucc 95), (3, Int.negSucc
    95), (29, Int.ofNat 144), (30, Int.negSucc 383), (31, Int.ofNat 240), (32, Int.ofNat 240),
    (58, Int.negSucc 95), (59, Int.ofNat 240), (60, Int.negSucc 143), (61, Int.negSucc 143), (87,
    Int.negSucc 95), (88, Int.ofNat 240), (89, Int.negSucc 143), (90, Int.negSucc 143), (132,
    Int.ofNat 24), (162, Int.ofNat 24), (192, Int.ofNat 96), (252, Int.ofNat 24), (282, Int.ofNat
    24), (468, Int.ofNat 24), (498, Int.ofNat 24), (528, Int.ofNat 96), (588, Int.ofNat 24), (618,
    Int.ofNat 24), (1, Int.negSucc 15), (3, Int.ofNat 32), (29, Int.negSucc 15), (30, Int.ofNat
    16), (32, Int.negSucc 15), (87, Int.ofNat 32), (88, Int.negSucc 15), (192, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (372, Int.ofNat 8), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (192, Int.ofNat 8), (252, Int.ofNat
    8), (282, Int.ofNat 8), (312, Int.ofNat 8), (342, Int.negSucc 7), (372, Int.negSucc 7), (402,
    Int.negSucc 7), (432, Int.ofNat 8), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat
    8), (648, Int.ofNat 8), (678, Int.negSucc 7), (708, Int.negSucc 7), (738, Int.negSucc 7),
    (768, Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (1, Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat
    96), (31, Int.negSucc 111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162,
    Int.negSucc 15), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (738, Int.ofNat 8), (0, Int.ofNat 8), (1, Int.negSucc 23), (2, Int.ofNat 8), (3,
    Int.ofNat 24), (29, Int.negSucc 23), (30, Int.ofNat 64), (31, Int.negSucc 23), (32,
    Int.negSucc 55), (58, Int.ofNat 8), (59, Int.negSucc 23), (60, Int.ofNat 8), (61, Int.ofNat
    24), (87, Int.ofNat 24), (88, Int.negSucc 55), (89, Int.ofNat 24), (90, Int.ofNat 40), (132,
    Int.negSucc 11), (162, Int.negSucc 3), (192, Int.negSucc 15), (222, Int.negSucc 3), (252,
    Int.negSucc 11), (282, Int.negSucc 3), (312, Int.negSucc 3), (432, Int.negSucc 3), (462,
    Int.ofNat 4), (468, Int.negSucc 11), (498, Int.negSucc 3), (528, Int.negSucc 15), (558,
    Int.negSucc 3), (588, Int.negSucc 11), (618, Int.negSucc 3), (648, Int.negSucc 3), (768,
    Int.negSucc 3), (798, Int.ofNat 4), (528, Int.ofNat 168), (588, Int.ofNat 168), (618,
    Int.ofNat 168), (648, Int.ofNat 168), (678, Int.negSucc 167), (708, Int.negSucc 167), (738,
    Int.negSucc 167), (768, Int.ofNat 168), (30, Int.ofNat 48), (57, Int.negSucc 47), (88,
    Int.negSucc 95), (115, Int.ofNat 96), (528, Int.negSucc 47), (588, Int.negSucc 47), (738,
    Int.ofNat 48), (768, Int.negSucc 47), (813, Int.negSucc 47), (815, Int.ofNat 96), (1,
    Int.negSucc 39), (28, Int.ofNat 40), (30, Int.ofNat 80), (57, Int.negSucc 79), (59,
    Int.negSucc 39), (86, Int.ofNat 40), (88, Int.negSucc 39), (115, Int.ofNat 40), (528,
    Int.negSucc 39), (768, Int.negSucc 39), (798, Int.ofNat 40), (812, Int.ofNat 40), (813,
    Int.negSucc 79), (814, Int.ofNat 40), (815, Int.ofNat 40), (30, Int.ofNat 8), (57, Int.negSucc
    7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618, Int.negSucc 7),
    (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (1,
    Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc 7), (528, Int.negSucc
    7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (29, Int.ofNat 120), (30, Int.negSucc 119), (31, Int.ofNat 120), (32,
    Int.ofNat 120), (57, Int.negSucc 119), (87, Int.negSucc 239), (88, Int.ofNat 240), (89,
    Int.negSucc 239), (90, Int.negSucc 239), (115, Int.ofNat 240), (468, Int.ofNat 120), (738,
    Int.ofNat 120), (768, Int.negSucc 119), (813, Int.negSucc 119), (815, Int.ofNat 240), (0,
    Int.negSucc 87), (1, Int.ofNat 88), (2, Int.negSucc 87), (3, Int.negSucc 87), (28, Int.ofNat
    88), (29, Int.ofNat 176), (30, Int.negSucc 175), (31, Int.ofNat 176), (32, Int.ofNat 176),
    (57, Int.negSucc 175), (58, Int.negSucc 87), (59, Int.ofNat 88), (60, Int.negSucc 87), (61,
    Int.negSucc 87), (86, Int.ofNat 88), (87, Int.negSucc 87), (88, Int.ofNat 88), (89,
    Int.negSucc 87), (90, Int.negSucc 87), (115, Int.ofNat 88), (468, Int.ofNat 88), (498,
    Int.ofNat 88), (558, Int.ofNat 88), (678, Int.ofNat 88), (708, Int.ofNat 88), (738, Int.ofNat
    88), (768, Int.negSucc 87), (812, Int.ofNat 88), (813, Int.negSucc 175), (814, Int.ofNat 88),
    (815, Int.ofNat 88), (29, Int.ofNat 8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat
    8), (57, Int.negSucc 7), (58, Int.negSucc 15), (59, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (708, Int.ofNat 8), (768, Int.negSucc
    7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0, Int.negSucc 15), (1, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat 8), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (558, Int.ofNat 8), (678,
    Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat
    56), (31, Int.negSucc 55), (32, Int.negSucc 55), (57, Int.ofNat 56), (87, Int.negSucc 111),
    (89, Int.ofNat 112), (90, Int.ofNat 112), (115, Int.negSucc 111), (468, Int.negSucc 55), (618,
    Int.negSucc 55), (678, Int.ofNat 56), (813, Int.ofNat 56), (815, Int.negSucc 111), (0,
    Int.negSucc 63), (2, Int.ofNat 64), (3, Int.ofNat 64), (28, Int.negSucc 63), (29, Int.ofNat
    128), (31, Int.negSucc 127), (32, Int.negSucc 127), (57, Int.ofNat 128), (58, Int.negSucc 63),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (86, Int.negSucc 63), (87, Int.negSucc 63), (89,
    Int.ofNat 64), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 63), (498,
    Int.negSucc 63), (588, Int.negSucc 63), (618, Int.negSucc 63), (812, Int.negSucc 63), (813,
    Int.ofNat 128), (814, Int.negSucc 63), (815, Int.negSucc 63), (29, Int.ofNat 8), (31,
    Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc 15), (60, Int.ofNat
    16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588, Int.negSucc 7),
    (678, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (29, Int.negSucc 55), (31,
    Int.ofNat 56), (32, Int.negSucc 55), (57, Int.ofNat 56), (87, Int.ofNat 112), (89, Int.negSucc
    111), (90, Int.ofNat 112), (115, Int.negSucc 111), (468, Int.negSucc 55), (648, Int.negSucc
    55), (708, Int.ofNat 56), (813, Int.ofNat 56), (815, Int.negSucc 111), (0, Int.ofNat 64), (2,
    Int.negSucc 63), (3, Int.ofNat 64), (28, Int.negSucc 63), (29, Int.negSucc 127), (31,
    Int.ofNat 128), (32, Int.negSucc 127), (57, Int.ofNat 128), (58, Int.ofNat 64), (60,
    Int.negSucc 63), (61, Int.ofNat 64), (86, Int.negSucc 63), (87, Int.ofNat 64), (89,
    Int.negSucc 63), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 63), (558,
    Int.negSucc 63), (588, Int.negSucc 63), (648, Int.negSucc 63), (812, Int.negSucc 63), (813,
    Int.ofNat 128), (814, Int.negSucc 63), (815, Int.negSucc 63), (0, Int.ofNat 72), (2, Int.ofNat
    72), (3, Int.negSucc 71), (28, Int.negSucc 71), (29, Int.negSucc 215), (31, Int.negSucc 215),
    (32, Int.ofNat 216), (57, Int.ofNat 216), (58, Int.ofNat 72), (60, Int.ofNat 72), (61,
    Int.negSucc 71), (86, Int.negSucc 71), (87, Int.ofNat 216), (89, Int.ofNat 216), (90,
    Int.negSucc 215), (115, Int.negSucc 215), (132, Int.ofNat 72), (498, Int.negSucc 71), (558,
    Int.negSucc 71), (618, Int.negSucc 71), (648, Int.negSucc 71), (738, Int.negSucc 71), (768,
    Int.ofNat 72), (812, Int.negSucc 71), (813, Int.ofNat 216), (814, Int.negSucc 71), (815,
    Int.negSucc 215), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat
    8), (58, Int.ofNat 16), (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.negSucc 15), (498,
    Int.negSucc 7), (648, Int.negSucc 7), (738, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc
    15), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (708, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (0, Int.ofNat 16), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.negSucc 15),
    (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (618, Int.negSucc 7), (738, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (798, Int.negSucc 119), (813, Int.ofNat 120), (840, Int.negSucc 119), (768,
    Int.ofNat 48), (798, Int.ofNat 48), (812, Int.negSucc 47), (814, Int.negSucc 47), (815,
    Int.negSucc 47), (840, Int.ofNat 96), (588, Int.ofNat 48), (798, Int.ofNat 48), (812,
    Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48), (815, Int.negSucc 47), (840,
    Int.ofNat 96), (618, Int.ofNat 48), (798, Int.ofNat 48), (812, Int.ofNat 48), (813,
    Int.negSucc 95), (814, Int.negSucc 47), (815, Int.ofNat 48), (840, Int.ofNat 96), (648,
    Int.ofNat 48), (798, Int.ofNat 48), (812, Int.negSucc 47), (813, Int.negSucc 95), (814,
    Int.ofNat 48), (815, Int.ofNat 48), (840, Int.ofNat 96), (468, Int.ofNat 80), (798,
    Int.negSucc 79), (815, Int.ofNat 160), (840, Int.negSucc 159), (498, Int.ofNat 48), (798,
    Int.negSucc 47), (814, Int.ofNat 96), (840, Int.negSucc 95), (558, Int.ofNat 48), (798,
    Int.negSucc 47), (812, Int.ofNat 96), (840, Int.negSucc 95), (29, Int.negSucc 31), (31,
    Int.negSucc 31), (32, Int.ofNat 32), (57, Int.ofNat 32), (87, Int.ofNat 64), (89, Int.ofNat
    64), (90, Int.negSucc 63), (115, Int.negSucc 63), (738, Int.negSucc 31), (768, Int.ofNat 32),
    (798, Int.ofNat 32), (813, Int.negSucc 31), (840, Int.ofNat 64), (798, Int.ofNat 40), (812,
    Int.negSucc 39), (813, Int.ofNat 40), (814, Int.negSucc 39), (815, Int.negSucc 39), (840,
    Int.ofNat 40), (798, Int.negSucc 15), (812, Int.ofNat 16), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 15)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 6, mode := 3, source := [(6, Int.negSucc 0), (35, Int.ofNat 2), (64, Int.negSucc 0),
    (93, Int.negSucc 0), (174, Int.negSucc 0), (175, Int.ofNat 2), (176, Int.negSucc 0), (177,
    Int.negSucc 0), (248, Int.negSucc 0), (278, Int.negSucc 0), (309, Int.ofNat 1), (461,
    Int.negSucc 0), (472, Int.negSucc 0), (502, Int.negSucc 0), (561, Int.ofNat 1), (769,
    Int.negSucc 0)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 28), (3, Int.negSucc 55),
    (29, Int.ofNat 28), (30, Int.negSucc 167), (31, Int.ofNat 28), (32, Int.ofNat 252), (59,
    Int.ofNat 28), (61, Int.negSucc 55), (87, Int.negSucc 55), (88, Int.ofNat 252), (89,
    Int.negSucc 55), (90, Int.negSucc 335), (132, Int.ofNat 84), (192, Int.ofNat 28), (252,
    Int.ofNat 28), (468, Int.ofNat 84), (528, Int.ofNat 28), (588, Int.ofNat 28), (0, Int.ofNat
    72), (1, Int.negSucc 179), (2, Int.ofNat 72), (3, Int.ofNat 144), (29, Int.negSucc 179), (30,
    Int.ofNat 432), (31, Int.negSucc 179), (32, Int.negSucc 323), (58, Int.ofNat 72), (59,
    Int.negSucc 179), (60, Int.ofNat 72), (61, Int.ofNat 144), (87, Int.ofNat 144), (88,
    Int.negSucc 323), (89, Int.ofNat 144), (90, Int.ofNat 216), (132, Int.negSucc 35), (192,
    Int.negSucc 107), (252, Int.negSucc 35), (468, Int.negSucc 35), (528, Int.negSucc 107), (588,
    Int.negSucc 35), (0, Int.negSucc 47), (1, Int.ofNat 144), (2, Int.negSucc 95), (3, Int.negSucc
    95), (29, Int.ofNat 144), (30, Int.negSucc 383), (31, Int.ofNat 240), (32, Int.ofNat 240),
    (58, Int.negSucc 95), (59, Int.ofNat 240), (60, Int.negSucc 143), (61, Int.negSucc 143), (87,
    Int.negSucc 95), (88, Int.ofNat 240), (89, Int.negSucc 143), (90, Int.negSucc 143), (132,
    Int.ofNat 24), (162, Int.ofNat 24), (192, Int.ofNat 96), (252, Int.ofNat 24), (282, Int.ofNat
    24), (468, Int.ofNat 24), (498, Int.ofNat 24), (528, Int.ofNat 96), (588, Int.ofNat 24), (618,
    Int.ofNat 24), (1, Int.negSucc 15), (3, Int.ofNat 32), (29, Int.negSucc 15), (30, Int.ofNat
    16), (32, Int.negSucc 15), (87, Int.ofNat 32), (88, Int.negSucc 15), (192, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (372, Int.ofNat 8), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (192, Int.ofNat 8), (252, Int.ofNat
    8), (282, Int.ofNat 8), (312, Int.ofNat 8), (342, Int.negSucc 7), (372, Int.negSucc 7), (402,
    Int.negSucc 7), (432, Int.ofNat 8), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat
    8), (648, Int.ofNat 8), (678, Int.negSucc 7), (708, Int.negSucc 7), (738, Int.negSucc 7),
    (768, Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (1, Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat
    96), (31, Int.negSucc 111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162,
    Int.negSucc 15), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (738, Int.ofNat 8), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16),
    (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 48), (588, Int.ofNat 48), (618, Int.ofNat
    48), (648, Int.ofNat 48), (678, Int.negSucc 47), (708, Int.negSucc 47), (738, Int.negSucc 47),
    (768, Int.ofNat 48), (30, Int.ofNat 8), (57, Int.negSucc 7), (88, Int.negSucc 15), (115,
    Int.ofNat 16), (528, Int.negSucc 7), (588, Int.negSucc 7), (738, Int.ofNat 8), (768,
    Int.negSucc 7), (813, Int.negSucc 7), (815, Int.ofNat 16), (1, Int.negSucc 7), (28, Int.ofNat
    8), (30, Int.ofNat 16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88,
    Int.negSucc 7), (115, Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (30, Int.ofNat 8), (57, Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528,
    Int.negSucc 7), (618, Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813,
    Int.negSucc 7), (814, Int.ofNat 16), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat
    8), (57, Int.negSucc 7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 24), (30,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.ofNat 24), (57, Int.negSucc 23), (87,
    Int.negSucc 47), (88, Int.ofNat 48), (89, Int.negSucc 47), (90, Int.negSucc 47), (115,
    Int.ofNat 48), (468, Int.ofNat 24), (738, Int.ofNat 24), (768, Int.negSucc 23), (813,
    Int.negSucc 23), (815, Int.ofNat 48), (0, Int.negSucc 15), (1, Int.ofNat 16), (2, Int.negSucc
    15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat 32), (30, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.ofNat 32), (57, Int.negSucc 31), (58, Int.negSucc 15), (59, Int.ofNat
    16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (87, Int.negSucc 15),
    (88, Int.ofNat 16), (89, Int.negSucc 15), (90, Int.negSucc 15), (115, Int.ofNat 16), (468,
    Int.ofNat 16), (498, Int.ofNat 16), (558, Int.ofNat 16), (678, Int.ofNat 16), (708, Int.ofNat
    16), (738, Int.ofNat 16), (768, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.negSucc 31),
    (814, Int.ofNat 16), (815, Int.ofNat 16), (29, Int.ofNat 8), (30, Int.negSucc 7), (31,
    Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.negSucc 15), (59, Int.ofNat
    16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (708,
    Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0, Int.negSucc
    15), (1, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29,
    Int.ofNat 8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7),
    (558, Int.ofNat 8), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat
    8), (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 7), (618, Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc
    15), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58,
    Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87,
    Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468,
    Int.negSucc 15), (498, Int.negSucc 15), (588, Int.negSucc 15), (618, Int.negSucc 15), (812,
    Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (29,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc
    15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588,
    Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16),
    (89, Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (648,
    Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat
    16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (60, Int.negSucc
    15), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15), (558, Int.negSucc 15), (588,
    Int.negSucc 15), (648, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.negSucc 15), (0, Int.ofNat 16), (2, Int.ofNat 16), (3, Int.negSucc
    15), (28, Int.negSucc 15), (29, Int.negSucc 47), (31, Int.negSucc 47), (32, Int.ofNat 48),
    (57, Int.ofNat 48), (58, Int.ofNat 16), (60, Int.ofNat 16), (61, Int.negSucc 15), (86,
    Int.negSucc 15), (87, Int.ofNat 48), (89, Int.ofNat 48), (90, Int.negSucc 47), (115,
    Int.negSucc 47), (132, Int.ofNat 16), (498, Int.negSucc 15), (558, Int.negSucc 15), (618,
    Int.negSucc 15), (648, Int.negSucc 15), (738, Int.negSucc 15), (768, Int.ofNat 16), (812,
    Int.negSucc 15), (813, Int.ofNat 48), (814, Int.negSucc 15), (815, Int.negSucc 47), (29,
    Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (58, Int.ofNat 16),
    (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.negSucc 15), (498, Int.negSucc 7), (648,
    Int.negSucc 7), (738, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat
    16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31,
    Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc
    7), (708, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (0, Int.ofNat 16), (2,
    Int.ofNat 16), (3, Int.negSucc 15), (28, Int.negSucc 15), (29, Int.negSucc 7), (31,
    Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (558, Int.negSucc 7), (618, Int.negSucc
    7), (738, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (798, Int.negSucc 39),
    (813, Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 32), (588,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814, Int.negSucc 15), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (840,
    Int.ofNat 32), (468, Int.ofNat 16), (798, Int.negSucc 15), (815, Int.ofNat 32), (840,
    Int.negSucc 31), (498, Int.ofNat 16), (798, Int.negSucc 15), (814, Int.ofNat 32), (840,
    Int.negSucc 31), (558, Int.ofNat 16), (798, Int.negSucc 15), (812, Int.ofNat 32), (840,
    Int.negSucc 31), (798, Int.ofNat 8), (812, Int.negSucc 7), (813, Int.ofNat 8), (814,
    Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 1, mode := 2, source := [(0, Int.ofNat 2), (1, Int.negSucc 5), (2, Int.ofNat 2), (3,
    Int.ofNat 6), (29, Int.negSucc 5), (30, Int.ofNat 16), (31, Int.negSucc 5), (32, Int.negSucc
    13), (58, Int.ofNat 2), (59, Int.negSucc 5), (60, Int.ofNat 2), (61, Int.ofNat 6), (87,
    Int.ofNat 6), (88, Int.negSucc 13), (89, Int.ofNat 6), (90, Int.ofNat 10), (132, Int.negSucc
    2), (162, Int.negSucc 0), (192, Int.negSucc 3), (222, Int.negSucc 0), (252, Int.negSucc 2),
    (282, Int.negSucc 0), (312, Int.negSucc 0), (432, Int.negSucc 0), (462, Int.ofNat 1), (468,
    Int.negSucc 2), (498, Int.negSucc 0), (528, Int.negSucc 3), (558, Int.negSucc 0), (588,
    Int.negSucc 2), (618, Int.negSucc 0), (648, Int.negSucc 0), (768, Int.negSucc 0), (798,
    Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (0, Int.ofNat
    88), (1, Int.negSucc 219), (2, Int.ofNat 88), (3, Int.ofNat 176), (29, Int.negSucc 219), (30,
    Int.ofNat 528), (31, Int.negSucc 219), (32, Int.negSucc 395), (58, Int.ofNat 88), (59,
    Int.negSucc 219), (60, Int.ofNat 88), (61, Int.ofNat 176), (87, Int.ofNat 176), (88,
    Int.negSucc 395), (89, Int.ofNat 176), (90, Int.ofNat 264), (132, Int.negSucc 43), (192,
    Int.negSucc 131), (252, Int.negSucc 43), (468, Int.negSucc 43), (528, Int.negSucc 131), (588,
    Int.negSucc 43), (0, Int.negSucc 47), (1, Int.ofNat 144), (2, Int.negSucc 95), (3, Int.negSucc
    95), (29, Int.ofNat 144), (30, Int.negSucc 383), (31, Int.ofNat 240), (32, Int.ofNat 240),
    (58, Int.negSucc 95), (59, Int.ofNat 240), (60, Int.negSucc 143), (61, Int.negSucc 143), (87,
    Int.negSucc 95), (88, Int.ofNat 240), (89, Int.negSucc 143), (90, Int.negSucc 143), (132,
    Int.ofNat 24), (162, Int.ofNat 24), (192, Int.ofNat 96), (252, Int.ofNat 24), (282, Int.ofNat
    24), (468, Int.ofNat 24), (498, Int.ofNat 24), (528, Int.ofNat 96), (588, Int.ofNat 24), (618,
    Int.ofNat 24), (1, Int.negSucc 15), (3, Int.ofNat 32), (29, Int.negSucc 15), (30, Int.ofNat
    16), (32, Int.negSucc 15), (87, Int.ofNat 32), (88, Int.negSucc 15), (192, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (372, Int.ofNat 8), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (192, Int.ofNat 8), (252, Int.ofNat
    8), (282, Int.ofNat 8), (312, Int.ofNat 8), (342, Int.negSucc 7), (372, Int.negSucc 7), (402,
    Int.negSucc 7), (432, Int.ofNat 8), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat
    8), (648, Int.ofNat 8), (678, Int.negSucc 7), (708, Int.negSucc 7), (738, Int.negSucc 7),
    (768, Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (1, Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat
    96), (31, Int.negSucc 111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162,
    Int.negSucc 15), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (738, Int.ofNat 8), (0, Int.ofNat 8), (1, Int.negSucc 23), (2, Int.ofNat 8), (3,
    Int.ofNat 24), (29, Int.negSucc 23), (30, Int.ofNat 64), (31, Int.negSucc 23), (32,
    Int.negSucc 55), (58, Int.ofNat 8), (59, Int.negSucc 23), (60, Int.ofNat 8), (61, Int.ofNat
    24), (87, Int.ofNat 24), (88, Int.negSucc 55), (89, Int.ofNat 24), (90, Int.ofNat 40), (132,
    Int.negSucc 11), (162, Int.negSucc 3), (192, Int.negSucc 15), (222, Int.negSucc 3), (252,
    Int.negSucc 11), (282, Int.negSucc 3), (312, Int.negSucc 3), (432, Int.negSucc 3), (462,
    Int.ofNat 4), (468, Int.negSucc 11), (498, Int.negSucc 3), (528, Int.negSucc 15), (558,
    Int.negSucc 3), (588, Int.negSucc 11), (618, Int.negSucc 3), (648, Int.negSucc 3), (768,
    Int.negSucc 3), (798, Int.ofNat 4), (528, Int.ofNat 128), (588, Int.ofNat 128), (618,
    Int.ofNat 128), (648, Int.ofNat 128), (678, Int.negSucc 127), (708, Int.negSucc 127), (738,
    Int.negSucc 127), (768, Int.ofNat 128), (30, Int.ofNat 32), (57, Int.negSucc 31), (88,
    Int.negSucc 63), (115, Int.ofNat 64), (528, Int.negSucc 31), (588, Int.negSucc 31), (738,
    Int.ofNat 32), (768, Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (1,
    Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 32), (57, Int.negSucc 31), (59,
    Int.negSucc 15), (86, Int.ofNat 16), (88, Int.negSucc 15), (115, Int.ofNat 16), (528,
    Int.negSucc 15), (768, Int.negSucc 15), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618, Int.negSucc 7),
    (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (1,
    Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc 7), (528, Int.negSucc
    7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (29, Int.ofNat 80), (30, Int.negSucc 79), (31, Int.ofNat 80), (32, Int.ofNat
    80), (57, Int.negSucc 79), (87, Int.negSucc 159), (88, Int.ofNat 160), (89, Int.negSucc 159),
    (90, Int.negSucc 159), (115, Int.ofNat 160), (468, Int.ofNat 80), (738, Int.ofNat 80), (768,
    Int.negSucc 79), (813, Int.negSucc 79), (815, Int.ofNat 160), (0, Int.negSucc 63), (1,
    Int.ofNat 64), (2, Int.negSucc 63), (3, Int.negSucc 63), (28, Int.ofNat 64), (29, Int.ofNat
    128), (30, Int.negSucc 127), (31, Int.ofNat 128), (32, Int.ofNat 128), (57, Int.negSucc 127),
    (58, Int.negSucc 63), (59, Int.ofNat 64), (60, Int.negSucc 63), (61, Int.negSucc 63), (86,
    Int.ofNat 64), (87, Int.negSucc 63), (88, Int.ofNat 64), (89, Int.negSucc 63), (90,
    Int.negSucc 63), (115, Int.ofNat 64), (468, Int.ofNat 64), (498, Int.ofNat 64), (558,
    Int.ofNat 64), (678, Int.ofNat 64), (708, Int.ofNat 64), (738, Int.ofNat 64), (768,
    Int.negSucc 63), (812, Int.ofNat 64), (813, Int.negSucc 127), (814, Int.ofNat 64), (815,
    Int.ofNat 64), (29, Int.ofNat 8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8),
    (57, Int.negSucc 7), (58, Int.negSucc 15), (59, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (708, Int.ofNat 8), (768, Int.negSucc
    7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0, Int.negSucc 15), (1, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat 8), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (558, Int.ofNat 8), (678,
    Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat
    40), (31, Int.negSucc 39), (32, Int.negSucc 39), (57, Int.ofNat 40), (87, Int.negSucc 79),
    (89, Int.ofNat 80), (90, Int.ofNat 80), (115, Int.negSucc 79), (468, Int.negSucc 39), (618,
    Int.negSucc 39), (678, Int.ofNat 40), (813, Int.ofNat 40), (815, Int.negSucc 79), (0,
    Int.negSucc 39), (2, Int.ofNat 40), (3, Int.ofNat 40), (28, Int.negSucc 39), (29, Int.ofNat
    80), (31, Int.negSucc 79), (32, Int.negSucc 79), (57, Int.ofNat 80), (58, Int.negSucc 39),
    (60, Int.ofNat 40), (61, Int.ofNat 40), (86, Int.negSucc 39), (87, Int.negSucc 39), (89,
    Int.ofNat 40), (90, Int.ofNat 40), (115, Int.negSucc 39), (468, Int.negSucc 39), (498,
    Int.negSucc 39), (588, Int.negSucc 39), (618, Int.negSucc 39), (812, Int.negSucc 39), (813,
    Int.ofNat 80), (814, Int.negSucc 39), (815, Int.negSucc 39), (29, Int.ofNat 8), (31,
    Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc 15), (60, Int.ofNat
    16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588, Int.negSucc 7),
    (678, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (29, Int.negSucc 39), (31,
    Int.ofNat 40), (32, Int.negSucc 39), (57, Int.ofNat 40), (87, Int.ofNat 80), (89, Int.negSucc
    79), (90, Int.ofNat 80), (115, Int.negSucc 79), (468, Int.negSucc 39), (648, Int.negSucc 39),
    (708, Int.ofNat 40), (813, Int.ofNat 40), (815, Int.negSucc 79), (0, Int.ofNat 40), (2,
    Int.negSucc 39), (3, Int.ofNat 40), (28, Int.negSucc 39), (29, Int.negSucc 79), (31, Int.ofNat
    80), (32, Int.negSucc 79), (57, Int.ofNat 80), (58, Int.ofNat 40), (60, Int.negSucc 39), (61,
    Int.ofNat 40), (86, Int.negSucc 39), (87, Int.ofNat 40), (89, Int.negSucc 39), (90, Int.ofNat
    40), (115, Int.negSucc 39), (468, Int.negSucc 39), (558, Int.negSucc 39), (588, Int.negSucc
    39), (648, Int.negSucc 39), (812, Int.negSucc 39), (813, Int.ofNat 80), (814, Int.negSucc 39),
    (815, Int.negSucc 39), (0, Int.ofNat 48), (2, Int.ofNat 48), (3, Int.negSucc 47), (28,
    Int.negSucc 47), (29, Int.negSucc 143), (31, Int.negSucc 143), (32, Int.ofNat 144), (57,
    Int.ofNat 144), (58, Int.ofNat 48), (60, Int.ofNat 48), (61, Int.negSucc 47), (86, Int.negSucc
    47), (87, Int.ofNat 144), (89, Int.ofNat 144), (90, Int.negSucc 143), (115, Int.negSucc 143),
    (132, Int.ofNat 48), (498, Int.negSucc 47), (558, Int.negSucc 47), (618, Int.negSucc 47),
    (648, Int.negSucc 47), (738, Int.negSucc 47), (768, Int.ofNat 48), (812, Int.negSucc 47),
    (813, Int.ofNat 144), (814, Int.negSucc 47), (815, Int.negSucc 143), (29, Int.negSucc 7), (31,
    Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (58, Int.ofNat 16), (60, Int.ofNat 16),
    (61, Int.negSucc 15), (86, Int.negSucc 15), (498, Int.negSucc 7), (648, Int.negSucc 7), (738,
    Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat 16), (2, Int.negSucc
    15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.ofNat 8), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc 7), (708, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (0, Int.ofNat 16), (2, Int.ofNat 16), (3,
    Int.negSucc 15), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.negSucc 7), (32,
    Int.ofNat 8), (57, Int.ofNat 8), (558, Int.negSucc 7), (618, Int.negSucc 7), (738, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (798, Int.negSucc 47), (813, Int.ofNat 48),
    (840, Int.negSucc 47), (768, Int.ofNat 24), (798, Int.ofNat 24), (812, Int.negSucc 23), (814,
    Int.negSucc 23), (815, Int.negSucc 23), (840, Int.ofNat 48), (588, Int.ofNat 24), (798,
    Int.ofNat 24), (812, Int.ofNat 24), (813, Int.negSucc 47), (814, Int.ofNat 24), (815,
    Int.negSucc 23), (840, Int.ofNat 48), (618, Int.ofNat 24), (798, Int.ofNat 24), (812,
    Int.ofNat 24), (813, Int.negSucc 47), (814, Int.negSucc 23), (815, Int.ofNat 24), (840,
    Int.ofNat 48), (648, Int.ofNat 24), (798, Int.ofNat 24), (812, Int.negSucc 23), (813,
    Int.negSucc 47), (814, Int.ofNat 24), (815, Int.ofNat 24), (840, Int.ofNat 48), (468,
    Int.ofNat 40), (798, Int.negSucc 39), (815, Int.ofNat 80), (840, Int.negSucc 79), (498,
    Int.ofNat 24), (798, Int.negSucc 23), (814, Int.ofNat 48), (840, Int.negSucc 47), (558,
    Int.ofNat 24), (798, Int.negSucc 23), (812, Int.ofNat 48), (840, Int.negSucc 47), (29,
    Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57, Int.ofNat 16), (87, Int.ofNat
    32), (89, Int.ofNat 32), (90, Int.negSucc 31), (115, Int.negSucc 31), (738, Int.negSucc 15),
    (768, Int.ofNat 16), (798, Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 11, mode := 3, source := [(11, Int.negSucc 2), (40, Int.ofNat 5), (69, Int.negSucc
    0), (98, Int.negSucc 4), (125, Int.ofNat 3), (153, Int.ofNat 1), (237, Int.ofNat 1), (265,
    Int.ofNat 3), (319, Int.negSucc 2), (320, Int.ofNat 5), (321, Int.negSucc 0), (322,
    Int.negSucc 4), (425, Int.ofNat 1), (565, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 8), (32, Int.negSucc 15), (88, Int.negSucc 15), (90, Int.ofNat 32),
    (132, Int.negSucc 7), (468, Int.negSucc 7), (30, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc
    31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat 8), (342, Int.negSucc 7), (528,
    Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678, Int.negSucc 7), (0, Int.negSucc
    23), (1, Int.ofNat 60), (2, Int.negSucc 23), (3, Int.negSucc 47), (29, Int.ofNat 60), (30,
    Int.negSucc 143), (31, Int.ofNat 60), (32, Int.ofNat 108), (58, Int.negSucc 23), (59,
    Int.ofNat 60), (60, Int.negSucc 23), (61, Int.negSucc 47), (87, Int.negSucc 47), (88,
    Int.ofNat 108), (89, Int.negSucc 47), (90, Int.negSucc 71), (132, Int.ofNat 12), (192,
    Int.ofNat 36), (252, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat 36), (588, Int.ofNat
    12), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 32), (3, Int.ofNat 32), (29,
    Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 79), (32, Int.negSucc 79), (58,
    Int.ofNat 32), (59, Int.negSucc 79), (60, Int.ofNat 48), (61, Int.ofNat 48), (87, Int.ofNat
    32), (88, Int.negSucc 79), (89, Int.ofNat 48), (90, Int.ofNat 48), (132, Int.negSucc 7), (162,
    Int.negSucc 7), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 7), (468,
    Int.negSucc 7), (498, Int.negSucc 7), (528, Int.negSucc 31), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat
    8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402,
    Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat
    8), (768, Int.negSucc 7), (0, Int.ofNat 72), (1, Int.negSucc 119), (2, Int.ofNat 48), (3,
    Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat 192), (31, Int.negSucc 71), (32,
    Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71), (60, Int.ofNat 24), (61, Int.ofNat
    48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89, Int.ofNat 48), (90, Int.ofNat 72), (132,
    Int.negSucc 11), (192, Int.negSucc 47), (222, Int.negSucc 11), (252, Int.negSucc 11), (312,
    Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 47), (558, Int.negSucc 11), (588,
    Int.negSucc 11), (648, Int.negSucc 11), (1, Int.ofNat 32), (2, Int.negSucc 63), (29, Int.ofNat
    32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58, Int.negSucc 63), (59,
    Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88, Int.ofNat 32), (89,
    Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat
    32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498, Int.ofNat 16),
    (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (738, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc
    7), (3, Int.negSucc 7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32,
    Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4),
    (192, Int.ofNat 4), (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558,
    Int.ofNat 12), (648, Int.ofNat 4), (528, Int.ofNat 104), (588, Int.ofNat 104), (618, Int.ofNat
    104), (648, Int.ofNat 104), (678, Int.negSucc 103), (708, Int.negSucc 103), (738, Int.negSucc
    103), (768, Int.ofNat 104), (30, Int.ofNat 56), (57, Int.negSucc 55), (88, Int.negSucc 111),
    (115, Int.ofNat 112), (528, Int.negSucc 55), (588, Int.negSucc 55), (738, Int.ofNat 56), (768,
    Int.negSucc 55), (813, Int.negSucc 55), (815, Int.ofNat 112), (1, Int.negSucc 15), (28,
    Int.ofNat 16), (30, Int.ofNat 32), (57, Int.negSucc 31), (59, Int.negSucc 15), (86, Int.ofNat
    16), (88, Int.negSucc 15), (115, Int.ofNat 16), (528, Int.negSucc 15), (768, Int.negSucc 15),
    (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat
    16), (528, Int.negSucc 7), (618, Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7),
    (813, Int.negSucc 7), (814, Int.ofNat 16), (1, Int.negSucc 47), (28, Int.ofNat 48), (30,
    Int.ofNat 24), (57, Int.negSucc 23), (528, Int.negSucc 23), (648, Int.negSucc 23), (678,
    Int.ofNat 24), (768, Int.negSucc 23), (812, Int.ofNat 48), (813, Int.negSucc 23), (29,
    Int.ofNat 56), (30, Int.negSucc 55), (31, Int.ofNat 56), (32, Int.ofNat 56), (57, Int.negSucc
    55), (87, Int.negSucc 111), (88, Int.ofNat 112), (89, Int.negSucc 111), (90, Int.negSucc 111),
    (115, Int.ofNat 112), (468, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (813,
    Int.negSucc 55), (815, Int.ofNat 112), (0, Int.negSucc 55), (1, Int.ofNat 56), (2, Int.negSucc
    55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.ofNat 112), (30, Int.negSucc 111), (31,
    Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111), (58, Int.negSucc 55), (59,
    Int.ofNat 56), (60, Int.negSucc 55), (61, Int.negSucc 55), (86, Int.ofNat 56), (87,
    Int.negSucc 55), (88, Int.ofNat 56), (89, Int.negSucc 55), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 56), (498, Int.ofNat 56), (558, Int.ofNat 56), (678, Int.ofNat
    56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812, Int.ofNat 56),
    (813, Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (29, Int.negSucc 31), (30,
    Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat
    64), (59, Int.negSucc 63), (60, Int.ofNat 64), (61, Int.ofNat 64), (86, Int.negSucc 63), (498,
    Int.negSucc 31), (708, Int.negSucc 31), (768, Int.ofNat 32), (813, Int.ofNat 32), (814,
    Int.negSucc 63), (0, Int.negSucc 31), (1, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc
    31), (28, Int.ofNat 32), (29, Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.ofNat 16), (57, Int.negSucc 15), (558, Int.ofNat 16), (678, Int.ofNat 16), (768,
    Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 40), (31,
    Int.negSucc 39), (32, Int.negSucc 39), (57, Int.ofNat 40), (87, Int.negSucc 79), (89,
    Int.ofNat 80), (90, Int.ofNat 80), (115, Int.negSucc 79), (468, Int.negSucc 39), (618,
    Int.negSucc 39), (678, Int.ofNat 40), (813, Int.ofNat 40), (815, Int.negSucc 79), (0,
    Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.ofNat
    64), (31, Int.negSucc 63), (32, Int.negSucc 63), (57, Int.ofNat 64), (58, Int.negSucc 31),
    (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc 31), (87, Int.negSucc 31), (89,
    Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 31), (498,
    Int.negSucc 31), (588, Int.negSucc 31), (618, Int.negSucc 31), (812, Int.negSucc 31), (813,
    Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (29, Int.negSucc 7), (31,
    Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.ofNat 16), (60, Int.negSucc
    15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (588, Int.ofNat 8), (678,
    Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (29, Int.negSucc 47), (31,
    Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (87, Int.ofNat 96), (89, Int.negSucc
    95), (90, Int.ofNat 96), (115, Int.negSucc 95), (468, Int.negSucc 47), (648, Int.negSucc 47),
    (708, Int.ofNat 48), (813, Int.ofNat 48), (815, Int.negSucc 95), (0, Int.ofNat 24), (2,
    Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc 47), (31, Int.ofNat
    48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60, Int.negSucc 23), (61,
    Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89, Int.negSucc 23), (90, Int.ofNat
    24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558, Int.negSucc 23), (588, Int.negSucc
    23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23),
    (815, Int.negSucc 23), (0, Int.ofNat 40), (2, Int.ofNat 40), (3, Int.negSucc 39), (28,
    Int.negSucc 39), (29, Int.negSucc 119), (31, Int.negSucc 119), (32, Int.ofNat 120), (57,
    Int.ofNat 120), (58, Int.ofNat 40), (60, Int.ofNat 40), (61, Int.negSucc 39), (86, Int.negSucc
    39), (87, Int.ofNat 120), (89, Int.ofNat 120), (90, Int.negSucc 119), (115, Int.negSucc 119),
    (132, Int.ofNat 40), (498, Int.negSucc 39), (558, Int.negSucc 39), (618, Int.negSucc 39),
    (648, Int.negSucc 39), (738, Int.negSucc 39), (768, Int.ofNat 40), (812, Int.negSucc 39),
    (813, Int.ofNat 120), (814, Int.negSucc 39), (815, Int.negSucc 119), (29, Int.ofNat 16), (31,
    Int.ofNat 16), (32, Int.negSucc 15), (57, Int.negSucc 15), (58, Int.negSucc 31), (60,
    Int.negSucc 31), (61, Int.ofNat 32), (86, Int.ofNat 32), (498, Int.ofNat 16), (648, Int.ofNat
    16), (738, Int.negSucc 15), (813, Int.negSucc 15), (814, Int.ofNat 32), (0, Int.ofNat 48), (2,
    Int.negSucc 47), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.negSucc 23), (31, Int.ofNat
    24), (32, Int.negSucc 23), (57, Int.ofNat 24), (558, Int.negSucc 23), (588, Int.negSucc 23),
    (708, Int.ofNat 24), (812, Int.negSucc 47), (813, Int.ofNat 24), (0, Int.ofNat 48), (2,
    Int.ofNat 48), (3, Int.negSucc 47), (28, Int.negSucc 47), (29, Int.negSucc 23), (31,
    Int.negSucc 23), (32, Int.ofNat 24), (57, Int.ofNat 24), (558, Int.negSucc 23), (618,
    Int.negSucc 23), (738, Int.ofNat 24), (812, Int.negSucc 47), (813, Int.ofNat 24), (798,
    Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 48), (798, Int.negSucc 47), (815,
    Int.ofNat 96), (840, Int.negSucc 95), (498, Int.ofNat 16), (798, Int.negSucc 15), (814,
    Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 32), (798, Int.negSucc 31), (812,
    Int.ofNat 64), (840, Int.negSucc 63), (29, Int.negSucc 31), (31, Int.negSucc 31), (32,
    Int.ofNat 32), (57, Int.ofNat 32), (87, Int.ofNat 64), (89, Int.ofNat 64), (90, Int.negSucc
    63), (115, Int.negSucc 63), (738, Int.negSucc 31), (768, Int.ofNat 32), (798, Int.ofNat 32),
    (813, Int.negSucc 31), (840, Int.ofNat 64), (0, Int.negSucc 31), (2, Int.ofNat 32), (3,
    Int.ofNat 32), (28, Int.negSucc 31), (29, Int.ofNat 16), (31, Int.negSucc 15), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (678, Int.negSucc 15), (768, Int.ofNat 16), (798,
    Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 32), (812,
    Int.negSucc 31), (813, Int.ofNat 32), (814, Int.negSucc 31), (815, Int.negSucc 31), (840,
    Int.ofNat 32), (798, Int.negSucc 15), (812, Int.ofNat 16), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 15), (798, Int.negSucc 7), (812, Int.negSucc 7), (814,
    Int.ofNat 8), (815, Int.ofNat 8), (840, Int.negSucc 7)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 3, source := [(15, Int.ofNat 2), (44, Int.negSucc 5), (73, Int.ofNat 2),
    (102, Int.ofNat 6), (188, Int.negSucc 3), (245, Int.negSucc 2), (273, Int.negSucc 0), (301,
    Int.negSucc 0), (412, Int.negSucc 0), (436, Int.negSucc 0), (463, Int.ofNat 1), (827,
    Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.negSucc 63), (32, Int.ofNat 128), (88, Int.ofNat 128), (90, Int.negSucc
    255), (132, Int.ofNat 64), (468, Int.ofNat 64), (1, Int.negSucc 19), (3, Int.ofNat 40), (29,
    Int.negSucc 19), (30, Int.ofNat 120), (31, Int.negSucc 19), (32, Int.negSucc 179), (59,
    Int.negSucc 19), (61, Int.ofNat 40), (87, Int.ofNat 40), (88, Int.negSucc 179), (89, Int.ofNat
    40), (90, Int.ofNat 240), (132, Int.negSucc 59), (192, Int.negSucc 19), (252, Int.negSucc 19),
    (468, Int.negSucc 59), (528, Int.negSucc 19), (588, Int.negSucc 19), (0, Int.negSucc 55), (1,
    Int.ofNat 140), (2, Int.negSucc 55), (3, Int.negSucc 111), (29, Int.ofNat 140), (30,
    Int.negSucc 335), (31, Int.ofNat 140), (32, Int.ofNat 252), (58, Int.negSucc 55), (59,
    Int.ofNat 140), (60, Int.negSucc 55), (61, Int.negSucc 111), (87, Int.negSucc 111), (88,
    Int.ofNat 252), (89, Int.negSucc 111), (90, Int.negSucc 167), (132, Int.ofNat 28), (192,
    Int.ofNat 84), (252, Int.ofNat 28), (468, Int.ofNat 28), (528, Int.ofNat 84), (588, Int.ofNat
    28), (0, Int.ofNat 32), (1, Int.negSucc 95), (2, Int.ofNat 64), (3, Int.ofNat 64), (29,
    Int.negSucc 95), (30, Int.ofNat 256), (31, Int.negSucc 159), (32, Int.negSucc 159), (58,
    Int.ofNat 64), (59, Int.negSucc 159), (60, Int.ofNat 96), (61, Int.ofNat 96), (87, Int.ofNat
    64), (88, Int.negSucc 159), (89, Int.ofNat 96), (90, Int.ofNat 96), (132, Int.negSucc 15),
    (162, Int.negSucc 15), (192, Int.negSucc 63), (252, Int.negSucc 15), (282, Int.negSucc 15),
    (468, Int.negSucc 15), (498, Int.negSucc 15), (528, Int.negSucc 63), (588, Int.negSucc 15),
    (618, Int.negSucc 15), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30,
    Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat
    4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588,
    Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 3), (252,
    Int.negSucc 3), (282, Int.negSucc 3), (312, Int.negSucc 3), (342, Int.ofNat 4), (372,
    Int.ofNat 4), (402, Int.ofNat 4), (432, Int.negSucc 3), (528, Int.negSucc 3), (588,
    Int.negSucc 3), (618, Int.negSucc 3), (648, Int.negSucc 3), (678, Int.ofNat 4), (708,
    Int.ofNat 4), (738, Int.ofNat 4), (768, Int.negSucc 3), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 16), (2, Int.negSucc
    31), (29, Int.ofNat 16), (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58,
    Int.negSucc 31), (59, Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat
    4), (282, Int.ofNat 16), (312, Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498,
    Int.ofNat 8), (528, Int.ofNat 16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat
    4), (678, Int.negSucc 3), (738, Int.negSucc 3), (0, Int.negSucc 15), (1, Int.ofNat 48), (2,
    Int.negSucc 15), (3, Int.negSucc 47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 112), (58, Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47),
    (90, Int.negSucc 79), (132, Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222,
    Int.ofNat 8), (252, Int.ofNat 24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8),
    (462, Int.negSucc 7), (468, Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558,
    Int.ofNat 8), (588, Int.ofNat 24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8),
    (798, Int.negSucc 7), (528, Int.negSucc 87), (588, Int.negSucc 87), (618, Int.negSucc 87),
    (648, Int.negSucc 87), (678, Int.ofNat 88), (708, Int.ofNat 88), (738, Int.ofNat 88), (768,
    Int.negSucc 87), (30, Int.negSucc 39), (57, Int.ofNat 40), (88, Int.ofNat 80), (115,
    Int.negSucc 79), (528, Int.ofNat 40), (588, Int.ofNat 40), (738, Int.negSucc 39), (768,
    Int.ofNat 40), (813, Int.ofNat 40), (815, Int.negSucc 79), (1, Int.ofNat 16), (28, Int.negSucc
    15), (30, Int.negSucc 31), (57, Int.ofNat 32), (59, Int.ofNat 16), (86, Int.negSucc 15), (88,
    Int.ofNat 16), (115, Int.negSucc 15), (528, Int.ofNat 16), (768, Int.ofNat 16), (798,
    Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815,
    Int.negSucc 15), (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat 16), (86, Int.negSucc
    15), (528, Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768, Int.ofNat 8), (813,
    Int.ofNat 8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc 15), (30, Int.negSucc
    7), (57, Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678, Int.negSucc 7), (768,
    Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 63), (30, Int.ofNat
    64), (31, Int.negSucc 63), (32, Int.negSucc 63), (57, Int.ofNat 64), (87, Int.ofNat 128), (88,
    Int.negSucc 127), (89, Int.ofNat 128), (90, Int.ofNat 128), (115, Int.negSucc 127), (468,
    Int.negSucc 63), (738, Int.negSucc 63), (768, Int.ofNat 64), (813, Int.ofNat 64), (815,
    Int.negSucc 127), (0, Int.ofNat 40), (1, Int.negSucc 39), (2, Int.ofNat 40), (3, Int.ofNat
    40), (28, Int.negSucc 39), (29, Int.negSucc 79), (30, Int.ofNat 80), (31, Int.negSucc 79),
    (32, Int.negSucc 79), (57, Int.ofNat 80), (58, Int.ofNat 40), (59, Int.negSucc 39), (60,
    Int.ofNat 40), (61, Int.ofNat 40), (86, Int.negSucc 39), (87, Int.ofNat 40), (88, Int.negSucc
    39), (89, Int.ofNat 40), (90, Int.ofNat 40), (115, Int.negSucc 39), (468, Int.negSucc 39),
    (498, Int.negSucc 39), (558, Int.negSucc 39), (678, Int.negSucc 39), (708, Int.negSucc 39),
    (738, Int.negSucc 39), (768, Int.ofNat 40), (812, Int.negSucc 39), (813, Int.ofNat 80), (814,
    Int.negSucc 39), (815, Int.negSucc 39), (29, Int.negSucc 35), (31, Int.ofNat 36), (32,
    Int.ofNat 36), (57, Int.negSucc 35), (87, Int.ofNat 72), (89, Int.negSucc 71), (90,
    Int.negSucc 71), (115, Int.ofNat 72), (468, Int.ofNat 36), (618, Int.ofNat 36), (678,
    Int.negSucc 35), (813, Int.negSucc 35), (815, Int.ofNat 72), (0, Int.ofNat 24), (2,
    Int.negSucc 23), (3, Int.negSucc 23), (28, Int.ofNat 24), (29, Int.negSucc 47), (31, Int.ofNat
    48), (32, Int.ofNat 48), (57, Int.negSucc 47), (58, Int.ofNat 24), (60, Int.negSucc 23), (61,
    Int.negSucc 23), (86, Int.ofNat 24), (87, Int.ofNat 24), (89, Int.negSucc 23), (90,
    Int.negSucc 23), (115, Int.ofNat 24), (468, Int.ofNat 24), (498, Int.ofNat 24), (588,
    Int.ofNat 24), (618, Int.ofNat 24), (812, Int.ofNat 24), (813, Int.negSucc 47), (814,
    Int.ofNat 24), (815, Int.ofNat 24), (29, Int.negSucc 3), (31, Int.ofNat 4), (32, Int.ofNat 4),
    (57, Int.negSucc 3), (58, Int.ofNat 8), (60, Int.negSucc 7), (61, Int.negSucc 7), (86,
    Int.ofNat 8), (498, Int.ofNat 4), (588, Int.ofNat 4), (678, Int.negSucc 3), (813, Int.negSucc
    3), (814, Int.ofNat 8), (29, Int.ofNat 36), (31, Int.negSucc 35), (32, Int.ofNat 36), (57,
    Int.negSucc 35), (87, Int.negSucc 71), (89, Int.ofNat 72), (90, Int.negSucc 71), (115,
    Int.ofNat 72), (468, Int.ofNat 36), (648, Int.ofNat 36), (708, Int.negSucc 35), (813,
    Int.negSucc 35), (815, Int.ofNat 72), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.negSucc
    23), (28, Int.ofNat 24), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.ofNat 48), (57,
    Int.negSucc 47), (58, Int.negSucc 23), (60, Int.ofNat 24), (61, Int.negSucc 23), (86,
    Int.ofNat 24), (87, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.negSucc 23), (115, Int.ofNat
    24), (468, Int.ofNat 24), (558, Int.ofNat 24), (588, Int.ofNat 24), (648, Int.ofNat 24), (812,
    Int.ofNat 24), (813, Int.negSucc 47), (814, Int.ofNat 24), (815, Int.ofNat 24), (0,
    Int.negSucc 31), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.ofNat 32), (29, Int.ofNat
    96), (31, Int.ofNat 96), (32, Int.negSucc 95), (57, Int.negSucc 95), (58, Int.negSucc 31),
    (60, Int.negSucc 31), (61, Int.ofNat 32), (86, Int.ofNat 32), (87, Int.negSucc 95), (89,
    Int.negSucc 95), (90, Int.ofNat 96), (115, Int.ofNat 96), (132, Int.negSucc 31), (498,
    Int.ofNat 32), (558, Int.ofNat 32), (618, Int.ofNat 32), (648, Int.ofNat 32), (738, Int.ofNat
    32), (768, Int.negSucc 31), (812, Int.ofNat 32), (813, Int.negSucc 95), (814, Int.ofNat 32),
    (815, Int.ofNat 96), (29, Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57,
    Int.negSucc 3), (58, Int.negSucc 7), (60, Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat
    8), (498, Int.ofNat 4), (648, Int.ofNat 4), (738, Int.negSucc 3), (813, Int.negSucc 3), (814,
    Int.ofNat 8), (0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8),
    (29, Int.ofNat 4), (31, Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558,
    Int.ofNat 4), (588, Int.ofNat 4), (708, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc
    3), (0, Int.negSucc 7), (2, Int.negSucc 7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29,
    Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4),
    (618, Int.ofNat 4), (738, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798,
    Int.ofNat 48), (813, Int.negSucc 47), (840, Int.ofNat 48), (768, Int.negSucc 35), (798,
    Int.negSucc 35), (812, Int.ofNat 36), (814, Int.ofNat 36), (815, Int.ofNat 36), (840,
    Int.negSucc 71), (738, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813,
    Int.negSucc 7), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (588,
    Int.negSucc 19), (798, Int.negSucc 19), (812, Int.negSucc 19), (813, Int.ofNat 40), (814,
    Int.negSucc 19), (815, Int.ofNat 20), (840, Int.negSucc 39), (618, Int.negSucc 19), (798,
    Int.negSucc 19), (812, Int.negSucc 19), (813, Int.ofNat 40), (814, Int.ofNat 20), (815,
    Int.negSucc 19), (840, Int.negSucc 39), (648, Int.negSucc 19), (798, Int.negSucc 19), (812,
    Int.ofNat 20), (813, Int.ofNat 40), (814, Int.negSucc 19), (815, Int.negSucc 19), (840,
    Int.negSucc 39), (468, Int.negSucc 47), (798, Int.ofNat 48), (815, Int.negSucc 95), (840,
    Int.ofNat 96), (498, Int.negSucc 23), (798, Int.ofNat 24), (814, Int.negSucc 47), (840,
    Int.ofNat 48), (558, Int.negSucc 23), (798, Int.ofNat 24), (812, Int.negSucc 47), (840,
    Int.ofNat 48), (29, Int.ofNat 24), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.negSucc
    23), (87, Int.negSucc 47), (89, Int.negSucc 47), (90, Int.ofNat 48), (115, Int.ofNat 48),
    (738, Int.ofNat 24), (768, Int.negSucc 23), (798, Int.negSucc 23), (813, Int.ofNat 24), (840,
    Int.negSucc 47), (798, Int.negSucc 39), (812, Int.ofNat 40), (813, Int.negSucc 39), (814,
    Int.ofNat 40), (815, Int.ofNat 40), (840, Int.negSucc 39), (798, Int.ofNat 20), (812,
    Int.negSucc 19), (814, Int.negSucc 19), (815, Int.ofNat 20), (840, Int.ofNat 20), (798,
    Int.ofNat 4), (812, Int.negSucc 3), (814, Int.ofNat 4), (815, Int.negSucc 3), (840, Int.ofNat
    4), (798, Int.ofNat 8), (812, Int.ofNat 8), (814, Int.negSucc 7), (815, Int.negSucc 7), (840,
    Int.ofNat 8), (812, Int.negSucc 7), (813, Int.ofNat 4), (840, Int.ofNat 4)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 3, source := [(14, Int.ofNat 1), (43, Int.negSucc 3), (72, Int.ofNat 1),
    (101, Int.ofNat 5), (129, Int.negSucc 2), (157, Int.negSucc 0), (214, Int.ofNat 1), (407,
    Int.negSucc 0), (434, Int.ofNat 1), (537, Int.ofNat 1), (826, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 31), (32, Int.ofNat 64), (88, Int.ofNat 64), (90, Int.negSucc
    127), (132, Int.ofNat 32), (468, Int.ofNat 32), (1, Int.negSucc 11), (3, Int.ofNat 24), (29,
    Int.negSucc 11), (30, Int.ofNat 72), (31, Int.negSucc 11), (32, Int.negSucc 107), (59,
    Int.negSucc 11), (61, Int.ofNat 24), (87, Int.ofNat 24), (88, Int.negSucc 107), (89, Int.ofNat
    24), (90, Int.ofNat 144), (132, Int.negSucc 35), (192, Int.negSucc 11), (252, Int.negSucc 11),
    (468, Int.negSucc 35), (528, Int.negSucc 11), (588, Int.negSucc 11), (0, Int.negSucc 71), (1,
    Int.ofNat 180), (2, Int.negSucc 71), (3, Int.negSucc 143), (29, Int.ofNat 180), (30,
    Int.negSucc 431), (31, Int.ofNat 180), (32, Int.ofNat 324), (58, Int.negSucc 71), (59,
    Int.ofNat 180), (60, Int.negSucc 71), (61, Int.negSucc 143), (87, Int.negSucc 143), (88,
    Int.ofNat 324), (89, Int.negSucc 143), (90, Int.negSucc 215), (132, Int.ofNat 36), (192,
    Int.ofNat 108), (252, Int.ofNat 36), (468, Int.ofNat 36), (528, Int.ofNat 108), (588,
    Int.ofNat 36), (0, Int.ofNat 48), (1, Int.negSucc 143), (2, Int.ofNat 96), (3, Int.ofNat 96),
    (29, Int.negSucc 143), (30, Int.ofNat 384), (31, Int.negSucc 239), (32, Int.negSucc 239), (58,
    Int.ofNat 96), (59, Int.negSucc 239), (60, Int.ofNat 144), (61, Int.ofNat 144), (87, Int.ofNat
    96), (88, Int.negSucc 239), (89, Int.ofNat 144), (90, Int.ofNat 144), (132, Int.negSucc 23),
    (162, Int.negSucc 23), (192, Int.negSucc 95), (252, Int.negSucc 23), (282, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (528, Int.negSucc 95), (588, Int.negSucc 23),
    (618, Int.negSucc 23), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30,
    Int.negSucc 15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat
    8), (252, Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588,
    Int.ofNat 8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252,
    Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372,
    Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (528, Int.negSucc 119), (588, Int.negSucc
    119), (618, Int.negSucc 119), (648, Int.negSucc 119), (678, Int.ofNat 120), (708, Int.ofNat
    120), (738, Int.ofNat 120), (768, Int.negSucc 119), (30, Int.negSucc 71), (57, Int.ofNat 72),
    (88, Int.ofNat 144), (115, Int.negSucc 143), (528, Int.ofNat 72), (588, Int.ofNat 72), (738,
    Int.negSucc 71), (768, Int.ofNat 72), (813, Int.ofNat 72), (815, Int.negSucc 143), (1,
    Int.ofNat 24), (28, Int.negSucc 23), (30, Int.negSucc 47), (57, Int.ofNat 48), (59, Int.ofNat
    24), (86, Int.negSucc 23), (88, Int.ofNat 24), (115, Int.negSucc 23), (528, Int.ofNat 24),
    (768, Int.ofNat 24), (798, Int.negSucc 23), (812, Int.negSucc 23), (813, Int.ofNat 48), (814,
    Int.negSucc 23), (815, Int.negSucc 23), (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat
    16), (86, Int.negSucc 15), (528, Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768,
    Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc
    15), (30, Int.negSucc 7), (57, Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29,
    Int.negSucc 95), (30, Int.ofNat 96), (31, Int.negSucc 95), (32, Int.negSucc 95), (57,
    Int.ofNat 96), (87, Int.ofNat 192), (88, Int.negSucc 191), (89, Int.ofNat 192), (90, Int.ofNat
    192), (115, Int.negSucc 191), (468, Int.negSucc 95), (738, Int.negSucc 95), (768, Int.ofNat
    96), (813, Int.ofNat 96), (815, Int.negSucc 191), (0, Int.ofNat 24), (1, Int.negSucc 23), (2,
    Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc 47), (30, Int.ofNat
    48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (59,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat
    24), (88, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (558, Int.negSucc 23), (678, Int.negSucc 23),
    (708, Int.negSucc 23), (738, Int.negSucc 23), (768, Int.ofNat 24), (812, Int.negSucc 23),
    (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29, Int.negSucc 7), (30,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16),
    (59, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498,
    Int.negSucc 7), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (0, Int.ofNat 16), (1, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16),
    (28, Int.negSucc 15), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 71), (31, Int.ofNat 72), (32,
    Int.ofNat 72), (57, Int.negSucc 71), (87, Int.ofNat 144), (89, Int.negSucc 143), (90,
    Int.negSucc 143), (115, Int.ofNat 144), (468, Int.ofNat 72), (618, Int.ofNat 72), (678,
    Int.negSucc 71), (813, Int.negSucc 71), (815, Int.ofNat 144), (0, Int.ofNat 24), (2,
    Int.negSucc 23), (3, Int.negSucc 23), (28, Int.ofNat 24), (29, Int.negSucc 47), (31, Int.ofNat
    48), (32, Int.ofNat 48), (57, Int.negSucc 47), (58, Int.ofNat 24), (60, Int.negSucc 23), (61,
    Int.negSucc 23), (86, Int.ofNat 24), (87, Int.ofNat 24), (89, Int.negSucc 23), (90,
    Int.negSucc 23), (115, Int.ofNat 24), (468, Int.ofNat 24), (498, Int.ofNat 24), (588,
    Int.ofNat 24), (618, Int.ofNat 24), (812, Int.ofNat 24), (813, Int.negSucc 47), (814,
    Int.ofNat 24), (815, Int.ofNat 24), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8),
    (57, Int.negSucc 7), (58, Int.ofNat 16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (498, Int.ofNat 8), (588, Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc
    7), (814, Int.ofNat 16), (29, Int.ofNat 72), (31, Int.negSucc 71), (32, Int.ofNat 72), (57,
    Int.negSucc 71), (87, Int.negSucc 143), (89, Int.ofNat 144), (90, Int.negSucc 143), (115,
    Int.ofNat 144), (468, Int.ofNat 72), (648, Int.ofNat 72), (708, Int.negSucc 71), (813,
    Int.negSucc 71), (815, Int.ofNat 144), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.negSucc
    23), (28, Int.ofNat 24), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.ofNat 48), (57,
    Int.negSucc 47), (58, Int.negSucc 23), (60, Int.ofNat 24), (61, Int.negSucc 23), (86,
    Int.ofNat 24), (87, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.negSucc 23), (115, Int.ofNat
    24), (468, Int.ofNat 24), (558, Int.ofNat 24), (588, Int.ofNat 24), (648, Int.ofNat 24), (812,
    Int.ofNat 24), (813, Int.negSucc 47), (814, Int.ofNat 24), (815, Int.ofNat 24), (0,
    Int.negSucc 23), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.ofNat 24), (29, Int.ofNat
    72), (31, Int.ofNat 72), (32, Int.negSucc 71), (57, Int.negSucc 71), (58, Int.negSucc 23),
    (60, Int.negSucc 23), (61, Int.ofNat 24), (86, Int.ofNat 24), (87, Int.negSucc 71), (89,
    Int.negSucc 71), (90, Int.ofNat 72), (115, Int.ofNat 72), (132, Int.negSucc 23), (498,
    Int.ofNat 24), (558, Int.ofNat 24), (618, Int.ofNat 24), (648, Int.ofNat 24), (738, Int.ofNat
    24), (768, Int.negSucc 23), (812, Int.ofNat 24), (813, Int.negSucc 71), (814, Int.ofNat 24),
    (815, Int.ofNat 72), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
    Int.negSucc 7), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat
    16), (498, Int.ofNat 8), (648, Int.ofNat 8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.ofNat
    16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.negSucc 7), (558,
    Int.ofNat 8), (588, Int.ofNat 8), (708, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc
    7), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29,
    Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8),
    (618, Int.ofNat 8), (738, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798,
    Int.ofNat 32), (813, Int.negSucc 31), (840, Int.ofNat 32), (768, Int.negSucc 47), (798,
    Int.negSucc 47), (812, Int.ofNat 48), (814, Int.ofNat 48), (815, Int.ofNat 48), (840,
    Int.negSucc 95), (738, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813,
    Int.negSucc 15), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (588,
    Int.negSucc 15), (798, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.negSucc 31), (618, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 31), (648, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.negSucc 31), (468, Int.negSucc 71), (798, Int.ofNat 72), (815, Int.negSucc 143), (840,
    Int.ofNat 144), (498, Int.negSucc 23), (798, Int.ofNat 24), (814, Int.negSucc 47), (840,
    Int.ofNat 48), (558, Int.negSucc 23), (798, Int.ofNat 24), (812, Int.negSucc 47), (840,
    Int.ofNat 48), (29, Int.ofNat 48), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.negSucc
    47), (87, Int.negSucc 95), (89, Int.negSucc 95), (90, Int.ofNat 96), (115, Int.ofNat 96),
    (738, Int.ofNat 48), (768, Int.negSucc 47), (798, Int.negSucc 47), (813, Int.ofNat 48), (840,
    Int.negSucc 95), (798, Int.negSucc 63), (812, Int.ofNat 64), (813, Int.negSucc 63), (814,
    Int.ofNat 64), (815, Int.ofNat 64), (840, Int.negSucc 63), (798, Int.ofNat 40), (812,
    Int.negSucc 39), (814, Int.negSucc 39), (815, Int.ofNat 40), (840, Int.ofNat 40), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (814, Int.ofNat 8), (815, Int.negSucc 7), (840, Int.ofNat
    8), (798, Int.ofNat 16), (812, Int.ofNat 16), (814, Int.negSucc 15), (815, Int.negSucc 15),
    (840, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.ofNat 8), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 2, source := [(15, Int.ofNat 2), (44, Int.negSucc 5), (73, Int.ofNat 2),
    (102, Int.ofNat 6), (188, Int.negSucc 3), (245, Int.negSucc 2), (273, Int.negSucc 0), (301,
    Int.negSucc 0), (412, Int.negSucc 0), (436, Int.negSucc 0), (463, Int.ofNat 1), (827,
    Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.negSucc 55), (32, Int.ofNat 112), (88, Int.ofNat 112), (90, Int.negSucc
    223), (132, Int.ofNat 56), (468, Int.ofNat 56), (1, Int.negSucc 19), (3, Int.ofNat 40), (29,
    Int.negSucc 19), (30, Int.ofNat 120), (31, Int.negSucc 19), (32, Int.negSucc 179), (59,
    Int.negSucc 19), (61, Int.ofNat 40), (87, Int.ofNat 40), (88, Int.negSucc 179), (89, Int.ofNat
    40), (90, Int.ofNat 240), (132, Int.negSucc 59), (192, Int.negSucc 19), (252, Int.negSucc 19),
    (468, Int.negSucc 59), (528, Int.negSucc 19), (588, Int.negSucc 19), (0, Int.negSucc 55), (1,
    Int.ofNat 140), (2, Int.negSucc 55), (3, Int.negSucc 111), (29, Int.ofNat 140), (30,
    Int.negSucc 335), (31, Int.ofNat 140), (32, Int.ofNat 252), (58, Int.negSucc 55), (59,
    Int.ofNat 140), (60, Int.negSucc 55), (61, Int.negSucc 111), (87, Int.negSucc 111), (88,
    Int.ofNat 252), (89, Int.negSucc 111), (90, Int.negSucc 167), (132, Int.ofNat 28), (192,
    Int.ofNat 84), (252, Int.ofNat 28), (468, Int.ofNat 28), (528, Int.ofNat 84), (588, Int.ofNat
    28), (0, Int.ofNat 32), (1, Int.negSucc 95), (2, Int.ofNat 64), (3, Int.ofNat 64), (29,
    Int.negSucc 95), (30, Int.ofNat 256), (31, Int.negSucc 159), (32, Int.negSucc 159), (58,
    Int.ofNat 64), (59, Int.negSucc 159), (60, Int.ofNat 96), (61, Int.ofNat 96), (87, Int.ofNat
    64), (88, Int.negSucc 159), (89, Int.ofNat 96), (90, Int.ofNat 96), (132, Int.negSucc 15),
    (162, Int.negSucc 15), (192, Int.negSucc 63), (252, Int.negSucc 15), (282, Int.negSucc 15),
    (468, Int.negSucc 15), (498, Int.negSucc 15), (528, Int.negSucc 63), (588, Int.negSucc 15),
    (618, Int.negSucc 15), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30,
    Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat
    4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588,
    Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 3), (252,
    Int.negSucc 3), (282, Int.negSucc 3), (312, Int.negSucc 3), (342, Int.ofNat 4), (372,
    Int.ofNat 4), (402, Int.ofNat 4), (432, Int.negSucc 3), (528, Int.negSucc 3), (588,
    Int.negSucc 3), (618, Int.negSucc 3), (648, Int.negSucc 3), (678, Int.ofNat 4), (708,
    Int.ofNat 4), (738, Int.ofNat 4), (768, Int.negSucc 3), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 16), (2, Int.negSucc
    31), (29, Int.ofNat 16), (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58,
    Int.negSucc 31), (59, Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat
    4), (282, Int.ofNat 16), (312, Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498,
    Int.ofNat 8), (528, Int.ofNat 16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat
    4), (678, Int.negSucc 3), (738, Int.negSucc 3), (0, Int.negSucc 15), (1, Int.ofNat 48), (2,
    Int.negSucc 15), (3, Int.negSucc 47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 112), (58, Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47),
    (90, Int.negSucc 79), (132, Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222,
    Int.ofNat 8), (252, Int.ofNat 24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8),
    (462, Int.negSucc 7), (468, Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558,
    Int.ofNat 8), (588, Int.ofNat 24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8),
    (798, Int.negSucc 7), (528, Int.negSucc 71), (588, Int.negSucc 71), (618, Int.negSucc 71),
    (648, Int.negSucc 71), (678, Int.ofNat 72), (708, Int.ofNat 72), (738, Int.ofNat 72), (768,
    Int.negSucc 71), (30, Int.negSucc 31), (57, Int.ofNat 32), (88, Int.ofNat 64), (115,
    Int.negSucc 63), (528, Int.ofNat 32), (588, Int.ofNat 32), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (1, Int.ofNat 8), (28, Int.negSucc
    7), (30, Int.negSucc 15), (57, Int.ofNat 16), (59, Int.ofNat 8), (86, Int.negSucc 7), (88,
    Int.ofNat 8), (115, Int.negSucc 7), (528, Int.ofNat 8), (768, Int.ofNat 8), (798, Int.negSucc
    7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814, Int.negSucc 7), (815, Int.negSucc 7),
    (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat 16), (86, Int.negSucc 15), (528,
    Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat
    8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc 15), (30, Int.negSucc 7), (57,
    Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678, Int.negSucc 7), (768, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 47), (30, Int.ofNat 48), (31,
    Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (87, Int.ofNat 96), (88,
    Int.negSucc 95), (89, Int.ofNat 96), (90, Int.ofNat 96), (115, Int.negSucc 95), (468,
    Int.negSucc 47), (738, Int.negSucc 47), (768, Int.ofNat 48), (813, Int.ofNat 48), (815,
    Int.negSucc 95), (0, Int.ofNat 32), (1, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32),
    (28, Int.negSucc 31), (29, Int.negSucc 63), (30, Int.ofNat 64), (31, Int.negSucc 63), (32,
    Int.negSucc 63), (57, Int.ofNat 64), (58, Int.ofNat 32), (59, Int.negSucc 31), (60, Int.ofNat
    32), (61, Int.ofNat 32), (86, Int.negSucc 31), (87, Int.ofNat 32), (88, Int.negSucc 31), (89,
    Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 31), (498,
    Int.negSucc 31), (558, Int.negSucc 31), (678, Int.negSucc 31), (708, Int.negSucc 31), (738,
    Int.negSucc 31), (768, Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 64), (814,
    Int.negSucc 31), (815, Int.negSucc 31), (29, Int.negSucc 27), (31, Int.ofNat 28), (32,
    Int.ofNat 28), (57, Int.negSucc 27), (87, Int.ofNat 56), (89, Int.negSucc 55), (90,
    Int.negSucc 55), (115, Int.ofNat 56), (468, Int.ofNat 28), (618, Int.ofNat 28), (678,
    Int.negSucc 27), (813, Int.negSucc 27), (815, Int.ofNat 56), (0, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.negSucc 31), (31, Int.ofNat
    32), (32, Int.ofNat 32), (57, Int.negSucc 31), (58, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.negSucc 15), (86, Int.ofNat 16), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.negSucc 15), (115, Int.ofNat 16), (468, Int.ofNat 16), (498, Int.ofNat 16), (588,
    Int.ofNat 16), (618, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (29, Int.negSucc 3), (31, Int.ofNat 4), (32, Int.ofNat 4),
    (57, Int.negSucc 3), (58, Int.ofNat 8), (60, Int.negSucc 7), (61, Int.negSucc 7), (86,
    Int.ofNat 8), (498, Int.ofNat 4), (588, Int.ofNat 4), (678, Int.negSucc 3), (813, Int.negSucc
    3), (814, Int.ofNat 8), (29, Int.ofNat 28), (31, Int.negSucc 27), (32, Int.ofNat 28), (57,
    Int.negSucc 27), (87, Int.negSucc 55), (89, Int.ofNat 56), (90, Int.negSucc 55), (115,
    Int.ofNat 56), (468, Int.ofNat 28), (648, Int.ofNat 28), (708, Int.negSucc 27), (813,
    Int.negSucc 27), (815, Int.ofNat 56), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc
    15), (28, Int.ofNat 16), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.ofNat 32), (57,
    Int.negSucc 31), (58, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.ofNat
    16), (468, Int.ofNat 16), (558, Int.ofNat 16), (588, Int.ofNat 16), (648, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (0,
    Int.negSucc 23), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.ofNat 24), (29, Int.ofNat
    72), (31, Int.ofNat 72), (32, Int.negSucc 71), (57, Int.negSucc 71), (58, Int.negSucc 23),
    (60, Int.negSucc 23), (61, Int.ofNat 24), (86, Int.ofNat 24), (87, Int.negSucc 71), (89,
    Int.negSucc 71), (90, Int.ofNat 72), (115, Int.ofNat 72), (132, Int.negSucc 23), (498,
    Int.ofNat 24), (558, Int.ofNat 24), (618, Int.ofNat 24), (648, Int.ofNat 24), (738, Int.ofNat
    24), (768, Int.negSucc 23), (812, Int.ofNat 24), (813, Int.negSucc 71), (814, Int.ofNat 24),
    (815, Int.ofNat 72), (29, Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57,
    Int.negSucc 3), (58, Int.negSucc 7), (60, Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat
    8), (498, Int.ofNat 4), (648, Int.ofNat 4), (738, Int.negSucc 3), (813, Int.negSucc 3), (814,
    Int.ofNat 8), (0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8),
    (29, Int.ofNat 4), (31, Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558,
    Int.ofNat 4), (588, Int.ofNat 4), (708, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc
    3), (0, Int.negSucc 7), (2, Int.negSucc 7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29,
    Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4),
    (618, Int.ofNat 4), (738, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798,
    Int.ofNat 24), (813, Int.negSucc 23), (840, Int.ofNat 24), (768, Int.negSucc 27), (798,
    Int.negSucc 27), (812, Int.ofNat 28), (814, Int.ofNat 28), (815, Int.ofNat 28), (840,
    Int.negSucc 55), (738, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813,
    Int.negSucc 7), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (588,
    Int.negSucc 11), (798, Int.negSucc 11), (812, Int.negSucc 11), (813, Int.ofNat 24), (814,
    Int.negSucc 11), (815, Int.ofNat 12), (840, Int.negSucc 23), (618, Int.negSucc 11), (798,
    Int.negSucc 11), (812, Int.negSucc 11), (813, Int.ofNat 24), (814, Int.ofNat 12), (815,
    Int.negSucc 11), (840, Int.negSucc 23), (648, Int.negSucc 11), (798, Int.negSucc 11), (812,
    Int.ofNat 12), (813, Int.ofNat 24), (814, Int.negSucc 11), (815, Int.negSucc 11), (840,
    Int.negSucc 23), (468, Int.negSucc 31), (798, Int.ofNat 32), (815, Int.negSucc 63), (840,
    Int.ofNat 64), (498, Int.negSucc 15), (798, Int.ofNat 16), (814, Int.negSucc 31), (840,
    Int.ofNat 32), (558, Int.negSucc 15), (798, Int.ofNat 16), (812, Int.negSucc 31), (840,
    Int.ofNat 32), (29, Int.ofNat 16), (31, Int.ofNat 16), (32, Int.negSucc 15), (57, Int.negSucc
    15), (87, Int.negSucc 31), (89, Int.negSucc 31), (90, Int.ofNat 32), (115, Int.ofNat 32),
    (738, Int.ofNat 16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813, Int.ofNat 16), (840,
    Int.negSucc 31), (798, Int.negSucc 19), (812, Int.ofNat 20), (813, Int.negSucc 19), (814,
    Int.ofNat 20), (815, Int.ofNat 20), (840, Int.negSucc 19), (798, Int.ofNat 12), (812,
    Int.negSucc 11), (814, Int.negSucc 11), (815, Int.ofNat 12), (840, Int.ofNat 12), (798,
    Int.ofNat 4), (812, Int.negSucc 3), (814, Int.ofNat 4), (815, Int.negSucc 3), (840, Int.ofNat
    4), (798, Int.ofNat 4), (812, Int.ofNat 4), (814, Int.negSucc 3), (815, Int.negSucc 3), (840,
    Int.ofNat 4)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 3, source := [(14, Int.negSucc 3), (43, Int.ofNat 10), (72, Int.negSucc
    9), (101, Int.negSucc 3), (157, Int.ofNat 2), (326, Int.ofNat 1), (381, Int.negSucc 0), (537,
    Int.negSucc 3)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 32), (32, Int.negSucc 63), (88, Int.negSucc 63), (90, Int.ofNat
    128), (132, Int.negSucc 31), (468, Int.negSucc 31), (1, Int.negSucc 15), (3, Int.ofNat 32),
    (29, Int.negSucc 15), (30, Int.ofNat 96), (31, Int.negSucc 15), (32, Int.negSucc 143), (59,
    Int.negSucc 15), (61, Int.ofNat 32), (87, Int.ofNat 32), (88, Int.negSucc 143), (89, Int.ofNat
    32), (90, Int.ofNat 192), (132, Int.negSucc 47), (192, Int.negSucc 15), (252, Int.negSucc 15),
    (468, Int.negSucc 47), (528, Int.negSucc 15), (588, Int.negSucc 15), (0, Int.negSucc 135), (1,
    Int.ofNat 340), (2, Int.negSucc 135), (3, Int.negSucc 271), (29, Int.ofNat 340), (30,
    Int.negSucc 815), (31, Int.ofNat 340), (32, Int.ofNat 612), (58, Int.negSucc 135), (59,
    Int.ofNat 340), (60, Int.negSucc 135), (61, Int.negSucc 271), (87, Int.negSucc 271), (88,
    Int.ofNat 612), (89, Int.negSucc 271), (90, Int.negSucc 407), (132, Int.ofNat 68), (192,
    Int.ofNat 204), (252, Int.ofNat 68), (468, Int.ofNat 68), (528, Int.ofNat 204), (588,
    Int.ofNat 68), (0, Int.ofNat 96), (1, Int.negSucc 287), (2, Int.ofNat 192), (3, Int.ofNat
    192), (29, Int.negSucc 287), (30, Int.ofNat 768), (31, Int.negSucc 479), (32, Int.negSucc
    479), (58, Int.ofNat 192), (59, Int.negSucc 479), (60, Int.ofNat 288), (61, Int.ofNat 288),
    (87, Int.ofNat 192), (88, Int.negSucc 479), (89, Int.ofNat 288), (90, Int.ofNat 288), (132,
    Int.negSucc 47), (162, Int.negSucc 47), (192, Int.negSucc 191), (252, Int.negSucc 47), (282,
    Int.negSucc 47), (468, Int.negSucc 47), (498, Int.negSucc 47), (528, Int.negSucc 191), (588,
    Int.negSucc 47), (618, Int.negSucc 47), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat
    16), (30, Int.negSucc 95), (31, Int.ofNat 144), (32, Int.ofNat 16), (58, Int.negSucc 31), (59,
    Int.ofNat 144), (60, Int.negSucc 191), (61, Int.negSucc 31), (88, Int.ofNat 16), (89,
    Int.negSucc 31), (162, Int.ofNat 48), (192, Int.ofNat 16), (282, Int.ofNat 16), (498,
    Int.ofNat 48), (528, Int.ofNat 16), (618, Int.ofNat 16), (0, Int.ofNat 72), (1, Int.negSucc
    119), (2, Int.ofNat 48), (3, Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat 192), (31,
    Int.negSucc 71), (32, Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71), (60,
    Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89, Int.ofNat
    48), (90, Int.ofNat 72), (132, Int.negSucc 11), (192, Int.negSucc 47), (222, Int.negSucc 11),
    (252, Int.negSucc 11), (312, Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 47),
    (558, Int.negSucc 11), (588, Int.negSucc 11), (648, Int.negSucc 11), (1, Int.ofNat 32), (2,
    Int.negSucc 63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat
    32), (58, Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63),
    (88, Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252,
    Int.ofNat 8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc
    7), (498, Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648,
    Int.ofNat 8), (678, Int.negSucc 7), (738, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat
    36), (2, Int.negSucc 7), (3, Int.negSucc 7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31,
    Int.ofNat 4), (32, Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7),
    (88, Int.ofNat 4), (192, Int.ofNat 4), (222, Int.ofNat 12), (312, Int.ofNat 4), (528,
    Int.ofNat 4), (558, Int.ofNat 12), (648, Int.ofNat 4), (528, Int.ofNat 272), (588, Int.ofNat
    272), (618, Int.ofNat 272), (648, Int.ofNat 272), (678, Int.negSucc 271), (708, Int.negSucc
    271), (738, Int.negSucc 271), (768, Int.ofNat 272), (30, Int.ofNat 24), (57, Int.negSucc 23),
    (88, Int.negSucc 47), (115, Int.ofNat 48), (528, Int.negSucc 23), (588, Int.negSucc 23), (738,
    Int.ofNat 24), (768, Int.negSucc 23), (813, Int.negSucc 23), (815, Int.ofNat 48), (1,
    Int.negSucc 79), (28, Int.ofNat 80), (30, Int.ofNat 160), (57, Int.negSucc 159), (59,
    Int.negSucc 79), (86, Int.ofNat 80), (88, Int.negSucc 79), (115, Int.ofNat 80), (528,
    Int.negSucc 79), (768, Int.negSucc 79), (798, Int.ofNat 80), (812, Int.ofNat 80), (813,
    Int.negSucc 159), (814, Int.ofNat 80), (815, Int.ofNat 80), (30, Int.ofNat 112), (57,
    Int.negSucc 111), (59, Int.negSucc 223), (86, Int.ofNat 224), (528, Int.negSucc 111), (618,
    Int.negSucc 111), (708, Int.ofNat 112), (768, Int.negSucc 111), (813, Int.negSucc 111), (814,
    Int.ofNat 224), (1, Int.negSucc 47), (28, Int.ofNat 48), (30, Int.ofNat 24), (57, Int.negSucc
    23), (528, Int.negSucc 23), (648, Int.negSucc 23), (678, Int.ofNat 24), (768, Int.negSucc 23),
    (812, Int.ofNat 48), (813, Int.negSucc 23), (29, Int.ofNat 104), (30, Int.negSucc 103), (31,
    Int.ofNat 104), (32, Int.ofNat 104), (57, Int.negSucc 103), (87, Int.negSucc 207), (88,
    Int.ofNat 208), (89, Int.negSucc 207), (90, Int.negSucc 207), (115, Int.ofNat 208), (468,
    Int.ofNat 104), (738, Int.ofNat 104), (768, Int.negSucc 103), (813, Int.negSucc 103), (815,
    Int.ofNat 208), (0, Int.negSucc 95), (1, Int.ofNat 96), (2, Int.negSucc 95), (3, Int.negSucc
    95), (28, Int.ofNat 96), (29, Int.ofNat 192), (30, Int.negSucc 191), (31, Int.ofNat 192), (32,
    Int.ofNat 192), (57, Int.negSucc 191), (58, Int.negSucc 95), (59, Int.ofNat 96), (60,
    Int.negSucc 95), (61, Int.negSucc 95), (86, Int.ofNat 96), (87, Int.negSucc 95), (88,
    Int.ofNat 96), (89, Int.negSucc 95), (90, Int.negSucc 95), (115, Int.ofNat 96), (468,
    Int.ofNat 96), (498, Int.ofNat 96), (558, Int.ofNat 96), (678, Int.ofNat 96), (708, Int.ofNat
    96), (738, Int.ofNat 96), (768, Int.negSucc 95), (812, Int.ofNat 96), (813, Int.negSucc 191),
    (814, Int.ofNat 96), (815, Int.ofNat 96), (29, Int.ofNat 128), (30, Int.negSucc 127), (31,
    Int.ofNat 128), (32, Int.ofNat 128), (57, Int.negSucc 127), (58, Int.negSucc 255), (59,
    Int.ofNat 256), (60, Int.negSucc 255), (61, Int.negSucc 255), (86, Int.ofNat 256), (498,
    Int.ofNat 128), (708, Int.ofNat 128), (768, Int.negSucc 127), (813, Int.negSucc 127), (814,
    Int.ofNat 256), (0, Int.negSucc 63), (1, Int.ofNat 64), (2, Int.negSucc 63), (3, Int.negSucc
    63), (28, Int.ofNat 64), (29, Int.ofNat 32), (30, Int.negSucc 31), (31, Int.ofNat 32), (32,
    Int.ofNat 32), (57, Int.negSucc 31), (558, Int.ofNat 32), (678, Int.ofNat 32), (768,
    Int.negSucc 31), (812, Int.ofNat 64), (813, Int.negSucc 31), (29, Int.ofNat 32), (31,
    Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (87, Int.negSucc 63), (89,
    Int.ofNat 64), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 31), (618,
    Int.negSucc 31), (678, Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (0,
    Int.negSucc 71), (2, Int.ofNat 72), (3, Int.ofNat 72), (28, Int.negSucc 71), (29, Int.ofNat
    144), (31, Int.negSucc 143), (32, Int.negSucc 143), (57, Int.ofNat 144), (58, Int.negSucc 71),
    (60, Int.ofNat 72), (61, Int.ofNat 72), (86, Int.negSucc 71), (87, Int.negSucc 71), (89,
    Int.ofNat 72), (90, Int.ofNat 72), (115, Int.negSucc 71), (468, Int.negSucc 71), (498,
    Int.negSucc 71), (588, Int.negSucc 71), (618, Int.negSucc 71), (812, Int.negSucc 71), (813,
    Int.ofNat 144), (814, Int.negSucc 71), (815, Int.negSucc 71), (29, Int.ofNat 120), (31,
    Int.negSucc 119), (32, Int.negSucc 119), (57, Int.ofNat 120), (58, Int.negSucc 239), (60,
    Int.ofNat 240), (61, Int.ofNat 240), (86, Int.negSucc 239), (498, Int.negSucc 119), (588,
    Int.negSucc 119), (678, Int.ofNat 120), (813, Int.ofNat 120), (814, Int.negSucc 239), (29,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.ofNat 24), (87, Int.ofNat
    48), (89, Int.negSucc 47), (90, Int.ofNat 48), (115, Int.negSucc 47), (468, Int.negSucc 23),
    (648, Int.negSucc 23), (708, Int.ofNat 24), (813, Int.ofNat 24), (815, Int.negSucc 47), (0,
    Int.ofNat 80), (2, Int.negSucc 79), (3, Int.ofNat 80), (28, Int.negSucc 79), (29, Int.negSucc
    159), (31, Int.ofNat 160), (32, Int.negSucc 159), (57, Int.ofNat 160), (58, Int.ofNat 80),
    (60, Int.negSucc 79), (61, Int.ofNat 80), (86, Int.negSucc 79), (87, Int.ofNat 80), (89,
    Int.negSucc 79), (90, Int.ofNat 80), (115, Int.negSucc 79), (468, Int.negSucc 79), (558,
    Int.negSucc 79), (588, Int.negSucc 79), (648, Int.negSucc 79), (812, Int.negSucc 79), (813,
    Int.ofNat 160), (814, Int.negSucc 79), (815, Int.negSucc 79), (0, Int.ofNat 72), (2, Int.ofNat
    72), (3, Int.negSucc 71), (28, Int.negSucc 71), (29, Int.negSucc 215), (31, Int.negSucc 215),
    (32, Int.ofNat 216), (57, Int.ofNat 216), (58, Int.ofNat 72), (60, Int.ofNat 72), (61,
    Int.negSucc 71), (86, Int.negSucc 71), (87, Int.ofNat 216), (89, Int.ofNat 216), (90,
    Int.negSucc 215), (115, Int.negSucc 215), (132, Int.ofNat 72), (498, Int.negSucc 71), (558,
    Int.negSucc 71), (618, Int.negSucc 71), (648, Int.negSucc 71), (738, Int.negSucc 71), (768,
    Int.ofNat 72), (812, Int.negSucc 71), (813, Int.ofNat 216), (814, Int.negSucc 71), (815,
    Int.negSucc 215), (29, Int.negSucc 119), (31, Int.negSucc 119), (32, Int.ofNat 120), (57,
    Int.ofNat 120), (58, Int.ofNat 240), (60, Int.ofNat 240), (61, Int.negSucc 239), (86,
    Int.negSucc 239), (498, Int.negSucc 119), (648, Int.negSucc 119), (738, Int.ofNat 120), (813,
    Int.ofNat 120), (814, Int.negSucc 239), (0, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.ofNat
    48), (28, Int.negSucc 47), (29, Int.negSucc 23), (31, Int.ofNat 24), (32, Int.negSucc 23),
    (57, Int.ofNat 24), (558, Int.negSucc 23), (588, Int.negSucc 23), (708, Int.ofNat 24), (812,
    Int.negSucc 47), (813, Int.ofNat 24), (0, Int.ofNat 64), (2, Int.ofNat 64), (3, Int.negSucc
    63), (28, Int.negSucc 63), (29, Int.negSucc 31), (31, Int.negSucc 31), (32, Int.ofNat 32),
    (57, Int.ofNat 32), (558, Int.negSucc 31), (618, Int.negSucc 31), (738, Int.ofNat 32), (812,
    Int.negSucc 63), (813, Int.ofNat 32), (798, Int.negSucc 191), (813, Int.ofNat 192), (840,
    Int.negSucc 191), (768, Int.ofNat 112), (798, Int.ofNat 112), (812, Int.negSucc 111), (814,
    Int.negSucc 111), (815, Int.negSucc 111), (840, Int.ofNat 224), (708, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.ofNat 16), (813, Int.ofNat 16), (814, Int.negSucc 15), (815,
    Int.ofNat 16), (840, Int.negSucc 31), (588, Int.ofNat 48), (798, Int.ofNat 48), (812,
    Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48), (815, Int.negSucc 47), (840,
    Int.ofNat 96), (618, Int.ofNat 48), (798, Int.ofNat 48), (812, Int.ofNat 48), (813,
    Int.negSucc 95), (814, Int.negSucc 47), (815, Int.ofNat 48), (840, Int.ofNat 96), (648,
    Int.ofNat 48), (798, Int.ofNat 48), (812, Int.negSucc 47), (813, Int.negSucc 95), (814,
    Int.ofNat 48), (815, Int.ofNat 48), (840, Int.ofNat 96), (468, Int.ofNat 80), (798,
    Int.negSucc 79), (815, Int.ofNat 160), (840, Int.negSucc 159), (498, Int.ofNat 144), (798,
    Int.negSucc 143), (814, Int.ofNat 288), (840, Int.negSucc 287), (558, Int.ofNat 80), (798,
    Int.negSucc 79), (812, Int.ofNat 160), (840, Int.negSucc 159), (29, Int.negSucc 23), (31,
    Int.negSucc 23), (32, Int.ofNat 24), (57, Int.ofNat 24), (87, Int.ofNat 48), (89, Int.ofNat
    48), (90, Int.negSucc 47), (115, Int.negSucc 47), (738, Int.negSucc 23), (768, Int.ofNat 24),
    (798, Int.ofNat 24), (813, Int.negSucc 23), (840, Int.ofNat 48), (29, Int.negSucc 95), (31,
    Int.ofNat 96), (32, Int.negSucc 95), (57, Int.ofNat 96), (58, Int.ofNat 192), (60, Int.negSucc
    191), (61, Int.ofNat 192), (86, Int.negSucc 191), (708, Int.negSucc 95), (768, Int.ofNat 96),
    (798, Int.ofNat 96), (813, Int.negSucc 95), (840, Int.ofNat 192), (0, Int.negSucc 47), (2,
    Int.ofNat 48), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.ofNat 24), (31, Int.negSucc
    23), (32, Int.negSucc 23), (57, Int.ofNat 24), (678, Int.negSucc 23), (768, Int.ofNat 24),
    (798, Int.ofNat 24), (813, Int.negSucc 23), (840, Int.ofNat 48), (798, Int.ofNat 128), (812,
    Int.negSucc 127), (813, Int.ofNat 128), (814, Int.negSucc 127), (815, Int.negSucc 127), (840,
    Int.ofNat 128), (798, Int.negSucc 15), (812, Int.ofNat 16), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 15), (798, Int.negSucc 63), (812, Int.ofNat 64), (814,
    Int.negSucc 63), (815, Int.ofNat 64), (840, Int.negSucc 63), (798, Int.negSucc 15), (812,
    Int.negSucc 15), (814, Int.ofNat 16), (815, Int.ofNat 16), (840, Int.negSucc 15)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 2, source := [(14, Int.negSucc 3), (43, Int.ofNat 10), (72, Int.negSucc
    9), (101, Int.negSucc 3), (157, Int.ofNat 2), (326, Int.ofNat 1), (381, Int.negSucc 0), (537,
    Int.negSucc 3)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 16), (32, Int.negSucc 31), (88, Int.negSucc 31), (90, Int.ofNat 64),
    (132, Int.negSucc 15), (468, Int.negSucc 15), (1, Int.negSucc 15), (3, Int.ofNat 32), (29,
    Int.negSucc 15), (30, Int.ofNat 96), (31, Int.negSucc 15), (32, Int.negSucc 143), (59,
    Int.negSucc 15), (61, Int.ofNat 32), (87, Int.ofNat 32), (88, Int.negSucc 143), (89, Int.ofNat
    32), (90, Int.ofNat 192), (132, Int.negSucc 47), (192, Int.negSucc 15), (252, Int.negSucc 15),
    (468, Int.negSucc 47), (528, Int.negSucc 15), (588, Int.negSucc 15), (0, Int.negSucc 135), (1,
    Int.ofNat 340), (2, Int.negSucc 135), (3, Int.negSucc 271), (29, Int.ofNat 340), (30,
    Int.negSucc 815), (31, Int.ofNat 340), (32, Int.ofNat 612), (58, Int.negSucc 135), (59,
    Int.ofNat 340), (60, Int.negSucc 135), (61, Int.negSucc 271), (87, Int.negSucc 271), (88,
    Int.ofNat 612), (89, Int.negSucc 271), (90, Int.negSucc 407), (132, Int.ofNat 68), (192,
    Int.ofNat 204), (252, Int.ofNat 68), (468, Int.ofNat 68), (528, Int.ofNat 204), (588,
    Int.ofNat 68), (0, Int.ofNat 96), (1, Int.negSucc 287), (2, Int.ofNat 192), (3, Int.ofNat
    192), (29, Int.negSucc 287), (30, Int.ofNat 768), (31, Int.negSucc 479), (32, Int.negSucc
    479), (58, Int.ofNat 192), (59, Int.negSucc 479), (60, Int.ofNat 288), (61, Int.ofNat 288),
    (87, Int.ofNat 192), (88, Int.negSucc 479), (89, Int.ofNat 288), (90, Int.ofNat 288), (132,
    Int.negSucc 47), (162, Int.negSucc 47), (192, Int.negSucc 191), (252, Int.negSucc 47), (282,
    Int.negSucc 47), (468, Int.negSucc 47), (498, Int.negSucc 47), (528, Int.negSucc 191), (588,
    Int.negSucc 47), (618, Int.negSucc 47), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat
    16), (30, Int.negSucc 95), (31, Int.ofNat 144), (32, Int.ofNat 16), (58, Int.negSucc 31), (59,
    Int.ofNat 144), (60, Int.negSucc 191), (61, Int.negSucc 31), (88, Int.ofNat 16), (89,
    Int.negSucc 31), (162, Int.ofNat 48), (192, Int.ofNat 16), (282, Int.ofNat 16), (498,
    Int.ofNat 48), (528, Int.ofNat 16), (618, Int.ofNat 16), (0, Int.ofNat 72), (1, Int.negSucc
    119), (2, Int.ofNat 48), (3, Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat 192), (31,
    Int.negSucc 71), (32, Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71), (60,
    Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89, Int.ofNat
    48), (90, Int.ofNat 72), (132, Int.negSucc 11), (192, Int.negSucc 47), (222, Int.negSucc 11),
    (252, Int.negSucc 11), (312, Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 47),
    (558, Int.negSucc 11), (588, Int.negSucc 11), (648, Int.negSucc 11), (1, Int.ofNat 32), (2,
    Int.negSucc 63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat
    32), (58, Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63),
    (88, Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252,
    Int.ofNat 8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc
    7), (498, Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648,
    Int.ofNat 8), (678, Int.negSucc 7), (738, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat
    36), (2, Int.negSucc 7), (3, Int.negSucc 7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31,
    Int.ofNat 4), (32, Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7),
    (88, Int.ofNat 4), (192, Int.ofNat 4), (222, Int.ofNat 12), (312, Int.ofNat 4), (528,
    Int.ofNat 4), (558, Int.ofNat 12), (648, Int.ofNat 4), (528, Int.ofNat 208), (588, Int.ofNat
    208), (618, Int.ofNat 208), (648, Int.ofNat 208), (678, Int.negSucc 207), (708, Int.negSucc
    207), (738, Int.negSucc 207), (768, Int.ofNat 208), (30, Int.ofNat 16), (57, Int.negSucc 15),
    (88, Int.negSucc 31), (115, Int.ofNat 32), (528, Int.negSucc 15), (588, Int.negSucc 15), (738,
    Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (1,
    Int.negSucc 63), (28, Int.ofNat 64), (30, Int.ofNat 128), (57, Int.negSucc 127), (59,
    Int.negSucc 63), (86, Int.ofNat 64), (88, Int.negSucc 63), (115, Int.ofNat 64), (528,
    Int.negSucc 63), (768, Int.negSucc 63), (798, Int.ofNat 64), (812, Int.ofNat 64), (813,
    Int.negSucc 127), (814, Int.ofNat 64), (815, Int.ofNat 64), (30, Int.ofNat 80), (57,
    Int.negSucc 79), (59, Int.negSucc 159), (86, Int.ofNat 160), (528, Int.negSucc 79), (618,
    Int.negSucc 79), (708, Int.ofNat 80), (768, Int.negSucc 79), (813, Int.negSucc 79), (814,
    Int.ofNat 160), (1, Int.negSucc 31), (28, Int.ofNat 32), (30, Int.ofNat 16), (57, Int.negSucc
    15), (528, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (768, Int.negSucc 15),
    (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 80), (30, Int.negSucc 79), (31,
    Int.ofNat 80), (32, Int.ofNat 80), (57, Int.negSucc 79), (87, Int.negSucc 159), (88, Int.ofNat
    160), (89, Int.negSucc 159), (90, Int.negSucc 159), (115, Int.ofNat 160), (468, Int.ofNat 80),
    (738, Int.ofNat 80), (768, Int.negSucc 79), (813, Int.negSucc 79), (815, Int.ofNat 160), (0,
    Int.negSucc 79), (1, Int.ofNat 80), (2, Int.negSucc 79), (3, Int.negSucc 79), (28, Int.ofNat
    80), (29, Int.ofNat 160), (30, Int.negSucc 159), (31, Int.ofNat 160), (32, Int.ofNat 160),
    (57, Int.negSucc 159), (58, Int.negSucc 79), (59, Int.ofNat 80), (60, Int.negSucc 79), (61,
    Int.negSucc 79), (86, Int.ofNat 80), (87, Int.negSucc 79), (88, Int.ofNat 80), (89,
    Int.negSucc 79), (90, Int.negSucc 79), (115, Int.ofNat 80), (468, Int.ofNat 80), (498,
    Int.ofNat 80), (558, Int.ofNat 80), (678, Int.ofNat 80), (708, Int.ofNat 80), (738, Int.ofNat
    80), (768, Int.negSucc 79), (812, Int.ofNat 80), (813, Int.negSucc 159), (814, Int.ofNat 80),
    (815, Int.ofNat 80), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32,
    Int.ofNat 96), (57, Int.negSucc 95), (58, Int.negSucc 191), (59, Int.ofNat 192), (60,
    Int.negSucc 191), (61, Int.negSucc 191), (86, Int.ofNat 192), (498, Int.ofNat 96), (708,
    Int.ofNat 96), (768, Int.negSucc 95), (813, Int.negSucc 95), (814, Int.ofNat 192), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 24), (30, Int.negSucc 23), (31, Int.ofNat 24), (32, Int.ofNat 24), (57,
    Int.negSucc 23), (558, Int.ofNat 24), (678, Int.ofNat 24), (768, Int.negSucc 23), (812,
    Int.ofNat 48), (813, Int.negSucc 23), (29, Int.ofNat 24), (31, Int.negSucc 23), (32,
    Int.negSucc 23), (57, Int.ofNat 24), (87, Int.negSucc 47), (89, Int.ofNat 48), (90, Int.ofNat
    48), (115, Int.negSucc 47), (468, Int.negSucc 23), (618, Int.negSucc 23), (678, Int.ofNat 24),
    (813, Int.ofNat 24), (815, Int.negSucc 47), (0, Int.negSucc 55), (2, Int.ofNat 56), (3,
    Int.ofNat 56), (28, Int.negSucc 55), (29, Int.ofNat 112), (31, Int.negSucc 111), (32,
    Int.negSucc 111), (57, Int.ofNat 112), (58, Int.negSucc 55), (60, Int.ofNat 56), (61,
    Int.ofNat 56), (86, Int.negSucc 55), (87, Int.negSucc 55), (89, Int.ofNat 56), (90, Int.ofNat
    56), (115, Int.negSucc 55), (468, Int.negSucc 55), (498, Int.negSucc 55), (588, Int.negSucc
    55), (618, Int.negSucc 55), (812, Int.negSucc 55), (813, Int.ofNat 112), (814, Int.negSucc
    55), (815, Int.negSucc 55), (29, Int.ofNat 88), (31, Int.negSucc 87), (32, Int.negSucc 87),
    (57, Int.ofNat 88), (58, Int.negSucc 175), (60, Int.ofNat 176), (61, Int.ofNat 176), (86,
    Int.negSucc 175), (498, Int.negSucc 87), (588, Int.negSucc 87), (678, Int.ofNat 88), (813,
    Int.ofNat 88), (814, Int.negSucc 175), (29, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.negSucc 31), (90, Int.ofNat
    32), (115, Int.negSucc 31), (468, Int.negSucc 15), (648, Int.negSucc 15), (708, Int.ofNat 16),
    (813, Int.ofNat 16), (815, Int.negSucc 31), (0, Int.ofNat 64), (2, Int.negSucc 63), (3,
    Int.ofNat 64), (28, Int.negSucc 63), (29, Int.negSucc 127), (31, Int.ofNat 128), (32,
    Int.negSucc 127), (57, Int.ofNat 128), (58, Int.ofNat 64), (60, Int.negSucc 63), (61,
    Int.ofNat 64), (86, Int.negSucc 63), (87, Int.ofNat 64), (89, Int.negSucc 63), (90, Int.ofNat
    64), (115, Int.negSucc 63), (468, Int.negSucc 63), (558, Int.negSucc 63), (588, Int.negSucc
    63), (648, Int.negSucc 63), (812, Int.negSucc 63), (813, Int.ofNat 128), (814, Int.negSucc
    63), (815, Int.negSucc 63), (0, Int.ofNat 56), (2, Int.ofNat 56), (3, Int.negSucc 55), (28,
    Int.negSucc 55), (29, Int.negSucc 167), (31, Int.negSucc 167), (32, Int.ofNat 168), (57,
    Int.ofNat 168), (58, Int.ofNat 56), (60, Int.ofNat 56), (61, Int.negSucc 55), (86, Int.negSucc
    55), (87, Int.ofNat 168), (89, Int.ofNat 168), (90, Int.negSucc 167), (115, Int.negSucc 167),
    (132, Int.ofNat 56), (498, Int.negSucc 55), (558, Int.negSucc 55), (618, Int.negSucc 55),
    (648, Int.negSucc 55), (738, Int.negSucc 55), (768, Int.ofNat 56), (812, Int.negSucc 55),
    (813, Int.ofNat 168), (814, Int.negSucc 55), (815, Int.negSucc 167), (29, Int.negSucc 87),
    (31, Int.negSucc 87), (32, Int.ofNat 88), (57, Int.ofNat 88), (58, Int.ofNat 176), (60,
    Int.ofNat 176), (61, Int.negSucc 175), (86, Int.negSucc 175), (498, Int.negSucc 87), (648,
    Int.negSucc 87), (738, Int.ofNat 88), (813, Int.ofNat 88), (814, Int.negSucc 175), (0,
    Int.ofNat 32), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc
    15), (31, Int.ofNat 16), (32, Int.negSucc 15), (57, Int.ofNat 16), (558, Int.negSucc 15),
    (588, Int.negSucc 15), (708, Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (0,
    Int.ofNat 48), (2, Int.ofNat 48), (3, Int.negSucc 47), (28, Int.negSucc 47), (29, Int.negSucc
    23), (31, Int.negSucc 23), (32, Int.ofNat 24), (57, Int.ofNat 24), (558, Int.negSucc 23),
    (618, Int.negSucc 23), (738, Int.ofNat 24), (812, Int.negSucc 47), (813, Int.ofNat 24), (798,
    Int.negSucc 143), (813, Int.ofNat 144), (840, Int.negSucc 143), (768, Int.ofNat 96), (798,
    Int.ofNat 96), (812, Int.negSucc 95), (814, Int.negSucc 95), (815, Int.negSucc 95), (840,
    Int.ofNat 192), (708, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (813,
    Int.ofNat 16), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.negSucc 31), (588,
    Int.ofNat 32), (798, Int.ofNat 32), (812, Int.ofNat 32), (813, Int.negSucc 63), (814,
    Int.ofNat 32), (815, Int.negSucc 31), (840, Int.ofNat 64), (618, Int.ofNat 32), (798,
    Int.ofNat 32), (812, Int.ofNat 32), (813, Int.negSucc 63), (814, Int.negSucc 31), (815,
    Int.ofNat 32), (840, Int.ofNat 64), (648, Int.ofNat 32), (798, Int.ofNat 32), (812,
    Int.negSucc 31), (813, Int.negSucc 63), (814, Int.ofNat 32), (815, Int.ofNat 32), (840,
    Int.ofNat 64), (468, Int.ofNat 56), (798, Int.negSucc 55), (815, Int.ofNat 112), (840,
    Int.negSucc 111), (498, Int.ofNat 96), (798, Int.negSucc 95), (814, Int.ofNat 192), (840,
    Int.negSucc 191), (558, Int.ofNat 56), (798, Int.negSucc 55), (812, Int.ofNat 112), (840,
    Int.negSucc 111), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57,
    Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat 32), (90, Int.negSucc 31), (115, Int.negSucc
    31), (738, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16), (813, Int.negSucc 15),
    (840, Int.ofNat 32), (29, Int.negSucc 63), (31, Int.ofNat 64), (32, Int.negSucc 63), (57,
    Int.ofNat 64), (58, Int.ofNat 128), (60, Int.negSucc 127), (61, Int.ofNat 128), (86,
    Int.negSucc 127), (708, Int.negSucc 63), (768, Int.ofNat 64), (798, Int.ofNat 64), (813,
    Int.negSucc 63), (840, Int.ofNat 128), (0, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat
    32), (28, Int.negSucc 31), (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15),
    (57, Int.ofNat 16), (678, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16), (813,
    Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 64), (812, Int.negSucc 63), (813,
    Int.ofNat 64), (814, Int.negSucc 63), (815, Int.negSucc 63), (840, Int.ofNat 64), (798,
    Int.negSucc 7), (812, Int.ofNat 8), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.negSucc 7), (798, Int.negSucc 31), (812, Int.ofNat 32), (814, Int.negSucc 31), (815,
    Int.ofNat 32), (840, Int.negSucc 31), (798, Int.negSucc 7), (812, Int.negSucc 7), (814,
    Int.ofNat 8), (815, Int.ofNat 8), (840, Int.negSucc 7)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 2, source := [(14, Int.ofNat 1), (43, Int.negSucc 3), (72, Int.ofNat 1),
    (101, Int.ofNat 5), (129, Int.negSucc 2), (157, Int.negSucc 0), (214, Int.ofNat 1), (407,
    Int.negSucc 0), (434, Int.ofNat 1), (537, Int.ofNat 1), (826, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 23), (32, Int.ofNat 48), (88, Int.ofNat 48), (90, Int.negSucc 95),
    (132, Int.ofNat 24), (468, Int.ofNat 24), (1, Int.negSucc 11), (3, Int.ofNat 24), (29,
    Int.negSucc 11), (30, Int.ofNat 72), (31, Int.negSucc 11), (32, Int.negSucc 107), (59,
    Int.negSucc 11), (61, Int.ofNat 24), (87, Int.ofNat 24), (88, Int.negSucc 107), (89, Int.ofNat
    24), (90, Int.ofNat 144), (132, Int.negSucc 35), (192, Int.negSucc 11), (252, Int.negSucc 11),
    (468, Int.negSucc 35), (528, Int.negSucc 11), (588, Int.negSucc 11), (0, Int.negSucc 71), (1,
    Int.ofNat 180), (2, Int.negSucc 71), (3, Int.negSucc 143), (29, Int.ofNat 180), (30,
    Int.negSucc 431), (31, Int.ofNat 180), (32, Int.ofNat 324), (58, Int.negSucc 71), (59,
    Int.ofNat 180), (60, Int.negSucc 71), (61, Int.negSucc 143), (87, Int.negSucc 143), (88,
    Int.ofNat 324), (89, Int.negSucc 143), (90, Int.negSucc 215), (132, Int.ofNat 36), (192,
    Int.ofNat 108), (252, Int.ofNat 36), (468, Int.ofNat 36), (528, Int.ofNat 108), (588,
    Int.ofNat 36), (0, Int.ofNat 48), (1, Int.negSucc 143), (2, Int.ofNat 96), (3, Int.ofNat 96),
    (29, Int.negSucc 143), (30, Int.ofNat 384), (31, Int.negSucc 239), (32, Int.negSucc 239), (58,
    Int.ofNat 96), (59, Int.negSucc 239), (60, Int.ofNat 144), (61, Int.ofNat 144), (87, Int.ofNat
    96), (88, Int.negSucc 239), (89, Int.ofNat 144), (90, Int.ofNat 144), (132, Int.negSucc 23),
    (162, Int.negSucc 23), (192, Int.negSucc 95), (252, Int.negSucc 23), (282, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (528, Int.negSucc 95), (588, Int.negSucc 23),
    (618, Int.negSucc 23), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30,
    Int.negSucc 15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat
    8), (252, Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588,
    Int.ofNat 8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252,
    Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372,
    Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (528, Int.negSucc 95), (588, Int.negSucc 95),
    (618, Int.negSucc 95), (648, Int.negSucc 95), (678, Int.ofNat 96), (708, Int.ofNat 96), (738,
    Int.ofNat 96), (768, Int.negSucc 95), (30, Int.negSucc 55), (57, Int.ofNat 56), (88, Int.ofNat
    112), (115, Int.negSucc 111), (528, Int.ofNat 56), (588, Int.ofNat 56), (738, Int.negSucc 55),
    (768, Int.ofNat 56), (813, Int.ofNat 56), (815, Int.negSucc 111), (1, Int.ofNat 16), (28,
    Int.negSucc 15), (30, Int.negSucc 31), (57, Int.ofNat 32), (59, Int.ofNat 16), (86,
    Int.negSucc 15), (88, Int.ofNat 16), (115, Int.negSucc 15), (528, Int.ofNat 16), (768,
    Int.ofNat 16), (798, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.negSucc 15), (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat
    16), (86, Int.negSucc 15), (528, Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768,
    Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc
    15), (30, Int.negSucc 7), (57, Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29,
    Int.negSucc 71), (30, Int.ofNat 72), (31, Int.negSucc 71), (32, Int.negSucc 71), (57,
    Int.ofNat 72), (87, Int.ofNat 144), (88, Int.negSucc 143), (89, Int.ofNat 144), (90, Int.ofNat
    144), (115, Int.negSucc 143), (468, Int.negSucc 71), (738, Int.negSucc 71), (768, Int.ofNat
    72), (813, Int.ofNat 72), (815, Int.negSucc 143), (0, Int.ofNat 16), (1, Int.negSucc 15), (2,
    Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 31), (30, Int.ofNat
    32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (59,
    Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat
    16), (88, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15),
    (468, Int.negSucc 15), (498, Int.negSucc 15), (558, Int.negSucc 15), (678, Int.negSucc 15),
    (708, Int.negSucc 15), (738, Int.negSucc 15), (768, Int.ofNat 16), (812, Int.negSucc 15),
    (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (29, Int.negSucc 7), (30,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16),
    (59, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498,
    Int.negSucc 7), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (0, Int.ofNat 16), (1, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16),
    (28, Int.negSucc 15), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 55), (31, Int.ofNat 56), (32,
    Int.ofNat 56), (57, Int.negSucc 55), (87, Int.ofNat 112), (89, Int.negSucc 111), (90,
    Int.negSucc 111), (115, Int.ofNat 112), (468, Int.ofNat 56), (618, Int.ofNat 56), (678,
    Int.negSucc 55), (813, Int.negSucc 55), (815, Int.ofNat 112), (0, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.negSucc 31), (31, Int.ofNat
    32), (32, Int.ofNat 32), (57, Int.negSucc 31), (58, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.negSucc 15), (86, Int.ofNat 16), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.negSucc 15), (115, Int.ofNat 16), (468, Int.ofNat 16), (498, Int.ofNat 16), (588,
    Int.ofNat 16), (618, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8),
    (57, Int.negSucc 7), (58, Int.ofNat 16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (498, Int.ofNat 8), (588, Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc
    7), (814, Int.ofNat 16), (29, Int.ofNat 56), (31, Int.negSucc 55), (32, Int.ofNat 56), (57,
    Int.negSucc 55), (87, Int.negSucc 111), (89, Int.ofNat 112), (90, Int.negSucc 111), (115,
    Int.ofNat 112), (468, Int.ofNat 56), (648, Int.ofNat 56), (708, Int.negSucc 55), (813,
    Int.negSucc 55), (815, Int.ofNat 112), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc
    15), (28, Int.ofNat 16), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.ofNat 32), (57,
    Int.negSucc 31), (58, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.ofNat
    16), (468, Int.ofNat 16), (558, Int.ofNat 16), (588, Int.ofNat 16), (648, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (0,
    Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat
    48), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.negSucc 47), (58, Int.negSucc 15),
    (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (87, Int.negSucc 47), (89,
    Int.negSucc 47), (90, Int.ofNat 48), (115, Int.ofNat 48), (132, Int.negSucc 15), (498,
    Int.ofNat 16), (558, Int.ofNat 16), (618, Int.ofNat 16), (648, Int.ofNat 16), (738, Int.ofNat
    16), (768, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.negSucc 47), (814, Int.ofNat 16),
    (815, Int.ofNat 48), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
    Int.negSucc 7), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat
    16), (498, Int.ofNat 8), (648, Int.ofNat 8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.ofNat
    16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.negSucc 7), (558,
    Int.ofNat 8), (588, Int.ofNat 8), (708, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc
    7), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29,
    Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8),
    (618, Int.ofNat 8), (738, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798,
    Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat 8), (768, Int.negSucc 39), (798,
    Int.negSucc 39), (812, Int.ofNat 40), (814, Int.ofNat 40), (815, Int.ofNat 40), (840,
    Int.negSucc 79), (738, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813,
    Int.negSucc 15), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (588,
    Int.negSucc 7), (798, Int.negSucc 7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814,
    Int.negSucc 7), (815, Int.ofNat 8), (840, Int.negSucc 15), (618, Int.negSucc 7), (798,
    Int.negSucc 7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814, Int.ofNat 8), (815,
    Int.negSucc 7), (840, Int.negSucc 15), (648, Int.negSucc 7), (798, Int.negSucc 7), (812,
    Int.ofNat 8), (813, Int.ofNat 16), (814, Int.negSucc 7), (815, Int.negSucc 7), (840,
    Int.negSucc 15), (468, Int.negSucc 47), (798, Int.ofNat 48), (815, Int.negSucc 95), (840,
    Int.ofNat 96), (498, Int.negSucc 15), (798, Int.ofNat 16), (814, Int.negSucc 31), (840,
    Int.ofNat 32), (558, Int.negSucc 15), (798, Int.ofNat 16), (812, Int.negSucc 31), (840,
    Int.ofNat 32), (29, Int.ofNat 32), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.negSucc
    31), (87, Int.negSucc 63), (89, Int.negSucc 63), (90, Int.ofNat 64), (115, Int.ofNat 64),
    (738, Int.ofNat 32), (768, Int.negSucc 31), (798, Int.negSucc 31), (813, Int.ofNat 32), (840,
    Int.negSucc 63), (798, Int.negSucc 31), (812, Int.ofNat 32), (813, Int.negSucc 31), (814,
    Int.ofNat 32), (815, Int.ofNat 32), (840, Int.negSucc 31), (798, Int.ofNat 24), (812,
    Int.negSucc 23), (814, Int.negSucc 23), (815, Int.ofNat 24), (840, Int.ofNat 24), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (814, Int.ofNat 8), (815, Int.negSucc 7), (840, Int.ofNat
    8), (798, Int.ofNat 8), (812, Int.ofNat 8), (814, Int.negSucc 7), (815, Int.negSucc 7), (840,
    Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 2, source := [(15, Int.negSucc 3), (44, Int.ofNat 6), (73, Int.negSucc
    1), (102, Int.negSucc 3), (188, Int.ofNat 4), (245, Int.ofNat 1), (301, Int.ofNat 1), (329,
    Int.ofNat 1), (385, Int.ofNat 1), (412, Int.ofNat 4), (435, Int.negSucc 3), (436, Int.ofNat
    6), (437, Int.negSucc 1), (438, Int.negSucc 3)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 64), (32, Int.negSucc 127), (88, Int.negSucc 127), (90, Int.ofNat
    256), (132, Int.negSucc 63), (468, Int.negSucc 63), (1, Int.ofNat 24), (3, Int.negSucc 47),
    (29, Int.ofNat 24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59,
    Int.ofNat 24), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89,
    Int.negSucc 47), (90, Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252,
    Int.ofNat 24), (468, Int.ofNat 72), (528, Int.ofNat 24), (588, Int.ofNat 24), (0, Int.ofNat
    8), (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16), (29, Int.negSucc 19), (30,
    Int.ofNat 48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58, Int.ofNat 8), (59, Int.negSucc
    19), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16), (88, Int.negSucc 35), (89,
    Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192, Int.negSucc 11), (252,
    Int.negSucc 3), (468, Int.negSucc 3), (528, Int.negSucc 11), (588, Int.negSucc 3), (1,
    Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc 15), (32, Int.ofNat
    16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252, Int.ofNat 8), (312,
    Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat
    8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7), (282, Int.negSucc 7),
    (312, Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402, Int.ofNat 8), (432,
    Int.negSucc 7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618, Int.negSucc 7), (648,
    Int.negSucc 7), (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc
    7), (0, Int.ofNat 24), (1, Int.negSucc 39), (2, Int.ofNat 16), (3, Int.ofNat 24), (29,
    Int.negSucc 39), (30, Int.ofNat 64), (31, Int.negSucc 23), (32, Int.negSucc 39), (58,
    Int.ofNat 16), (59, Int.negSucc 23), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat
    24), (88, Int.negSucc 39), (89, Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192,
    Int.negSucc 15), (222, Int.negSucc 3), (252, Int.negSucc 3), (312, Int.negSucc 3), (468,
    Int.negSucc 3), (528, Int.negSucc 15), (558, Int.negSucc 3), (588, Int.negSucc 3), (648,
    Int.negSucc 3), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58, Int.negSucc 31), (59, Int.ofNat 56), (60,
    Int.negSucc 31), (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc 31), (162,
    Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat 4), (282, Int.ofNat 16), (312, Int.ofNat
    4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498, Int.ofNat 8), (528, Int.ofNat 16), (588,
    Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat 4), (678, Int.negSucc 3), (738, Int.negSucc
    3), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48), (29,
    Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
    Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23),
    (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
    Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
    Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc 7), (3, Int.negSucc 7),
    (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32, Int.ofNat 4), (58,
    Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4), (192, Int.ofNat 4),
    (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558, Int.ofNat 12), (648,
    Int.ofNat 4), (528, Int.ofNat 56), (588, Int.ofNat 56), (618, Int.ofNat 56), (648, Int.ofNat
    56), (678, Int.negSucc 55), (708, Int.negSucc 55), (738, Int.negSucc 55), (768, Int.ofNat 56),
    (30, Int.ofNat 16), (57, Int.negSucc 15), (88, Int.negSucc 31), (115, Int.ofNat 32), (528,
    Int.negSucc 15), (588, Int.negSucc 15), (738, Int.ofNat 16), (768, Int.negSucc 15), (813,
    Int.negSucc 15), (815, Int.ofNat 32), (30, Int.ofNat 8), (57, Int.negSucc 7), (59, Int.negSucc
    15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618, Int.negSucc 7), (708, Int.ofNat 8), (768,
    Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (1, Int.negSucc 31), (28, Int.ofNat
    32), (30, Int.ofNat 16), (57, Int.negSucc 15), (528, Int.negSucc 15), (648, Int.negSucc 15),
    (678, Int.ofNat 16), (768, Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (29,
    Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc
    15), (87, Int.negSucc 31), (88, Int.ofNat 32), (89, Int.negSucc 31), (90, Int.negSucc 31),
    (115, Int.ofNat 32), (468, Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (813,
    Int.negSucc 15), (815, Int.ofNat 32), (0, Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc
    47), (3, Int.negSucc 47), (28, Int.ofNat 48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31,
    Int.ofNat 96), (32, Int.ofNat 96), (57, Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat
    48), (60, Int.negSucc 47), (61, Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47),
    (88, Int.ofNat 48), (89, Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468,
    Int.ofNat 48), (498, Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat
    48), (738, Int.ofNat 48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95),
    (814, Int.ofNat 48), (815, Int.ofNat 48), (29, Int.negSucc 15), (30, Int.ofNat 16), (31,
    Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 32), (59,
    Int.negSucc 31), (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc 31), (498,
    Int.negSucc 15), (708, Int.negSucc 15), (768, Int.ofNat 16), (813, Int.ofNat 16), (814,
    Int.negSucc 31), (0, Int.ofNat 16), (1, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16),
    (28, Int.negSucc 15), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32,
    Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.negSucc 3), (32,
    Int.negSucc 3), (57, Int.ofNat 4), (87, Int.negSucc 7), (89, Int.ofNat 8), (90, Int.ofNat 8),
    (115, Int.negSucc 7), (468, Int.negSucc 3), (618, Int.negSucc 3), (678, Int.ofNat 4), (813,
    Int.ofNat 4), (815, Int.negSucc 7), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24),
    (28, Int.negSucc 23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57,
    Int.ofNat 48), (58, Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc
    23), (87, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23),
    (812, Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.negSucc 3), (31, Int.ofNat 4), (32, Int.ofNat 4), (57, Int.negSucc 3), (58, Int.ofNat 8),
    (60, Int.negSucc 7), (61, Int.negSucc 7), (86, Int.ofNat 8), (498, Int.ofNat 4), (588,
    Int.ofNat 4), (678, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat 8), (29, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16), (89,
    Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (648,
    Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat
    16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (60, Int.negSucc
    15), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15), (558, Int.negSucc 15), (588,
    Int.negSucc 15), (648, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.negSucc 15), (0, Int.ofNat 24), (2, Int.ofNat 24), (3, Int.negSucc
    23), (28, Int.negSucc 23), (29, Int.negSucc 71), (31, Int.negSucc 71), (32, Int.ofNat 72),
    (57, Int.ofNat 72), (58, Int.ofNat 24), (60, Int.ofNat 24), (61, Int.negSucc 23), (86,
    Int.negSucc 23), (87, Int.ofNat 72), (89, Int.ofNat 72), (90, Int.negSucc 71), (115,
    Int.negSucc 71), (132, Int.ofNat 24), (498, Int.negSucc 23), (558, Int.negSucc 23), (618,
    Int.negSucc 23), (648, Int.negSucc 23), (738, Int.negSucc 23), (768, Int.ofNat 24), (812,
    Int.negSucc 23), (813, Int.ofNat 72), (814, Int.negSucc 23), (815, Int.negSucc 71), (29,
    Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc 3), (58, Int.negSucc
    7), (60, Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat 8), (498, Int.ofNat 4), (648,
    Int.ofNat 4), (738, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat 8), (0, Int.ofNat
    16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31,
    Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc
    7), (708, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (0, Int.ofNat 8), (2,
    Int.ofNat 8), (3, Int.negSucc 7), (28, Int.negSucc 7), (29, Int.negSucc 3), (31, Int.negSucc
    3), (32, Int.ofNat 4), (57, Int.ofNat 4), (558, Int.negSucc 3), (618, Int.negSucc 3), (738,
    Int.ofNat 4), (812, Int.negSucc 7), (813, Int.ofNat 4), (798, Int.negSucc 15), (813, Int.ofNat
    16), (840, Int.negSucc 15), (768, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7),
    (814, Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 16), (588, Int.ofNat 8), (798,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.negSucc
    7), (840, Int.ofNat 16), (618, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813,
    Int.negSucc 15), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (648,
    Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813, Int.negSucc 15), (814, Int.ofNat
    8), (815, Int.ofNat 8), (840, Int.ofNat 16), (468, Int.ofNat 12), (798, Int.negSucc 11), (815,
    Int.ofNat 24), (840, Int.negSucc 23), (498, Int.ofNat 8), (798, Int.negSucc 7), (814,
    Int.ofNat 16), (840, Int.negSucc 15), (558, Int.ofNat 12), (798, Int.negSucc 11), (812,
    Int.ofNat 24), (840, Int.negSucc 23), (29, Int.negSucc 3), (31, Int.negSucc 3), (32, Int.ofNat
    4), (57, Int.ofNat 4), (87, Int.ofNat 8), (89, Int.ofNat 8), (90, Int.negSucc 7), (115,
    Int.negSucc 7), (738, Int.negSucc 3), (768, Int.ofNat 4), (798, Int.ofNat 4), (813,
    Int.negSucc 3), (840, Int.ofNat 8), (0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.ofNat 8),
    (28, Int.negSucc 7), (29, Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (57,
    Int.ofNat 4), (678, Int.negSucc 3), (768, Int.ofNat 4), (798, Int.ofNat 4), (813, Int.negSucc
    3), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 6, mode := 2, source := [(6, Int.negSucc 0), (35, Int.ofNat 2), (64, Int.negSucc 0),
    (93, Int.negSucc 0), (174, Int.negSucc 0), (175, Int.ofNat 2), (176, Int.negSucc 0), (177,
    Int.negSucc 0), (248, Int.negSucc 0), (278, Int.negSucc 0), (309, Int.ofNat 1), (461,
    Int.negSucc 0), (472, Int.negSucc 0), (502, Int.negSucc 0), (561, Int.ofNat 1), (769,
    Int.negSucc 0)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 64), (32, Int.negSucc 127), (88, Int.negSucc 127), (90, Int.ofNat
    256), (132, Int.negSucc 63), (468, Int.negSucc 63), (1, Int.ofNat 28), (3, Int.negSucc 55),
    (29, Int.ofNat 28), (30, Int.negSucc 167), (31, Int.ofNat 28), (32, Int.ofNat 252), (59,
    Int.ofNat 28), (61, Int.negSucc 55), (87, Int.negSucc 55), (88, Int.ofNat 252), (89,
    Int.negSucc 55), (90, Int.negSucc 335), (132, Int.ofNat 84), (192, Int.ofNat 28), (252,
    Int.ofNat 28), (468, Int.ofNat 84), (528, Int.ofNat 28), (588, Int.ofNat 28), (0, Int.ofNat
    72), (1, Int.negSucc 179), (2, Int.ofNat 72), (3, Int.ofNat 144), (29, Int.negSucc 179), (30,
    Int.ofNat 432), (31, Int.negSucc 179), (32, Int.negSucc 323), (58, Int.ofNat 72), (59,
    Int.negSucc 179), (60, Int.ofNat 72), (61, Int.ofNat 144), (87, Int.ofNat 144), (88,
    Int.negSucc 323), (89, Int.ofNat 144), (90, Int.ofNat 216), (132, Int.negSucc 35), (192,
    Int.negSucc 107), (252, Int.negSucc 35), (468, Int.negSucc 35), (528, Int.negSucc 107), (588,
    Int.negSucc 35), (0, Int.negSucc 47), (1, Int.ofNat 144), (2, Int.negSucc 95), (3, Int.negSucc
    95), (29, Int.ofNat 144), (30, Int.negSucc 383), (31, Int.ofNat 240), (32, Int.ofNat 240),
    (58, Int.negSucc 95), (59, Int.ofNat 240), (60, Int.negSucc 143), (61, Int.negSucc 143), (87,
    Int.negSucc 95), (88, Int.ofNat 240), (89, Int.negSucc 143), (90, Int.negSucc 143), (132,
    Int.ofNat 24), (162, Int.ofNat 24), (192, Int.ofNat 96), (252, Int.ofNat 24), (282, Int.ofNat
    24), (468, Int.ofNat 24), (498, Int.ofNat 24), (528, Int.ofNat 96), (588, Int.ofNat 24), (618,
    Int.ofNat 24), (1, Int.negSucc 15), (3, Int.ofNat 32), (29, Int.negSucc 15), (30, Int.ofNat
    16), (32, Int.negSucc 15), (87, Int.ofNat 32), (88, Int.negSucc 15), (192, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (372, Int.ofNat 8), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (648, Int.negSucc 7), (708, Int.ofNat 8), (192, Int.ofNat 8), (252, Int.ofNat
    8), (282, Int.ofNat 8), (312, Int.ofNat 8), (342, Int.negSucc 7), (372, Int.negSucc 7), (402,
    Int.negSucc 7), (432, Int.ofNat 8), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat
    8), (648, Int.ofNat 8), (678, Int.negSucc 7), (708, Int.negSucc 7), (738, Int.negSucc 7),
    (768, Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (1, Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat
    96), (31, Int.negSucc 111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162,
    Int.negSucc 15), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (738, Int.ofNat 8), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16),
    (3, Int.ofNat 48), (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32,
    Int.negSucc 111), (58, Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat
    48), (87, Int.ofNat 48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132,
    Int.negSucc 23), (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252,
    Int.negSucc 23), (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462,
    Int.ofNat 8), (468, Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768,
    Int.negSucc 7), (798, Int.ofNat 8), (528, Int.ofNat 40), (588, Int.ofNat 40), (618, Int.ofNat
    40), (648, Int.ofNat 40), (678, Int.negSucc 39), (708, Int.negSucc 39), (738, Int.negSucc 39),
    (768, Int.ofNat 40), (30, Int.ofNat 8), (57, Int.negSucc 7), (88, Int.negSucc 15), (115,
    Int.ofNat 16), (528, Int.negSucc 7), (588, Int.negSucc 7), (738, Int.ofNat 8), (768,
    Int.negSucc 7), (813, Int.negSucc 7), (815, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618, Int.negSucc 7),
    (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (1,
    Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc 7), (528, Int.negSucc
    7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (29, Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat
    16), (57, Int.negSucc 15), (87, Int.negSucc 31), (88, Int.ofNat 32), (89, Int.negSucc 31),
    (90, Int.negSucc 31), (115, Int.ofNat 32), (468, Int.ofNat 16), (738, Int.ofNat 16), (768,
    Int.negSucc 15), (813, Int.negSucc 15), (815, Int.ofNat 32), (0, Int.negSucc 7), (1, Int.ofNat
    8), (2, Int.negSucc 7), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.ofNat 16), (30,
    Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (58,
    Int.negSucc 7), (59, Int.ofNat 8), (60, Int.negSucc 7), (61, Int.negSucc 7), (86, Int.ofNat
    8), (87, Int.negSucc 7), (88, Int.ofNat 8), (89, Int.negSucc 7), (90, Int.negSucc 7), (115,
    Int.ofNat 8), (468, Int.ofNat 8), (498, Int.ofNat 8), (558, Int.ofNat 8), (678, Int.ofNat 8),
    (708, Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 8), (813,
    Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (29, Int.ofNat 8), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.negSucc 15), (59,
    Int.ofNat 16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat
    8), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0,
    Int.negSucc 15), (1, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat
    16), (29, Int.ofNat 8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57,
    Int.negSucc 7), (558, Int.ofNat 8), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat
    16), (813, Int.negSucc 7), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57,
    Int.ofNat 8), (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc
    15), (468, Int.negSucc 7), (618, Int.negSucc 7), (678, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.ofNat 8), (28, Int.negSucc 7),
    (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (58,
    Int.negSucc 7), (60, Int.ofNat 8), (61, Int.ofNat 8), (86, Int.negSucc 7), (87, Int.negSucc
    7), (89, Int.ofNat 8), (90, Int.ofNat 8), (115, Int.negSucc 7), (468, Int.negSucc 7), (498,
    Int.negSucc 7), (588, Int.negSucc 7), (618, Int.negSucc 7), (812, Int.negSucc 7), (813,
    Int.ofNat 16), (814, Int.negSucc 7), (815, Int.negSucc 7), (29, Int.ofNat 8), (31, Int.negSucc
    7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc 15), (60, Int.ofNat 16), (61,
    Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588, Int.negSucc 7), (678,
    Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.ofNat
    8), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (648, Int.negSucc 7), (708,
    Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat 8), (2, Int.negSucc 7),
    (3, Int.ofNat 8), (28, Int.negSucc 7), (29, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 8), (60, Int.negSucc 7), (61, Int.ofNat
    8), (86, Int.negSucc 7), (87, Int.ofNat 8), (89, Int.negSucc 7), (90, Int.ofNat 8), (115,
    Int.negSucc 7), (468, Int.negSucc 7), (558, Int.negSucc 7), (588, Int.negSucc 7), (648,
    Int.negSucc 7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814, Int.negSucc 7), (815,
    Int.negSucc 7), (0, Int.ofNat 8), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.negSucc 7),
    (29, Int.negSucc 23), (31, Int.negSucc 23), (32, Int.ofNat 24), (57, Int.ofNat 24), (58,
    Int.ofNat 8), (60, Int.ofNat 8), (61, Int.negSucc 7), (86, Int.negSucc 7), (87, Int.ofNat 24),
    (89, Int.ofNat 24), (90, Int.negSucc 23), (115, Int.negSucc 23), (132, Int.ofNat 8), (498,
    Int.negSucc 7), (558, Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (738,
    Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 7), (813, Int.ofNat 24), (814,
    Int.negSucc 7), (815, Int.negSucc 23), (29, Int.negSucc 7), (31, Int.negSucc 7), (32,
    Int.ofNat 8), (57, Int.ofNat 8), (58, Int.ofNat 16), (60, Int.ofNat 16), (61, Int.negSucc 15),
    (86, Int.negSucc 15), (498, Int.negSucc 7), (648, Int.negSucc 7), (738, Int.ofNat 8), (813,
    Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat
    16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
    Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc 7), (708, Int.ofNat 8), (812,
    Int.negSucc 15), (813, Int.ofNat 8), (0, Int.ofNat 16), (2, Int.ofNat 16), (3, Int.negSucc
    15), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57,
    Int.ofNat 8), (558, Int.negSucc 7), (618, Int.negSucc 7), (738, Int.ofNat 8), (812,
    Int.negSucc 15), (813, Int.ofNat 8), (798, Int.negSucc 15), (813, Int.ofNat 16), (840,
    Int.negSucc 15), (768, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (814,
    Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 16), (588, Int.ofNat 8), (798, Int.ofNat
    8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.ofNat 16), (618, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc
    15), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (648, Int.ofNat 8), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (840, Int.ofNat 16), (468, Int.ofNat 8), (798, Int.negSucc 7), (815, Int.ofNat 16), (840,
    Int.negSucc 15), (498, Int.ofNat 8), (798, Int.negSucc 7), (814, Int.ofNat 16), (840,
    Int.negSucc 15), (558, Int.ofNat 8), (798, Int.negSucc 7), (812, Int.ofNat 16), (840,
    Int.negSucc 15)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 11, mode := 2, source := [(11, Int.negSucc 2), (40, Int.ofNat 5), (69, Int.negSucc
    0), (98, Int.negSucc 4), (125, Int.ofNat 3), (153, Int.ofNat 1), (237, Int.ofNat 1), (265,
    Int.ofNat 3), (319, Int.negSucc 2), (320, Int.ofNat 5), (321, Int.negSucc 0), (322,
    Int.negSucc 4), (425, Int.ofNat 1), (565, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16),
    (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252,
    Int.ofNat 8), (282, Int.ofNat 8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat
    8), (618, Int.ofNat 8), (678, Int.negSucc 7), (0, Int.negSucc 23), (1, Int.ofNat 60), (2,
    Int.negSucc 23), (3, Int.negSucc 47), (29, Int.ofNat 60), (30, Int.negSucc 143), (31,
    Int.ofNat 60), (32, Int.ofNat 108), (58, Int.negSucc 23), (59, Int.ofNat 60), (60, Int.negSucc
    23), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 108), (89, Int.negSucc 47),
    (90, Int.negSucc 71), (132, Int.ofNat 12), (192, Int.ofNat 36), (252, Int.ofNat 12), (468,
    Int.ofNat 12), (528, Int.ofNat 36), (588, Int.ofNat 12), (0, Int.ofNat 16), (1, Int.negSucc
    47), (2, Int.ofNat 32), (3, Int.ofNat 32), (29, Int.negSucc 47), (30, Int.ofNat 128), (31,
    Int.negSucc 79), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 79), (60,
    Int.ofNat 48), (61, Int.ofNat 48), (87, Int.ofNat 32), (88, Int.negSucc 79), (89, Int.ofNat
    48), (90, Int.ofNat 48), (132, Int.negSucc 7), (162, Int.negSucc 7), (192, Int.negSucc 31),
    (252, Int.negSucc 7), (282, Int.negSucc 7), (468, Int.negSucc 7), (498, Int.negSucc 7), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 7), (1, Int.ofNat 16), (3,
    Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc 15), (32, Int.ofNat 16), (87,
    Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat
    8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat 8), (708,
    Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7), (282, Int.negSucc 7), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc
    7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7),
    (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0,
    Int.ofNat 72), (1, Int.negSucc 119), (2, Int.ofNat 48), (3, Int.ofNat 72), (29, Int.negSucc
    119), (30, Int.ofNat 192), (31, Int.negSucc 71), (32, Int.negSucc 119), (58, Int.ofNat 48),
    (59, Int.negSucc 71), (60, Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat 72), (88,
    Int.negSucc 119), (89, Int.ofNat 48), (90, Int.ofNat 72), (132, Int.negSucc 11), (192,
    Int.negSucc 47), (222, Int.negSucc 11), (252, Int.negSucc 11), (312, Int.negSucc 11), (468,
    Int.negSucc 11), (528, Int.negSucc 47), (558, Int.negSucc 11), (588, Int.negSucc 11), (648,
    Int.negSucc 11), (1, Int.ofNat 32), (2, Int.negSucc 63), (29, Int.ofNat 32), (30, Int.negSucc
    95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58, Int.negSucc 63), (59, Int.ofNat 112), (60,
    Int.negSucc 63), (61, Int.negSucc 63), (88, Int.ofNat 32), (89, Int.negSucc 63), (162,
    Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat 32), (312, Int.ofNat
    8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498, Int.ofNat 16), (528, Int.ofNat 32),
    (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat 8), (678, Int.negSucc 7), (738,
    Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc 7), (3, Int.negSucc
    7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32, Int.ofNat 4), (58,
    Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4), (192, Int.ofNat 4),
    (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558, Int.ofNat 12), (648,
    Int.ofNat 4), (528, Int.ofNat 72), (588, Int.ofNat 72), (618, Int.ofNat 72), (648, Int.ofNat
    72), (678, Int.negSucc 71), (708, Int.negSucc 71), (738, Int.negSucc 71), (768, Int.ofNat 72),
    (30, Int.ofNat 40), (57, Int.negSucc 39), (88, Int.negSucc 79), (115, Int.ofNat 80), (528,
    Int.negSucc 39), (588, Int.negSucc 39), (738, Int.ofNat 40), (768, Int.negSucc 39), (813,
    Int.negSucc 39), (815, Int.ofNat 80), (1, Int.negSucc 7), (28, Int.ofNat 8), (30, Int.ofNat
    16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88, Int.negSucc 7), (115,
    Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.ofNat
    8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (30, Int.ofNat 8), (57,
    Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618,
    Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (1, Int.negSucc 31), (28, Int.ofNat 32), (30, Int.ofNat 16), (57, Int.negSucc
    15), (528, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (768, Int.negSucc 15),
    (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 32), (30, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.ofNat 32), (57, Int.negSucc 31), (87, Int.negSucc 63), (88, Int.ofNat
    64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115, Int.ofNat 64), (468, Int.ofNat 32),
    (738, Int.ofNat 32), (768, Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 31), (30, Int.ofNat 32), (31, Int.negSucc 31), (32,
    Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 64), (59, Int.negSucc 63), (60, Int.ofNat
    64), (61, Int.ofNat 64), (86, Int.negSucc 63), (498, Int.negSucc 31), (708, Int.negSucc 31),
    (768, Int.ofNat 32), (813, Int.ofNat 32), (814, Int.negSucc 63), (0, Int.negSucc 15), (1,
    Int.ofNat 16), (2, Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat
    8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (558,
    Int.ofNat 8), (678, Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc
    7), (29, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat 24), (87,
    Int.negSucc 47), (89, Int.ofNat 48), (90, Int.ofNat 48), (115, Int.negSucc 47), (468,
    Int.negSucc 23), (618, Int.negSucc 23), (678, Int.ofNat 24), (813, Int.ofNat 24), (815,
    Int.negSucc 47), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87,
    Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468,
    Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812,
    Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.ofNat 16),
    (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (588,
    Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (29,
    Int.negSucc 31), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (87, Int.ofNat
    64), (89, Int.negSucc 63), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 31),
    (648, Int.negSucc 31), (708, Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (0,
    Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc
    31), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (60,
    Int.negSucc 15), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (89,
    Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15), (558,
    Int.negSucc 15), (588, Int.negSucc 15), (648, Int.negSucc 15), (812, Int.negSucc 15), (813,
    Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (0, Int.ofNat 32), (2, Int.ofNat
    32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95),
    (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61,
    Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90,
    Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558,
    Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.ofNat 16), (31, Int.ofNat 16), (32, Int.negSucc 15), (57,
    Int.negSucc 15), (58, Int.negSucc 31), (60, Int.negSucc 31), (61, Int.ofNat 32), (86,
    Int.ofNat 32), (498, Int.ofNat 16), (648, Int.ofNat 16), (738, Int.negSucc 15), (813,
    Int.negSucc 15), (814, Int.ofNat 32), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.ofNat
    32), (28, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.negSucc 15),
    (57, Int.ofNat 16), (558, Int.negSucc 15), (588, Int.negSucc 15), (708, Int.ofNat 16), (812,
    Int.negSucc 31), (813, Int.ofNat 16), (0, Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc
    31), (28, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16),
    (57, Int.ofNat 16), (558, Int.negSucc 15), (618, Int.negSucc 15), (738, Int.ofNat 16), (812,
    Int.negSucc 31), (813, Int.ofNat 16), (798, Int.negSucc 15), (813, Int.ofNat 16), (840,
    Int.negSucc 15), (768, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (814,
    Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 16), (588, Int.ofNat 8), (798, Int.ofNat
    8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.ofNat 16), (618, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc
    15), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat 16), (648, Int.ofNat 8), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (840, Int.ofNat 16), (468, Int.ofNat 24), (798, Int.negSucc 23), (815, Int.ofNat 48),
    (840, Int.negSucc 47), (498, Int.ofNat 8), (798, Int.negSucc 7), (814, Int.ofNat 16), (840,
    Int.negSucc 15), (558, Int.ofNat 16), (798, Int.negSucc 15), (812, Int.ofNat 32), (840,
    Int.negSucc 31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57,
    Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat 32), (90, Int.negSucc 31), (115, Int.negSucc
    31), (738, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16), (813, Int.negSucc 15),
    (840, Int.ofNat 32), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28,
    Int.negSucc 15), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat
    8), (678, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840,
    Int.ofNat 16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 3, source := [(14, Int.negSucc 1), (43, Int.ofNat 6), (72, Int.negSucc
    1), (101, Int.negSucc 5), (129, Int.ofNat 2), (381, Int.ofNat 2), (406, Int.negSucc 1), (407,
    Int.ofNat 6), (408, Int.negSucc 1), (409, Int.negSucc 5), (453, Int.negSucc 1), (537,
    Int.negSucc 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 56), (32, Int.negSucc 111), (88, Int.negSucc 111), (90, Int.ofNat
    224), (132, Int.negSucc 55), (468, Int.negSucc 55), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (30, Int.negSucc
    15), (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.ofNat 40), (1, Int.negSucc 99), (2, Int.ofNat 40), (3, Int.ofNat 80),
    (29, Int.negSucc 99), (30, Int.ofNat 240), (31, Int.negSucc 99), (32, Int.negSucc 179), (58,
    Int.ofNat 40), (59, Int.negSucc 99), (60, Int.ofNat 40), (61, Int.ofNat 80), (87, Int.ofNat
    80), (88, Int.negSucc 179), (89, Int.ofNat 80), (90, Int.ofNat 120), (132, Int.negSucc 19),
    (192, Int.negSucc 59), (252, Int.negSucc 19), (468, Int.negSucc 19), (528, Int.negSucc 59),
    (588, Int.negSucc 19), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 31), (3,
    Int.negSucc 31), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 80), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 47), (61, Int.negSucc 47),
    (87, Int.negSucc 31), (88, Int.ofNat 80), (89, Int.negSucc 47), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (162, Int.ofNat 8), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat 8),
    (468, Int.ofNat 8), (498, Int.ofNat 8), (528, Int.ofNat 32), (588, Int.ofNat 8), (618,
    Int.ofNat 8), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat
    8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402,
    Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat
    8), (768, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48),
    (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
    Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23),
    (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
    Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
    Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (528, Int.ofNat 64), (588, Int.ofNat 64), (618, Int.ofNat 64), (648, Int.ofNat
    64), (678, Int.negSucc 63), (708, Int.negSucc 63), (738, Int.negSucc 63), (768, Int.ofNat 64),
    (30, Int.ofNat 32), (57, Int.negSucc 31), (88, Int.negSucc 63), (115, Int.ofNat 64), (528,
    Int.negSucc 31), (588, Int.negSucc 31), (738, Int.ofNat 32), (768, Int.negSucc 31), (813,
    Int.negSucc 31), (815, Int.ofNat 64), (1, Int.negSucc 7), (28, Int.ofNat 8), (30, Int.ofNat
    16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88, Int.negSucc 7), (115,
    Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.ofNat
    8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (30, Int.ofNat 8), (57,
    Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618,
    Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7),
    (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 40), (30, Int.negSucc 39), (31,
    Int.ofNat 40), (32, Int.ofNat 40), (57, Int.negSucc 39), (87, Int.negSucc 79), (88, Int.ofNat
    80), (89, Int.negSucc 79), (90, Int.negSucc 79), (115, Int.ofNat 80), (468, Int.ofNat 40),
    (738, Int.ofNat 40), (768, Int.negSucc 39), (813, Int.negSucc 39), (815, Int.ofNat 80), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 32), (59, Int.negSucc 31), (60, Int.ofNat
    32), (61, Int.ofNat 32), (86, Int.negSucc 31), (498, Int.negSucc 15), (708, Int.negSucc 15),
    (768, Int.ofNat 16), (813, Int.ofNat 16), (814, Int.negSucc 31), (0, Int.ofNat 32), (1,
    Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc
    15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (558,
    Int.negSucc 15), (678, Int.negSucc 15), (768, Int.ofNat 16), (812, Int.negSucc 31), (813,
    Int.ofNat 16), (29, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57, Int.ofNat
    24), (87, Int.negSucc 47), (89, Int.ofNat 48), (90, Int.ofNat 48), (115, Int.negSucc 47),
    (468, Int.negSucc 23), (618, Int.negSucc 23), (678, Int.ofNat 24), (813, Int.ofNat 24), (815,
    Int.negSucc 47), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87,
    Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468,
    Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812,
    Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.ofNat 24), (87, Int.ofNat
    48), (89, Int.negSucc 47), (90, Int.ofNat 48), (115, Int.negSucc 47), (468, Int.negSucc 23),
    (648, Int.negSucc 23), (708, Int.ofNat 24), (813, Int.ofNat 24), (815, Int.negSucc 47), (0,
    Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc
    47), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60,
    Int.negSucc 23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89,
    Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558,
    Int.negSucc 23), (588, Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813,
    Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 32), (2, Int.ofNat
    32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95),
    (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61,
    Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90,
    Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558,
    Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc
    7), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (498,
    Int.ofNat 8), (648, Int.ofNat 8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat
    16), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29,
    Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8),
    (618, Int.ofNat 8), (738, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798,
    Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 32), (798, Int.negSucc 31), (815,
    Int.ofNat 64), (840, Int.negSucc 63), (498, Int.ofNat 16), (798, Int.negSucc 15), (814,
    Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 16), (798, Int.negSucc 15), (812,
    Int.ofNat 32), (840, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32,
    Int.ofNat 16), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat 32), (90, Int.negSucc
    31), (115, Int.negSucc 31), (738, Int.negSucc 15), (768, Int.ofNat 16), (798, Int.ofNat 16),
    (813, Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 16), (812, Int.negSucc 15), (813,
    Int.ofNat 16), (814, Int.negSucc 15), (815, Int.negSucc 15), (840, Int.ofNat 16), (798,
    Int.negSucc 7), (812, Int.ofNat 8), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.negSucc 7)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 18, mode := 3, source := [(18, Int.ofNat 1), (47, Int.negSucc 3), (76, Int.ofNat 1),
    (105, Int.ofNat 5), (136, Int.negSucc 2), (166, Int.negSucc 0), (225, Int.ofNat 1), (433,
    Int.ofNat 1), (522, Int.ofNat 1), (523, Int.negSucc 3), (524, Int.ofNat 1), (525, Int.ofNat
    5), (584, Int.negSucc 2), (614, Int.negSucc 0), (645, Int.ofNat 1), (797, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 23), (32, Int.ofNat 48), (88, Int.ofNat 48), (90, Int.negSucc 95),
    (132, Int.ofNat 24), (468, Int.ofNat 24), (1, Int.negSucc 11), (3, Int.ofNat 24), (29,
    Int.negSucc 11), (30, Int.ofNat 72), (31, Int.negSucc 11), (32, Int.negSucc 107), (59,
    Int.negSucc 11), (61, Int.ofNat 24), (87, Int.ofNat 24), (88, Int.negSucc 107), (89, Int.ofNat
    24), (90, Int.ofNat 144), (132, Int.negSucc 35), (192, Int.negSucc 11), (252, Int.negSucc 11),
    (468, Int.negSucc 35), (528, Int.negSucc 11), (588, Int.negSucc 11), (0, Int.negSucc 71), (1,
    Int.ofNat 180), (2, Int.negSucc 71), (3, Int.negSucc 143), (29, Int.ofNat 180), (30,
    Int.negSucc 431), (31, Int.ofNat 180), (32, Int.ofNat 324), (58, Int.negSucc 71), (59,
    Int.ofNat 180), (60, Int.negSucc 71), (61, Int.negSucc 143), (87, Int.negSucc 143), (88,
    Int.ofNat 324), (89, Int.negSucc 143), (90, Int.negSucc 215), (132, Int.ofNat 36), (192,
    Int.ofNat 108), (252, Int.ofNat 36), (468, Int.ofNat 36), (528, Int.ofNat 108), (588,
    Int.ofNat 36), (0, Int.ofNat 48), (1, Int.negSucc 143), (2, Int.ofNat 96), (3, Int.ofNat 96),
    (29, Int.negSucc 143), (30, Int.ofNat 384), (31, Int.negSucc 239), (32, Int.negSucc 239), (58,
    Int.ofNat 96), (59, Int.negSucc 239), (60, Int.ofNat 144), (61, Int.ofNat 144), (87, Int.ofNat
    96), (88, Int.negSucc 239), (89, Int.ofNat 144), (90, Int.ofNat 144), (132, Int.negSucc 23),
    (162, Int.negSucc 23), (192, Int.negSucc 95), (252, Int.negSucc 23), (282, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (528, Int.negSucc 95), (588, Int.negSucc 23),
    (618, Int.negSucc 23), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30,
    Int.negSucc 15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat
    8), (252, Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588,
    Int.ofNat 8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252,
    Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372,
    Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (528, Int.negSucc 95), (588, Int.negSucc 95),
    (618, Int.negSucc 95), (648, Int.negSucc 95), (678, Int.ofNat 96), (708, Int.ofNat 96), (738,
    Int.ofNat 96), (768, Int.negSucc 95), (30, Int.negSucc 39), (57, Int.ofNat 40), (88, Int.ofNat
    80), (115, Int.negSucc 79), (528, Int.ofNat 40), (588, Int.ofNat 40), (738, Int.negSucc 39),
    (768, Int.ofNat 40), (813, Int.ofNat 40), (815, Int.negSucc 79), (1, Int.ofNat 8), (28,
    Int.negSucc 7), (30, Int.negSucc 15), (57, Int.ofNat 16), (59, Int.ofNat 8), (86, Int.negSucc
    7), (88, Int.ofNat 8), (115, Int.negSucc 7), (528, Int.ofNat 8), (768, Int.ofNat 8), (798,
    Int.negSucc 7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814, Int.negSucc 7), (815,
    Int.negSucc 7), (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat 16), (86, Int.negSucc
    15), (528, Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768, Int.ofNat 8), (813,
    Int.ofNat 8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc 15), (30, Int.negSucc
    7), (57, Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678, Int.negSucc 7), (768,
    Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 71), (30, Int.ofNat
    72), (31, Int.negSucc 71), (32, Int.negSucc 71), (57, Int.ofNat 72), (87, Int.ofNat 144), (88,
    Int.negSucc 143), (89, Int.ofNat 144), (90, Int.ofNat 144), (115, Int.negSucc 143), (468,
    Int.negSucc 71), (738, Int.negSucc 71), (768, Int.ofNat 72), (813, Int.ofNat 72), (815,
    Int.negSucc 143), (0, Int.ofNat 16), (1, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat
    16), (28, Int.negSucc 15), (29, Int.negSucc 31), (30, Int.ofNat 32), (31, Int.negSucc 31),
    (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (59, Int.negSucc 15), (60,
    Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (88, Int.negSucc
    15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15),
    (498, Int.negSucc 15), (558, Int.negSucc 15), (678, Int.negSucc 15), (708, Int.negSucc 15),
    (738, Int.negSucc 15), (768, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.negSucc 15), (29, Int.negSucc 7), (30, Int.ofNat 8), (31,
    Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16), (59, Int.negSucc
    15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (708,
    Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.ofNat
    16), (1, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29,
    Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat
    8), (558, Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15),
    (813, Int.ofNat 8), (29, Int.negSucc 55), (31, Int.ofNat 56), (32, Int.ofNat 56), (57,
    Int.negSucc 55), (87, Int.ofNat 112), (89, Int.negSucc 111), (90, Int.negSucc 111), (115,
    Int.ofNat 112), (468, Int.ofNat 56), (618, Int.ofNat 56), (678, Int.negSucc 55), (813,
    Int.negSucc 55), (815, Int.ofNat 112), (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.negSucc
    15), (28, Int.ofNat 16), (29, Int.negSucc 31), (31, Int.ofNat 32), (32, Int.ofNat 32), (57,
    Int.negSucc 31), (58, Int.ofNat 16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (87, Int.ofNat 16), (89, Int.negSucc 15), (90, Int.negSucc 15), (115, Int.ofNat
    16), (468, Int.ofNat 16), (498, Int.ofNat 16), (588, Int.ofNat 16), (618, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8), (57, Int.negSucc 7), (58, Int.ofNat 16),
    (60, Int.negSucc 15), (61, Int.negSucc 15), (86, Int.ofNat 16), (498, Int.ofNat 8), (588,
    Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (29, Int.ofNat
    56), (31, Int.negSucc 55), (32, Int.ofNat 56), (57, Int.negSucc 55), (87, Int.negSucc 111),
    (89, Int.ofNat 112), (90, Int.negSucc 111), (115, Int.ofNat 112), (468, Int.ofNat 56), (648,
    Int.ofNat 56), (708, Int.negSucc 55), (813, Int.negSucc 55), (815, Int.ofNat 112), (0,
    Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat
    32), (31, Int.negSucc 31), (32, Int.ofNat 32), (57, Int.negSucc 31), (58, Int.negSucc 15),
    (60, Int.ofNat 16), (61, Int.negSucc 15), (86, Int.ofNat 16), (87, Int.negSucc 15), (89,
    Int.ofNat 16), (90, Int.negSucc 15), (115, Int.ofNat 16), (468, Int.ofNat 16), (558, Int.ofNat
    16), (588, Int.ofNat 16), (648, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31),
    (814, Int.ofNat 16), (815, Int.ofNat 16), (0, Int.negSucc 15), (2, Int.negSucc 15), (3,
    Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat 48), (31, Int.ofNat 48), (32, Int.negSucc
    47), (57, Int.negSucc 47), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16),
    (86, Int.ofNat 16), (87, Int.negSucc 47), (89, Int.negSucc 47), (90, Int.ofNat 48), (115,
    Int.ofNat 48), (132, Int.negSucc 15), (498, Int.ofNat 16), (558, Int.ofNat 16), (618,
    Int.ofNat 16), (648, Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.negSucc 47), (814, Int.ofNat 16), (815, Int.ofNat 48), (29, Int.ofNat
    8), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (58, Int.negSucc 15), (60,
    Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (498, Int.ofNat 8), (648, Int.ofNat
    8), (738, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0, Int.negSucc 15), (2,
    Int.ofNat 16), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.ofNat 8), (31, Int.negSucc
    7), (32, Int.ofNat 8), (57, Int.negSucc 7), (558, Int.ofNat 8), (588, Int.ofNat 8), (708,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (0, Int.negSucc 15), (2,
    Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat 8), (31, Int.ofNat 8),
    (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8), (618, Int.ofNat 8), (738,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798, Int.ofNat 40), (813,
    Int.negSucc 39), (840, Int.ofNat 40), (768, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (814, Int.ofNat 16), (815, Int.ofNat 16), (840, Int.negSucc 31), (588,
    Int.negSucc 15), (798, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.negSucc 31), (618, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 31), (648, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.negSucc 31), (468, Int.negSucc 47), (798, Int.ofNat 48), (815, Int.negSucc 95), (840,
    Int.ofNat 96), (498, Int.negSucc 15), (798, Int.ofNat 16), (814, Int.negSucc 31), (840,
    Int.ofNat 32), (558, Int.negSucc 15), (798, Int.ofNat 16), (812, Int.negSucc 31), (840,
    Int.ofNat 32), (29, Int.ofNat 32), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.negSucc
    31), (87, Int.negSucc 63), (89, Int.negSucc 63), (90, Int.ofNat 64), (115, Int.ofNat 64),
    (738, Int.ofNat 32), (768, Int.negSucc 31), (798, Int.negSucc 31), (813, Int.ofNat 32), (840,
    Int.negSucc 63), (798, Int.negSucc 23), (812, Int.ofNat 24), (813, Int.negSucc 23), (814,
    Int.ofNat 24), (815, Int.ofNat 24), (840, Int.negSucc 23), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 1, source := [(14, Int.negSucc 3), (43, Int.ofNat 10), (72, Int.negSucc
    9), (101, Int.negSucc 3), (157, Int.ofNat 2), (326, Int.ofNat 1), (381, Int.negSucc 0), (537,
    Int.negSucc 3)],
    denominator := Int.ofNat 8,
    target := [(1, Int.negSucc 15), (3, Int.ofNat 32), (29, Int.negSucc 15), (30, Int.ofNat 96),
    (31, Int.negSucc 15), (32, Int.negSucc 143), (59, Int.negSucc 15), (61, Int.ofNat 32), (87,
    Int.ofNat 32), (88, Int.negSucc 143), (89, Int.ofNat 32), (90, Int.ofNat 192), (132,
    Int.negSucc 47), (192, Int.negSucc 15), (252, Int.negSucc 15), (468, Int.negSucc 47), (528,
    Int.negSucc 15), (588, Int.negSucc 15), (0, Int.negSucc 135), (1, Int.ofNat 340), (2,
    Int.negSucc 135), (3, Int.negSucc 271), (29, Int.ofNat 340), (30, Int.negSucc 815), (31,
    Int.ofNat 340), (32, Int.ofNat 612), (58, Int.negSucc 135), (59, Int.ofNat 340), (60,
    Int.negSucc 135), (61, Int.negSucc 271), (87, Int.negSucc 271), (88, Int.ofNat 612), (89,
    Int.negSucc 271), (90, Int.negSucc 407), (132, Int.ofNat 68), (192, Int.ofNat 204), (252,
    Int.ofNat 68), (468, Int.ofNat 68), (528, Int.ofNat 204), (588, Int.ofNat 68), (0, Int.ofNat
    96), (1, Int.negSucc 287), (2, Int.ofNat 192), (3, Int.ofNat 192), (29, Int.negSucc 287), (30,
    Int.ofNat 768), (31, Int.negSucc 479), (32, Int.negSucc 479), (58, Int.ofNat 192), (59,
    Int.negSucc 479), (60, Int.ofNat 288), (61, Int.ofNat 288), (87, Int.ofNat 192), (88,
    Int.negSucc 479), (89, Int.ofNat 288), (90, Int.ofNat 288), (132, Int.negSucc 47), (162,
    Int.negSucc 47), (192, Int.negSucc 191), (252, Int.negSucc 47), (282, Int.negSucc 47), (468,
    Int.negSucc 47), (498, Int.negSucc 47), (528, Int.negSucc 191), (588, Int.negSucc 47), (618,
    Int.negSucc 47), (1, Int.ofNat 16), (2, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    95), (31, Int.ofNat 144), (32, Int.ofNat 16), (58, Int.negSucc 31), (59, Int.ofNat 144), (60,
    Int.negSucc 191), (61, Int.negSucc 31), (88, Int.ofNat 16), (89, Int.negSucc 31), (162,
    Int.ofNat 48), (192, Int.ofNat 16), (282, Int.ofNat 16), (498, Int.ofNat 48), (528, Int.ofNat
    16), (618, Int.ofNat 16), (0, Int.ofNat 72), (1, Int.negSucc 119), (2, Int.ofNat 48), (3,
    Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat 192), (31, Int.negSucc 71), (32,
    Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71), (60, Int.ofNat 24), (61, Int.ofNat
    48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89, Int.ofNat 48), (90, Int.ofNat 72), (132,
    Int.negSucc 11), (192, Int.negSucc 47), (222, Int.negSucc 11), (252, Int.negSucc 11), (312,
    Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 47), (558, Int.negSucc 11), (588,
    Int.negSucc 11), (648, Int.negSucc 11), (1, Int.ofNat 32), (2, Int.negSucc 63), (29, Int.ofNat
    32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58, Int.negSucc 63), (59,
    Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88, Int.ofNat 32), (89,
    Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat
    32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498, Int.ofNat 16),
    (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat 8), (678,
    Int.negSucc 7), (738, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc
    7), (3, Int.negSucc 7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32,
    Int.ofNat 4), (58, Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4),
    (192, Int.ofNat 4), (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558,
    Int.ofNat 12), (648, Int.ofNat 4), (528, Int.ofNat 144), (588, Int.ofNat 144), (618, Int.ofNat
    144), (648, Int.ofNat 144), (678, Int.negSucc 143), (708, Int.negSucc 143), (738, Int.negSucc
    143), (768, Int.ofNat 144), (30, Int.ofNat 8), (57, Int.negSucc 7), (88, Int.negSucc 15),
    (115, Int.ofNat 16), (528, Int.negSucc 7), (588, Int.negSucc 7), (738, Int.ofNat 8), (768,
    Int.negSucc 7), (813, Int.negSucc 7), (815, Int.ofNat 16), (1, Int.negSucc 47), (28, Int.ofNat
    48), (30, Int.ofNat 96), (57, Int.negSucc 95), (59, Int.negSucc 47), (86, Int.ofNat 48), (88,
    Int.negSucc 47), (115, Int.ofNat 48), (528, Int.negSucc 47), (768, Int.negSucc 47), (798,
    Int.ofNat 48), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48), (815,
    Int.ofNat 48), (30, Int.ofNat 48), (57, Int.negSucc 47), (59, Int.negSucc 95), (86, Int.ofNat
    96), (528, Int.negSucc 47), (618, Int.negSucc 47), (708, Int.ofNat 48), (768, Int.negSucc 47),
    (813, Int.negSucc 47), (814, Int.ofNat 96), (1, Int.negSucc 15), (28, Int.ofNat 16), (30,
    Int.ofNat 8), (57, Int.negSucc 7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat
    8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 56), (30,
    Int.negSucc 55), (31, Int.ofNat 56), (32, Int.ofNat 56), (57, Int.negSucc 55), (87,
    Int.negSucc 111), (88, Int.ofNat 112), (89, Int.negSucc 111), (90, Int.negSucc 111), (115,
    Int.ofNat 112), (468, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (813,
    Int.negSucc 55), (815, Int.ofNat 112), (0, Int.negSucc 63), (1, Int.ofNat 64), (2, Int.negSucc
    63), (3, Int.negSucc 63), (28, Int.ofNat 64), (29, Int.ofNat 128), (30, Int.negSucc 127), (31,
    Int.ofNat 128), (32, Int.ofNat 128), (57, Int.negSucc 127), (58, Int.negSucc 63), (59,
    Int.ofNat 64), (60, Int.negSucc 63), (61, Int.negSucc 63), (86, Int.ofNat 64), (87,
    Int.negSucc 63), (88, Int.ofNat 64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115,
    Int.ofNat 64), (468, Int.ofNat 64), (498, Int.ofNat 64), (558, Int.ofNat 64), (678, Int.ofNat
    64), (708, Int.ofNat 64), (738, Int.ofNat 64), (768, Int.negSucc 63), (812, Int.ofNat 64),
    (813, Int.negSucc 127), (814, Int.ofNat 64), (815, Int.ofNat 64), (29, Int.ofNat 64), (30,
    Int.negSucc 63), (31, Int.ofNat 64), (32, Int.ofNat 64), (57, Int.negSucc 63), (58,
    Int.negSucc 127), (59, Int.ofNat 128), (60, Int.negSucc 127), (61, Int.negSucc 127), (86,
    Int.ofNat 128), (498, Int.ofNat 64), (708, Int.ofNat 64), (768, Int.negSucc 63), (813,
    Int.negSucc 63), (814, Int.ofNat 128), (0, Int.negSucc 31), (1, Int.ofNat 32), (2, Int.negSucc
    31), (3, Int.negSucc 31), (28, Int.ofNat 32), (29, Int.ofNat 16), (30, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (558, Int.ofNat 16), (678, Int.ofNat
    16), (768, Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 16),
    (31, Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (87, Int.negSucc 31), (89,
    Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 15), (618,
    Int.negSucc 15), (678, Int.ofNat 16), (813, Int.ofNat 16), (815, Int.negSucc 31), (0,
    Int.negSucc 39), (2, Int.ofNat 40), (3, Int.ofNat 40), (28, Int.negSucc 39), (29, Int.ofNat
    80), (31, Int.negSucc 79), (32, Int.negSucc 79), (57, Int.ofNat 80), (58, Int.negSucc 39),
    (60, Int.ofNat 40), (61, Int.ofNat 40), (86, Int.negSucc 39), (87, Int.negSucc 39), (89,
    Int.ofNat 40), (90, Int.ofNat 40), (115, Int.negSucc 39), (468, Int.negSucc 39), (498,
    Int.negSucc 39), (588, Int.negSucc 39), (618, Int.negSucc 39), (812, Int.negSucc 39), (813,
    Int.ofNat 80), (814, Int.negSucc 39), (815, Int.negSucc 39), (29, Int.ofNat 56), (31,
    Int.negSucc 55), (32, Int.negSucc 55), (57, Int.ofNat 56), (58, Int.negSucc 111), (60,
    Int.ofNat 112), (61, Int.ofNat 112), (86, Int.negSucc 111), (498, Int.negSucc 55), (588,
    Int.negSucc 55), (678, Int.ofNat 56), (813, Int.ofNat 56), (814, Int.negSucc 111), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16),
    (89, Int.negSucc 15), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (648,
    Int.negSucc 7), (708, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat
    48), (2, Int.negSucc 47), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.negSucc 95), (31,
    Int.ofNat 96), (32, Int.negSucc 95), (57, Int.ofNat 96), (58, Int.ofNat 48), (60, Int.negSucc
    47), (61, Int.ofNat 48), (86, Int.negSucc 47), (87, Int.ofNat 48), (89, Int.negSucc 47), (90,
    Int.ofNat 48), (115, Int.negSucc 47), (468, Int.negSucc 47), (558, Int.negSucc 47), (588,
    Int.negSucc 47), (648, Int.negSucc 47), (812, Int.negSucc 47), (813, Int.ofNat 96), (814,
    Int.negSucc 47), (815, Int.negSucc 47), (0, Int.ofNat 40), (2, Int.ofNat 40), (3, Int.negSucc
    39), (28, Int.negSucc 39), (29, Int.negSucc 119), (31, Int.negSucc 119), (32, Int.ofNat 120),
    (57, Int.ofNat 120), (58, Int.ofNat 40), (60, Int.ofNat 40), (61, Int.negSucc 39), (86,
    Int.negSucc 39), (87, Int.ofNat 120), (89, Int.ofNat 120), (90, Int.negSucc 119), (115,
    Int.negSucc 119), (132, Int.ofNat 40), (498, Int.negSucc 39), (558, Int.negSucc 39), (618,
    Int.negSucc 39), (648, Int.negSucc 39), (738, Int.negSucc 39), (768, Int.ofNat 40), (812,
    Int.negSucc 39), (813, Int.ofNat 120), (814, Int.negSucc 39), (815, Int.negSucc 119), (29,
    Int.negSucc 55), (31, Int.negSucc 55), (32, Int.ofNat 56), (57, Int.ofNat 56), (58, Int.ofNat
    112), (60, Int.ofNat 112), (61, Int.negSucc 111), (86, Int.negSucc 111), (498, Int.negSucc
    55), (648, Int.negSucc 55), (738, Int.ofNat 56), (813, Int.ofNat 56), (814, Int.negSucc 111),
    (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29,
    Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57, Int.ofNat 8), (558, Int.negSucc
    7), (588, Int.negSucc 7), (708, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (0,
    Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc
    15), (31, Int.negSucc 15), (32, Int.ofNat 16), (57, Int.ofNat 16), (558, Int.negSucc 15),
    (618, Int.negSucc 15), (738, Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (798,
    Int.negSucc 95), (813, Int.ofNat 96), (840, Int.negSucc 95), (768, Int.ofNat 80), (798,
    Int.ofNat 80), (812, Int.negSucc 79), (814, Int.negSucc 79), (815, Int.negSucc 79), (840,
    Int.ofNat 160), (708, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (813,
    Int.ofNat 16), (814, Int.negSucc 15), (815, Int.ofNat 16), (840, Int.negSucc 31), (588,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814, Int.negSucc 15), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798, Int.ofNat 16), (812,
    Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (840,
    Int.ofNat 32), (468, Int.ofNat 32), (798, Int.negSucc 31), (815, Int.ofNat 64), (840,
    Int.negSucc 63), (498, Int.ofNat 48), (798, Int.negSucc 47), (814, Int.ofNat 96), (840,
    Int.negSucc 95), (558, Int.ofNat 32), (798, Int.negSucc 31), (812, Int.ofNat 64), (840,
    Int.negSucc 63), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat
    8), (87, Int.ofNat 16), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.negSucc 15), (738,
    Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat
    16), (29, Int.negSucc 31), (31, Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58,
    Int.ofNat 64), (60, Int.negSucc 63), (61, Int.ofNat 64), (86, Int.negSucc 63), (708,
    Int.negSucc 31), (768, Int.ofNat 32), (798, Int.ofNat 32), (813, Int.negSucc 31), (840,
    Int.ofNat 64), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc
    15), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (678,
    Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat
    16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 3, source := [(15, Int.negSucc 3), (44, Int.ofNat 10), (73, Int.negSucc
    3), (102, Int.negSucc 7), (188, Int.ofNat 6), (245, Int.ofNat 2), (385, Int.ofNat 2), (412,
    Int.ofNat 6), (435, Int.negSucc 3), (436, Int.ofNat 10), (437, Int.negSucc 3), (438,
    Int.negSucc 7)],
    denominator := Int.ofNat 2,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 24), (3, Int.negSucc 47),
    (29, Int.ofNat 24), (30, Int.negSucc 143), (31, Int.ofNat 24), (32, Int.ofNat 216), (59,
    Int.ofNat 24), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 216), (89,
    Int.negSucc 47), (90, Int.negSucc 287), (132, Int.ofNat 72), (192, Int.ofNat 24), (252,
    Int.ofNat 24), (468, Int.ofNat 72), (528, Int.ofNat 24), (588, Int.ofNat 24), (30, Int.negSucc
    7), (31, Int.ofNat 8), (32, Int.ofNat 8), (59, Int.ofNat 8), (61, Int.negSucc 15), (88,
    Int.ofNat 8), (89, Int.negSucc 15), (192, Int.ofNat 4), (252, Int.ofNat 4), (282, Int.ofNat
    4), (342, Int.negSucc 3), (528, Int.ofNat 4), (588, Int.ofNat 4), (618, Int.ofNat 4), (678,
    Int.negSucc 3), (0, Int.ofNat 48), (1, Int.negSucc 119), (2, Int.ofNat 48), (3, Int.ofNat 96),
    (29, Int.negSucc 119), (30, Int.ofNat 288), (31, Int.negSucc 119), (32, Int.negSucc 215), (58,
    Int.ofNat 48), (59, Int.negSucc 119), (60, Int.ofNat 48), (61, Int.ofNat 96), (87, Int.ofNat
    96), (88, Int.negSucc 215), (89, Int.ofNat 96), (90, Int.ofNat 144), (132, Int.negSucc 23),
    (192, Int.negSucc 71), (252, Int.negSucc 23), (468, Int.negSucc 23), (528, Int.negSucc 71),
    (588, Int.negSucc 23), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 31), (3,
    Int.negSucc 31), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 80), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 47), (61, Int.negSucc 47),
    (87, Int.negSucc 31), (88, Int.ofNat 80), (89, Int.negSucc 47), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (162, Int.ofNat 8), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat 8),
    (468, Int.ofNat 8), (498, Int.ofNat 8), (528, Int.ofNat 32), (588, Int.ofNat 8), (618,
    Int.ofNat 8), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30, Int.negSucc 7),
    (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat 4), (252,
    Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588, Int.ofNat
    4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 3), (252, Int.negSucc 3),
    (282, Int.negSucc 3), (312, Int.negSucc 3), (342, Int.ofNat 4), (372, Int.ofNat 4), (402,
    Int.ofNat 4), (432, Int.negSucc 3), (528, Int.negSucc 3), (588, Int.negSucc 3), (618,
    Int.negSucc 3), (648, Int.negSucc 3), (678, Int.ofNat 4), (708, Int.ofNat 4), (738, Int.ofNat
    4), (768, Int.negSucc 3), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48),
    (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
    Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23),
    (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
    Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
    Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (528, Int.ofNat 56), (588, Int.ofNat 56), (618, Int.ofNat 56), (648, Int.ofNat
    56), (678, Int.negSucc 55), (708, Int.negSucc 55), (738, Int.negSucc 55), (768, Int.ofNat 56),
    (30, Int.ofNat 20), (57, Int.negSucc 19), (88, Int.negSucc 39), (115, Int.ofNat 40), (528,
    Int.negSucc 19), (588, Int.negSucc 19), (738, Int.ofNat 20), (768, Int.negSucc 19), (813,
    Int.negSucc 19), (815, Int.ofNat 40), (1, Int.negSucc 7), (28, Int.ofNat 8), (30, Int.ofNat
    16), (57, Int.negSucc 15), (59, Int.negSucc 7), (86, Int.ofNat 8), (88, Int.negSucc 7), (115,
    Int.ofNat 8), (528, Int.negSucc 7), (768, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.ofNat
    8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat 8), (30, Int.ofNat 8), (57,
    Int.negSucc 7), (59, Int.negSucc 15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618,
    Int.negSucc 7), (708, Int.ofNat 8), (768, Int.negSucc 7), (813, Int.negSucc 7), (814,
    Int.ofNat 16), (1, Int.negSucc 15), (28, Int.ofNat 16), (30, Int.ofNat 8), (57, Int.negSucc
    7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (768, Int.negSucc 7),
    (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 32), (30, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.ofNat 32), (57, Int.negSucc 31), (87, Int.negSucc 63), (88, Int.ofNat
    64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115, Int.ofNat 64), (468, Int.ofNat 32),
    (738, Int.ofNat 32), (768, Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (0,
    Int.negSucc 47), (1, Int.ofNat 48), (2, Int.negSucc 47), (3, Int.negSucc 47), (28, Int.ofNat
    48), (29, Int.ofNat 96), (30, Int.negSucc 95), (31, Int.ofNat 96), (32, Int.ofNat 96), (57,
    Int.negSucc 95), (58, Int.negSucc 47), (59, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.negSucc 47), (86, Int.ofNat 48), (87, Int.negSucc 47), (88, Int.ofNat 48), (89,
    Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 48), (498,
    Int.ofNat 48), (558, Int.ofNat 48), (678, Int.ofNat 48), (708, Int.ofNat 48), (738, Int.ofNat
    48), (768, Int.negSucc 47), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.ofNat 48),
    (815, Int.ofNat 48), (29, Int.negSucc 11), (30, Int.ofNat 12), (31, Int.negSucc 11), (32,
    Int.negSucc 11), (57, Int.ofNat 12), (58, Int.ofNat 24), (59, Int.negSucc 23), (60, Int.ofNat
    24), (61, Int.ofNat 24), (86, Int.negSucc 23), (498, Int.negSucc 11), (708, Int.negSucc 11),
    (768, Int.ofNat 12), (813, Int.ofNat 12), (814, Int.negSucc 23), (0, Int.ofNat 24), (1,
    Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc
    11), (30, Int.ofNat 12), (31, Int.negSucc 11), (32, Int.negSucc 11), (57, Int.ofNat 12), (558,
    Int.negSucc 11), (678, Int.negSucc 11), (768, Int.ofNat 12), (812, Int.negSucc 23), (813,
    Int.ofNat 12), (29, Int.ofNat 12), (31, Int.negSucc 11), (32, Int.negSucc 11), (57, Int.ofNat
    12), (87, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23),
    (468, Int.negSucc 11), (618, Int.negSucc 11), (678, Int.ofNat 12), (813, Int.ofNat 12), (815,
    Int.negSucc 23), (0, Int.negSucc 23), (2, Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc
    23), (29, Int.ofNat 48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87,
    Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23), (468,
    Int.negSucc 23), (498, Int.negSucc 23), (588, Int.negSucc 23), (618, Int.negSucc 23), (812,
    Int.negSucc 23), (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29,
    Int.negSucc 11), (31, Int.ofNat 12), (32, Int.negSucc 11), (57, Int.ofNat 12), (87, Int.ofNat
    24), (89, Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 11),
    (648, Int.negSucc 11), (708, Int.ofNat 12), (813, Int.ofNat 12), (815, Int.negSucc 23), (0,
    Int.ofNat 24), (2, Int.negSucc 23), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc
    47), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (60,
    Int.negSucc 23), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat 24), (89,
    Int.negSucc 23), (90, Int.ofNat 24), (115, Int.negSucc 23), (468, Int.negSucc 23), (558,
    Int.negSucc 23), (588, Int.negSucc 23), (648, Int.negSucc 23), (812, Int.negSucc 23), (813,
    Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (0, Int.ofNat 32), (2, Int.ofNat
    32), (3, Int.negSucc 31), (28, Int.negSucc 31), (29, Int.negSucc 95), (31, Int.negSucc 95),
    (32, Int.ofNat 96), (57, Int.ofNat 96), (58, Int.ofNat 32), (60, Int.ofNat 32), (61,
    Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat 96), (89, Int.ofNat 96), (90,
    Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32), (498, Int.negSucc 31), (558,
    Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814, Int.negSucc 31), (815,
    Int.negSucc 95), (29, Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc
    3), (58, Int.negSucc 7), (60, Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat 8), (498,
    Int.ofNat 4), (648, Int.ofNat 4), (738, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat
    8), (0, Int.negSucc 7), (2, Int.negSucc 7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29,
    Int.ofNat 4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4),
    (618, Int.ofNat 4), (738, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798,
    Int.negSucc 39), (813, Int.ofNat 40), (840, Int.negSucc 39), (768, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.ofNat 32), (588, Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813,
    Int.negSucc 31), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.ofNat 32), (618,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.ofNat 32), (648, Int.ofNat 16), (798,
    Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 24), (798, Int.negSucc 23), (815,
    Int.ofNat 48), (840, Int.negSucc 47), (498, Int.ofNat 16), (798, Int.negSucc 15), (814,
    Int.ofNat 32), (840, Int.negSucc 31), (558, Int.ofNat 16), (798, Int.negSucc 15), (812,
    Int.ofNat 32), (840, Int.negSucc 31), (29, Int.negSucc 7), (31, Int.negSucc 7), (32, Int.ofNat
    8), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.ofNat 16), (90, Int.negSucc 15), (115,
    Int.negSucc 15), (738, Int.negSucc 7), (768, Int.ofNat 8), (798, Int.ofNat 8), (813,
    Int.negSucc 7), (840, Int.ofNat 16), (798, Int.ofNat 12), (812, Int.negSucc 11), (813,
    Int.ofNat 12), (814, Int.negSucc 11), (815, Int.negSucc 11), (840, Int.ofNat 12), (798,
    Int.negSucc 3), (812, Int.ofNat 4), (814, Int.ofNat 4), (815, Int.negSucc 3), (840,
    Int.negSucc 3)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 13, mode := 3, source := [(13, Int.ofNat 3), (42, Int.negSucc 2), (71, Int.ofNat 1),
    (100, Int.ofNat 1), (212, Int.ofNat 1), (268, Int.ofNat 1), (377, Int.ofNat 3), (378,
    Int.negSucc 2), (379, Int.ofNat 1), (380, Int.ofNat 1), (422, Int.ofNat 1), (455, Int.ofNat
    1), (478, Int.ofNat 1), (595, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 71), (32, Int.ofNat 144), (88, Int.ofNat 144), (90, Int.negSucc
    287), (132, Int.ofNat 72), (468, Int.ofNat 72), (1, Int.negSucc 27), (3, Int.ofNat 56), (29,
    Int.negSucc 27), (30, Int.ofNat 168), (31, Int.negSucc 27), (32, Int.negSucc 251), (59,
    Int.negSucc 27), (61, Int.ofNat 56), (87, Int.ofNat 56), (88, Int.negSucc 251), (89, Int.ofNat
    56), (90, Int.ofNat 336), (132, Int.negSucc 83), (192, Int.negSucc 27), (252, Int.negSucc 27),
    (468, Int.negSucc 83), (528, Int.negSucc 27), (588, Int.negSucc 27), (30, Int.negSucc 15),
    (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.ofNat 24), (1, Int.negSucc 59), (2, Int.ofNat 24), (3, Int.ofNat 48),
    (29, Int.negSucc 59), (30, Int.ofNat 144), (31, Int.negSucc 59), (32, Int.negSucc 107), (58,
    Int.ofNat 24), (59, Int.negSucc 59), (60, Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 107), (89, Int.ofNat 48), (90, Int.ofNat 72), (132, Int.negSucc 11),
    (192, Int.negSucc 35), (252, Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 35),
    (588, Int.negSucc 11), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 31), (3,
    Int.negSucc 31), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 80), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 47), (61, Int.negSucc 47),
    (87, Int.negSucc 31), (88, Int.ofNat 80), (89, Int.negSucc 47), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (162, Int.ofNat 8), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat 8),
    (468, Int.ofNat 8), (498, Int.ofNat 8), (528, Int.ofNat 32), (588, Int.ofNat 8), (618,
    Int.ofNat 8), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3, Int.negSucc
    47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat 80), (58,
    Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31), (87,
    Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (1, Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat
    96), (31, Int.negSucc 111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111),
    (60, Int.ofNat 64), (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162,
    Int.negSucc 15), (192, Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312,
    Int.negSucc 7), (342, Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528,
    Int.negSucc 31), (588, Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (738, Int.ofNat 8), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 15),
    (3, Int.negSucc 47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 48), (32,
    Int.ofNat 112), (58, Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc 15), (61,
    Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47), (90,
    Int.negSucc 79), (132, Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat
    8), (252, Int.ofNat 24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8), (462,
    Int.negSucc 7), (468, Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat
    8), (588, Int.ofNat 24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8), (798,
    Int.negSucc 7), (0, Int.ofNat 96), (1, Int.negSucc 71), (2, Int.ofNat 16), (3, Int.ofNat 16),
    (29, Int.negSucc 71), (30, Int.ofNat 48), (31, Int.negSucc 7), (32, Int.negSucc 7), (58,
    Int.ofNat 16), (59, Int.negSucc 7), (87, Int.ofNat 16), (88, Int.negSucc 7), (192, Int.negSucc
    7), (222, Int.negSucc 23), (312, Int.negSucc 7), (528, Int.negSucc 7), (558, Int.negSucc 23),
    (648, Int.negSucc 7), (528, Int.negSucc 55), (588, Int.negSucc 55), (618, Int.negSucc 55),
    (648, Int.negSucc 55), (678, Int.ofNat 56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768,
    Int.negSucc 55), (30, Int.negSucc 7), (57, Int.ofNat 8), (88, Int.ofNat 16), (115, Int.negSucc
    15), (528, Int.ofNat 8), (588, Int.ofNat 8), (738, Int.negSucc 7), (768, Int.ofNat 8), (813,
    Int.ofNat 8), (815, Int.negSucc 15), (1, Int.ofNat 8), (28, Int.negSucc 7), (30, Int.negSucc
    15), (57, Int.ofNat 16), (59, Int.ofNat 8), (86, Int.negSucc 7), (88, Int.ofNat 8), (115,
    Int.negSucc 7), (528, Int.ofNat 8), (768, Int.ofNat 8), (798, Int.negSucc 7), (812,
    Int.negSucc 7), (813, Int.ofNat 16), (814, Int.negSucc 7), (815, Int.negSucc 7), (30,
    Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat 16), (86, Int.negSucc 15), (528, Int.ofNat
    8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (1, Int.ofNat 64), (28, Int.negSucc 63), (30, Int.negSucc 31), (57, Int.ofNat
    32), (528, Int.ofNat 32), (648, Int.ofNat 32), (678, Int.negSucc 31), (768, Int.ofNat 32),
    (812, Int.negSucc 63), (813, Int.ofNat 32), (29, Int.negSucc 7), (30, Int.ofNat 8), (31,
    Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (87, Int.ofNat 16), (88, Int.negSucc
    15), (89, Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7),
    (738, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0,
    Int.ofNat 40), (1, Int.negSucc 39), (2, Int.ofNat 40), (3, Int.ofNat 40), (28, Int.negSucc
    39), (29, Int.negSucc 79), (30, Int.ofNat 80), (31, Int.negSucc 79), (32, Int.negSucc 79),
    (57, Int.ofNat 80), (58, Int.ofNat 40), (59, Int.negSucc 39), (60, Int.ofNat 40), (61,
    Int.ofNat 40), (86, Int.negSucc 39), (87, Int.ofNat 40), (88, Int.negSucc 39), (89, Int.ofNat
    40), (90, Int.ofNat 40), (115, Int.negSucc 39), (468, Int.negSucc 39), (498, Int.negSucc 39),
    (558, Int.negSucc 39), (678, Int.negSucc 39), (708, Int.negSucc 39), (738, Int.negSucc 39),
    (768, Int.ofNat 40), (812, Int.negSucc 39), (813, Int.ofNat 80), (814, Int.negSucc 39), (815,
    Int.negSucc 39), (29, Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat
    16), (57, Int.negSucc 15), (58, Int.negSucc 31), (59, Int.ofNat 32), (60, Int.negSucc 31),
    (61, Int.negSucc 31), (86, Int.ofNat 32), (498, Int.ofNat 16), (708, Int.ofNat 16), (768,
    Int.negSucc 15), (813, Int.negSucc 15), (814, Int.ofNat 32), (0, Int.ofNat 16), (1,
    Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc
    7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (558,
    Int.negSucc 7), (678, Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc 31), (28, Int.ofNat 32),
    (29, Int.negSucc 63), (31, Int.ofNat 64), (32, Int.ofNat 64), (57, Int.negSucc 63), (58,
    Int.ofNat 32), (60, Int.negSucc 31), (61, Int.negSucc 31), (86, Int.ofNat 32), (87, Int.ofNat
    32), (89, Int.negSucc 31), (90, Int.negSucc 31), (115, Int.ofNat 32), (468, Int.ofNat 32),
    (498, Int.ofNat 32), (588, Int.ofNat 32), (618, Int.ofNat 32), (812, Int.ofNat 32), (813,
    Int.negSucc 63), (814, Int.ofNat 32), (815, Int.ofNat 32), (29, Int.ofNat 8), (31, Int.negSucc
    7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.negSucc 15), (60, Int.ofNat 16), (61,
    Int.ofNat 16), (86, Int.negSucc 15), (498, Int.negSucc 7), (588, Int.negSucc 7), (678,
    Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (0, Int.negSucc 23), (2, Int.ofNat
    24), (3, Int.negSucc 23), (28, Int.ofNat 24), (29, Int.ofNat 48), (31, Int.negSucc 47), (32,
    Int.ofNat 48), (57, Int.negSucc 47), (58, Int.negSucc 23), (60, Int.ofNat 24), (61,
    Int.negSucc 23), (86, Int.ofNat 24), (87, Int.negSucc 23), (89, Int.ofNat 24), (90,
    Int.negSucc 23), (115, Int.ofNat 24), (468, Int.ofNat 24), (558, Int.ofNat 24), (588,
    Int.ofNat 24), (648, Int.ofNat 24), (812, Int.ofNat 24), (813, Int.negSucc 47), (814,
    Int.ofNat 24), (815, Int.ofNat 24), (0, Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat
    16), (28, Int.ofNat 16), (29, Int.ofNat 48), (31, Int.ofNat 48), (32, Int.negSucc 47), (57,
    Int.negSucc 47), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16), (86,
    Int.ofNat 16), (87, Int.negSucc 47), (89, Int.negSucc 47), (90, Int.ofNat 48), (115, Int.ofNat
    48), (132, Int.negSucc 15), (498, Int.ofNat 16), (558, Int.ofNat 16), (618, Int.ofNat 16),
    (648, Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (812, Int.ofNat 16), (813,
    Int.negSucc 47), (814, Int.ofNat 16), (815, Int.ofNat 48), (0, Int.negSucc 47), (2, Int.ofNat
    48), (3, Int.negSucc 47), (28, Int.ofNat 48), (29, Int.ofNat 24), (31, Int.negSucc 23), (32,
    Int.ofNat 24), (57, Int.negSucc 23), (558, Int.ofNat 24), (588, Int.ofNat 24), (708,
    Int.negSucc 23), (812, Int.ofNat 48), (813, Int.negSucc 23), (0, Int.negSucc 47), (2,
    Int.negSucc 47), (3, Int.ofNat 48), (28, Int.ofNat 48), (29, Int.ofNat 24), (31, Int.ofNat
    24), (32, Int.negSucc 23), (57, Int.negSucc 23), (558, Int.ofNat 24), (618, Int.ofNat 24),
    (738, Int.negSucc 23), (812, Int.ofNat 48), (813, Int.negSucc 23), (798, Int.ofNat 40), (813,
    Int.negSucc 39), (840, Int.ofNat 40), (768, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (814, Int.ofNat 16), (815, Int.ofNat 16), (840, Int.negSucc 31), (588,
    Int.negSucc 15), (798, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.ofNat 16), (840, Int.negSucc 31), (618, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 31), (648, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (840,
    Int.negSucc 31), (468, Int.negSucc 15), (798, Int.ofNat 16), (815, Int.negSucc 31), (840,
    Int.ofNat 32), (498, Int.negSucc 15), (798, Int.ofNat 16), (814, Int.negSucc 31), (840,
    Int.ofNat 32), (558, Int.negSucc 31), (798, Int.ofNat 32), (812, Int.negSucc 63), (840,
    Int.ofNat 64), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc 31), (28, Int.ofNat
    32), (29, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (678,
    Int.ofNat 16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813, Int.ofNat 16), (840,
    Int.negSucc 31), (798, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.negSucc 15), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (840, Int.negSucc 15), (798, Int.ofNat 8), (812, Int.ofNat
    8), (814, Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 13, mode := 3, source := [(13, Int.ofNat 2), (42, Int.negSucc 5), (71, Int.ofNat 6),
    (100, Int.ofNat 2), (155, Int.negSucc 1), (295, Int.negSucc 1), (377, Int.ofNat 2), (378,
    Int.negSucc 5), (379, Int.ofNat 6), (380, Int.ofNat 2), (422, Int.ofNat 2), (455, Int.ofNat
    2), (478, Int.ofNat 2), (595, Int.ofNat 2)],
    denominator := Int.ofNat 4,
    target := [(30, Int.negSucc 71), (32, Int.ofNat 144), (88, Int.ofNat 144), (90, Int.negSucc
    287), (132, Int.ofNat 72), (468, Int.ofNat 72), (1, Int.negSucc 27), (3, Int.ofNat 56), (29,
    Int.negSucc 27), (30, Int.ofNat 168), (31, Int.negSucc 27), (32, Int.negSucc 251), (59,
    Int.negSucc 27), (61, Int.ofNat 56), (87, Int.ofNat 56), (88, Int.negSucc 251), (89, Int.ofNat
    56), (90, Int.ofNat 336), (132, Int.negSucc 83), (192, Int.negSucc 27), (252, Int.negSucc 27),
    (468, Int.negSucc 83), (528, Int.negSucc 27), (588, Int.negSucc 27), (30, Int.negSucc 15),
    (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.ofNat 24), (1, Int.negSucc 59), (2, Int.ofNat 24), (3, Int.ofNat 48),
    (29, Int.negSucc 59), (30, Int.ofNat 144), (31, Int.negSucc 59), (32, Int.negSucc 107), (58,
    Int.ofNat 24), (59, Int.negSucc 59), (60, Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 107), (89, Int.ofNat 48), (90, Int.ofNat 72), (132, Int.negSucc 11),
    (192, Int.negSucc 35), (252, Int.negSucc 11), (468, Int.negSucc 11), (528, Int.negSucc 35),
    (588, Int.negSucc 11), (0, Int.negSucc 47), (1, Int.ofNat 144), (2, Int.negSucc 95), (3,
    Int.negSucc 95), (29, Int.ofNat 144), (30, Int.negSucc 383), (31, Int.ofNat 240), (32,
    Int.ofNat 240), (58, Int.negSucc 95), (59, Int.ofNat 240), (60, Int.negSucc 143), (61,
    Int.negSucc 143), (87, Int.negSucc 95), (88, Int.ofNat 240), (89, Int.negSucc 143), (90,
    Int.negSucc 143), (132, Int.ofNat 24), (162, Int.ofNat 24), (192, Int.ofNat 96), (252,
    Int.ofNat 24), (282, Int.ofNat 24), (468, Int.ofNat 24), (498, Int.ofNat 24), (528, Int.ofNat
    96), (588, Int.ofNat 24), (618, Int.ofNat 24), (1, Int.negSucc 7), (2, Int.ofNat 16), (29,
    Int.negSucc 7), (30, Int.ofNat 48), (31, Int.negSucc 71), (32, Int.negSucc 7), (58, Int.ofNat
    16), (59, Int.negSucc 71), (60, Int.ofNat 96), (61, Int.ofNat 16), (88, Int.negSucc 7), (89,
    Int.ofNat 16), (162, Int.negSucc 23), (192, Int.negSucc 7), (282, Int.negSucc 7), (498,
    Int.negSucc 23), (528, Int.negSucc 7), (618, Int.negSucc 7), (0, Int.ofNat 48), (1,
    Int.negSucc 79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat
    128), (31, Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47),
    (60, Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89,
    Int.ofNat 32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222,
    Int.negSucc 7), (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528,
    Int.negSucc 31), (558, Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1,
    Int.negSucc 31), (2, Int.ofNat 64), (29, Int.negSucc 31), (30, Int.ofNat 96), (31, Int.negSucc
    111), (32, Int.negSucc 31), (58, Int.ofNat 64), (59, Int.negSucc 111), (60, Int.ofNat 64),
    (61, Int.ofNat 64), (88, Int.negSucc 31), (89, Int.ofNat 64), (162, Int.negSucc 15), (192,
    Int.negSucc 31), (252, Int.negSucc 7), (282, Int.negSucc 31), (312, Int.negSucc 7), (342,
    Int.ofNat 8), (402, Int.ofNat 8), (498, Int.negSucc 15), (528, Int.negSucc 31), (588,
    Int.negSucc 7), (618, Int.negSucc 31), (648, Int.negSucc 7), (678, Int.ofNat 8), (738,
    Int.ofNat 8), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 15), (3, Int.negSucc
    47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat 112), (58,
    Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 47), (87,
    Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47), (90, Int.negSucc 79), (132,
    Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat
    24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8), (462, Int.negSucc 7), (468,
    Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat
    24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8), (798, Int.negSucc 7), (528,
    Int.negSucc 55), (588, Int.negSucc 55), (618, Int.negSucc 55), (648, Int.negSucc 55), (678,
    Int.ofNat 56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (30,
    Int.negSucc 7), (57, Int.ofNat 8), (88, Int.ofNat 16), (115, Int.negSucc 15), (528, Int.ofNat
    8), (588, Int.ofNat 8), (738, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (815,
    Int.negSucc 15), (1, Int.ofNat 8), (28, Int.negSucc 7), (30, Int.negSucc 15), (57, Int.ofNat
    16), (59, Int.ofNat 8), (86, Int.negSucc 7), (88, Int.ofNat 8), (115, Int.negSucc 7), (528,
    Int.ofNat 8), (768, Int.ofNat 8), (798, Int.negSucc 7), (812, Int.negSucc 7), (813, Int.ofNat
    16), (814, Int.negSucc 7), (815, Int.negSucc 7), (30, Int.negSucc 31), (57, Int.ofNat 32),
    (59, Int.ofNat 64), (86, Int.negSucc 63), (528, Int.ofNat 32), (618, Int.ofNat 32), (708,
    Int.negSucc 31), (768, Int.ofNat 32), (813, Int.ofNat 32), (814, Int.negSucc 63), (1,
    Int.ofNat 16), (28, Int.negSucc 15), (30, Int.negSucc 7), (57, Int.ofNat 8), (528, Int.ofNat
    8), (648, Int.ofNat 8), (678, Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813,
    Int.ofNat 8), (29, Int.negSucc 7), (30, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc
    7), (57, Int.ofNat 8), (87, Int.ofNat 16), (88, Int.negSucc 15), (89, Int.ofNat 16), (90,
    Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 7), (738, Int.negSucc 7), (768,
    Int.ofNat 8), (813, Int.ofNat 8), (815, Int.negSucc 15), (0, Int.ofNat 40), (1, Int.negSucc
    39), (2, Int.ofNat 40), (3, Int.ofNat 40), (28, Int.negSucc 39), (29, Int.negSucc 79), (30,
    Int.ofNat 80), (31, Int.negSucc 79), (32, Int.negSucc 79), (57, Int.ofNat 80), (58, Int.ofNat
    40), (59, Int.negSucc 39), (60, Int.ofNat 40), (61, Int.ofNat 40), (86, Int.negSucc 39), (87,
    Int.ofNat 40), (88, Int.negSucc 39), (89, Int.ofNat 40), (90, Int.ofNat 40), (115, Int.negSucc
    39), (468, Int.negSucc 39), (498, Int.negSucc 39), (558, Int.negSucc 39), (678, Int.negSucc
    39), (708, Int.negSucc 39), (738, Int.negSucc 39), (768, Int.ofNat 40), (812, Int.negSucc 39),
    (813, Int.ofNat 80), (814, Int.negSucc 39), (815, Int.negSucc 39), (29, Int.negSucc 7), (30,
    Int.ofNat 8), (31, Int.negSucc 7), (32, Int.negSucc 7), (57, Int.ofNat 8), (58, Int.ofNat 16),
    (59, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (498,
    Int.negSucc 7), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814,
    Int.negSucc 15), (0, Int.negSucc 31), (1, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc
    31), (28, Int.ofNat 32), (29, Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.ofNat 16), (57, Int.negSucc 15), (558, Int.ofNat 16), (678, Int.ofNat 16), (768,
    Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (0, Int.ofNat 24), (2,
    Int.negSucc 23), (3, Int.negSucc 23), (28, Int.ofNat 24), (29, Int.negSucc 47), (31, Int.ofNat
    48), (32, Int.ofNat 48), (57, Int.negSucc 47), (58, Int.ofNat 24), (60, Int.negSucc 23), (61,
    Int.negSucc 23), (86, Int.ofNat 24), (87, Int.ofNat 24), (89, Int.negSucc 23), (90,
    Int.negSucc 23), (115, Int.ofNat 24), (468, Int.ofNat 24), (498, Int.ofNat 24), (588,
    Int.ofNat 24), (618, Int.ofNat 24), (812, Int.ofNat 24), (813, Int.negSucc 47), (814,
    Int.ofNat 24), (815, Int.ofNat 24), (29, Int.negSucc 23), (31, Int.ofNat 24), (32, Int.ofNat
    24), (57, Int.negSucc 23), (58, Int.ofNat 48), (60, Int.negSucc 47), (61, Int.negSucc 47),
    (86, Int.ofNat 48), (498, Int.ofNat 24), (588, Int.ofNat 24), (678, Int.negSucc 23), (813,
    Int.negSucc 23), (814, Int.ofNat 48), (0, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.negSucc
    31), (28, Int.ofNat 32), (29, Int.ofNat 64), (31, Int.negSucc 63), (32, Int.ofNat 64), (57,
    Int.negSucc 63), (58, Int.negSucc 31), (60, Int.ofNat 32), (61, Int.negSucc 31), (86,
    Int.ofNat 32), (87, Int.negSucc 31), (89, Int.ofNat 32), (90, Int.negSucc 31), (115, Int.ofNat
    32), (468, Int.ofNat 32), (558, Int.ofNat 32), (588, Int.ofNat 32), (648, Int.ofNat 32), (812,
    Int.ofNat 32), (813, Int.negSucc 63), (814, Int.ofNat 32), (815, Int.ofNat 32), (0,
    Int.negSucc 15), (2, Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat
    48), (31, Int.ofNat 48), (32, Int.negSucc 47), (57, Int.negSucc 47), (58, Int.negSucc 15),
    (60, Int.negSucc 15), (61, Int.ofNat 16), (86, Int.ofNat 16), (87, Int.negSucc 47), (89,
    Int.negSucc 47), (90, Int.ofNat 48), (115, Int.ofNat 48), (132, Int.negSucc 15), (498,
    Int.ofNat 16), (558, Int.ofNat 16), (618, Int.ofNat 16), (648, Int.ofNat 16), (738, Int.ofNat
    16), (768, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.negSucc 47), (814, Int.ofNat 16),
    (815, Int.ofNat 48), (29, Int.ofNat 24), (31, Int.ofNat 24), (32, Int.negSucc 23), (57,
    Int.negSucc 23), (58, Int.negSucc 47), (60, Int.negSucc 47), (61, Int.ofNat 48), (86,
    Int.ofNat 48), (498, Int.ofNat 24), (648, Int.ofNat 24), (738, Int.negSucc 23), (813,
    Int.negSucc 23), (814, Int.ofNat 48), (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat
    16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
    Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc 7), (708, Int.ofNat 8), (812,
    Int.negSucc 15), (813, Int.ofNat 8), (798, Int.ofNat 40), (813, Int.negSucc 39), (840,
    Int.ofNat 40), (768, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (840, Int.negSucc 31), (588, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815,
    Int.ofNat 16), (840, Int.negSucc 31), (618, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.negSucc 15), (813, Int.ofNat 32), (814, Int.ofNat 16), (815, Int.negSucc 15), (840,
    Int.negSucc 31), (648, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (813,
    Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (840, Int.negSucc 31), (468,
    Int.negSucc 15), (798, Int.ofNat 16), (815, Int.negSucc 31), (840, Int.ofNat 32), (498,
    Int.negSucc 31), (798, Int.ofNat 32), (814, Int.negSucc 63), (840, Int.ofNat 64), (558,
    Int.negSucc 15), (798, Int.ofNat 16), (812, Int.negSucc 31), (840, Int.ofNat 32), (29,
    Int.ofNat 16), (31, Int.negSucc 15), (32, Int.ofNat 16), (57, Int.negSucc 15), (58,
    Int.negSucc 31), (60, Int.ofNat 32), (61, Int.negSucc 31), (86, Int.ofNat 32), (708, Int.ofNat
    16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813, Int.ofNat 16), (840, Int.negSucc 31),
    (798, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.negSucc 15), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.negSucc 15), (798, Int.ofNat 8), (812, Int.negSucc 7), (814,
    Int.ofNat 8), (815, Int.negSucc 7), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648, 678,
    708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 13, mode := 3, source := [(13, Int.negSucc 3), (42, Int.ofNat 6), (71, Int.negSucc
    1), (100, Int.negSucc 3), (155, Int.ofNat 2), (268, Int.negSucc 3), (295, Int.ofNat 1), (377,
    Int.negSucc 0), (379, Int.negSucc 0), (380, Int.ofNat 1), (405, Int.ofNat 1), (595, Int.ofNat
    1), (825, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 72), (32, Int.negSucc 143), (88, Int.negSucc 143), (90, Int.ofNat
    288), (132, Int.negSucc 71), (468, Int.negSucc 71), (1, Int.ofNat 12), (3, Int.negSucc 23),
    (29, Int.ofNat 12), (30, Int.negSucc 71), (31, Int.ofNat 12), (32, Int.ofNat 108), (59,
    Int.ofNat 12), (61, Int.negSucc 23), (87, Int.negSucc 23), (88, Int.ofNat 108), (89,
    Int.negSucc 23), (90, Int.negSucc 143), (132, Int.ofNat 36), (192, Int.ofNat 12), (252,
    Int.ofNat 12), (468, Int.ofNat 36), (528, Int.ofNat 12), (588, Int.ofNat 12), (30, Int.ofNat
    32), (31, Int.negSucc 31), (32, Int.negSucc 31), (59, Int.negSucc 31), (61, Int.ofNat 64),
    (88, Int.negSucc 31), (89, Int.ofNat 64), (192, Int.negSucc 15), (252, Int.negSucc 15), (282,
    Int.negSucc 15), (342, Int.ofNat 16), (528, Int.negSucc 15), (588, Int.negSucc 15), (618,
    Int.negSucc 15), (678, Int.ofNat 16), (0, Int.negSucc 31), (1, Int.ofNat 80), (2, Int.negSucc
    31), (3, Int.negSucc 63), (29, Int.ofNat 80), (30, Int.negSucc 191), (31, Int.ofNat 80), (32,
    Int.ofNat 144), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 31), (61,
    Int.negSucc 63), (87, Int.negSucc 63), (88, Int.ofNat 144), (89, Int.negSucc 63), (90,
    Int.negSucc 95), (132, Int.ofNat 16), (192, Int.ofNat 48), (252, Int.ofNat 16), (468,
    Int.ofNat 16), (528, Int.ofNat 48), (588, Int.ofNat 16), (0, Int.ofNat 32), (1, Int.negSucc
    95), (2, Int.ofNat 64), (3, Int.ofNat 64), (29, Int.negSucc 95), (30, Int.ofNat 256), (31,
    Int.negSucc 159), (32, Int.negSucc 159), (58, Int.ofNat 64), (59, Int.negSucc 159), (60,
    Int.ofNat 96), (61, Int.ofNat 96), (87, Int.ofNat 64), (88, Int.negSucc 159), (89, Int.ofNat
    96), (90, Int.ofNat 96), (132, Int.negSucc 15), (162, Int.negSucc 15), (192, Int.negSucc 63),
    (252, Int.negSucc 15), (282, Int.negSucc 15), (468, Int.negSucc 15), (498, Int.negSucc 15),
    (528, Int.negSucc 63), (588, Int.negSucc 15), (618, Int.negSucc 15), (0, Int.ofNat 72), (1,
    Int.negSucc 119), (2, Int.ofNat 48), (3, Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat
    192), (31, Int.negSucc 71), (32, Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71),
    (60, Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89,
    Int.ofNat 48), (90, Int.ofNat 72), (132, Int.negSucc 11), (192, Int.negSucc 47), (222,
    Int.negSucc 11), (252, Int.negSucc 11), (312, Int.negSucc 11), (468, Int.negSucc 11), (528,
    Int.negSucc 47), (558, Int.negSucc 11), (588, Int.negSucc 11), (648, Int.negSucc 11), (1,
    Int.ofNat 64), (2, Int.negSucc 127), (29, Int.ofNat 64), (30, Int.negSucc 191), (31, Int.ofNat
    224), (32, Int.ofNat 64), (58, Int.negSucc 127), (59, Int.ofNat 224), (60, Int.negSucc 127),
    (61, Int.negSucc 127), (88, Int.ofNat 64), (89, Int.negSucc 127), (162, Int.ofNat 32), (192,
    Int.ofNat 64), (252, Int.ofNat 16), (282, Int.ofNat 64), (312, Int.ofNat 16), (342,
    Int.negSucc 15), (402, Int.negSucc 15), (498, Int.ofNat 32), (528, Int.ofNat 64), (588,
    Int.ofNat 16), (618, Int.ofNat 64), (648, Int.ofNat 16), (678, Int.negSucc 15), (738,
    Int.negSucc 15), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc 7), (3, Int.negSucc
    7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32, Int.ofNat 4), (58,
    Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4), (192, Int.ofNat 4),
    (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558, Int.ofNat 12), (648,
    Int.ofNat 4), (528, Int.ofNat 112), (588, Int.ofNat 112), (618, Int.ofNat 112), (648,
    Int.ofNat 112), (678, Int.negSucc 111), (708, Int.negSucc 111), (738, Int.negSucc 111), (768,
    Int.ofNat 112), (30, Int.ofNat 32), (57, Int.negSucc 31), (88, Int.negSucc 63), (115,
    Int.ofNat 64), (528, Int.negSucc 31), (588, Int.negSucc 31), (738, Int.ofNat 32), (768,
    Int.negSucc 31), (813, Int.negSucc 31), (815, Int.ofNat 64), (1, Int.negSucc 39), (28,
    Int.ofNat 40), (30, Int.ofNat 80), (57, Int.negSucc 79), (59, Int.negSucc 39), (86, Int.ofNat
    40), (88, Int.negSucc 39), (115, Int.ofNat 40), (528, Int.negSucc 39), (768, Int.negSucc 39),
    (798, Int.ofNat 40), (812, Int.ofNat 40), (813, Int.negSucc 79), (814, Int.ofNat 40), (815,
    Int.ofNat 40), (30, Int.ofNat 16), (57, Int.negSucc 15), (59, Int.negSucc 31), (86, Int.ofNat
    32), (528, Int.negSucc 15), (618, Int.negSucc 15), (708, Int.ofNat 16), (768, Int.negSucc 15),
    (813, Int.negSucc 15), (814, Int.ofNat 32), (1, Int.negSucc 47), (28, Int.ofNat 48), (30,
    Int.ofNat 24), (57, Int.negSucc 23), (528, Int.negSucc 23), (648, Int.negSucc 23), (678,
    Int.ofNat 24), (768, Int.negSucc 23), (812, Int.ofNat 48), (813, Int.negSucc 23), (29,
    Int.ofNat 80), (30, Int.negSucc 79), (31, Int.ofNat 80), (32, Int.ofNat 80), (57, Int.negSucc
    79), (87, Int.negSucc 159), (88, Int.ofNat 160), (89, Int.negSucc 159), (90, Int.negSucc 159),
    (115, Int.ofNat 160), (468, Int.ofNat 80), (738, Int.ofNat 80), (768, Int.negSucc 79), (813,
    Int.negSucc 79), (815, Int.ofNat 160), (0, Int.negSucc 79), (1, Int.ofNat 80), (2, Int.negSucc
    79), (3, Int.negSucc 79), (28, Int.ofNat 80), (29, Int.ofNat 160), (30, Int.negSucc 159), (31,
    Int.ofNat 160), (32, Int.ofNat 160), (57, Int.negSucc 159), (58, Int.negSucc 79), (59,
    Int.ofNat 80), (60, Int.negSucc 79), (61, Int.negSucc 79), (86, Int.ofNat 80), (87,
    Int.negSucc 79), (88, Int.ofNat 80), (89, Int.negSucc 79), (90, Int.negSucc 79), (115,
    Int.ofNat 80), (468, Int.ofNat 80), (498, Int.ofNat 80), (558, Int.ofNat 80), (678, Int.ofNat
    80), (708, Int.ofNat 80), (738, Int.ofNat 80), (768, Int.negSucc 79), (812, Int.ofNat 80),
    (813, Int.negSucc 159), (814, Int.ofNat 80), (815, Int.ofNat 80), (29, Int.negSucc 31), (30,
    Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat
    64), (59, Int.negSucc 63), (60, Int.ofNat 64), (61, Int.ofNat 64), (86, Int.negSucc 63), (498,
    Int.negSucc 31), (708, Int.negSucc 31), (768, Int.ofNat 32), (813, Int.ofNat 32), (814,
    Int.negSucc 63), (0, Int.negSucc 31), (1, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc
    31), (28, Int.ofNat 32), (29, Int.ofNat 16), (30, Int.negSucc 15), (31, Int.ofNat 16), (32,
    Int.ofNat 16), (57, Int.negSucc 15), (558, Int.ofNat 16), (678, Int.ofNat 16), (768,
    Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 32), (31,
    Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (87, Int.negSucc 63), (89,
    Int.ofNat 64), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 31), (618,
    Int.negSucc 31), (678, Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (0,
    Int.negSucc 71), (2, Int.ofNat 72), (3, Int.ofNat 72), (28, Int.negSucc 71), (29, Int.ofNat
    144), (31, Int.negSucc 143), (32, Int.negSucc 143), (57, Int.ofNat 144), (58, Int.negSucc 71),
    (60, Int.ofNat 72), (61, Int.ofNat 72), (86, Int.negSucc 71), (87, Int.negSucc 71), (89,
    Int.ofNat 72), (90, Int.ofNat 72), (115, Int.negSucc 71), (468, Int.negSucc 71), (498,
    Int.negSucc 71), (588, Int.negSucc 71), (618, Int.negSucc 71), (812, Int.negSucc 71), (813,
    Int.ofNat 144), (814, Int.negSucc 71), (815, Int.negSucc 71), (29, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.ofNat 16), (57, Int.negSucc 15), (58, Int.ofNat 32), (60, Int.negSucc
    31), (61, Int.negSucc 31), (86, Int.ofNat 32), (498, Int.ofNat 16), (588, Int.ofNat 16), (678,
    Int.negSucc 15), (813, Int.negSucc 15), (814, Int.ofNat 32), (29, Int.negSucc 31), (31,
    Int.ofNat 32), (32, Int.negSucc 31), (57, Int.ofNat 32), (87, Int.ofNat 64), (89, Int.negSucc
    63), (90, Int.ofNat 64), (115, Int.negSucc 63), (468, Int.negSucc 31), (648, Int.negSucc 31),
    (708, Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (0, Int.ofNat 48), (2,
    Int.negSucc 47), (3, Int.ofNat 48), (28, Int.negSucc 47), (29, Int.negSucc 95), (31, Int.ofNat
    96), (32, Int.negSucc 95), (57, Int.ofNat 96), (58, Int.ofNat 48), (60, Int.negSucc 47), (61,
    Int.ofNat 48), (86, Int.negSucc 47), (87, Int.ofNat 48), (89, Int.negSucc 47), (90, Int.ofNat
    48), (115, Int.negSucc 47), (468, Int.negSucc 47), (558, Int.negSucc 47), (588, Int.negSucc
    47), (648, Int.negSucc 47), (812, Int.negSucc 47), (813, Int.ofNat 96), (814, Int.negSucc 47),
    (815, Int.negSucc 47), (0, Int.ofNat 48), (2, Int.ofNat 48), (3, Int.negSucc 47), (28,
    Int.negSucc 47), (29, Int.negSucc 143), (31, Int.negSucc 143), (32, Int.ofNat 144), (57,
    Int.ofNat 144), (58, Int.ofNat 48), (60, Int.ofNat 48), (61, Int.negSucc 47), (86, Int.negSucc
    47), (87, Int.ofNat 144), (89, Int.ofNat 144), (90, Int.negSucc 143), (115, Int.negSucc 143),
    (132, Int.ofNat 48), (498, Int.negSucc 47), (558, Int.negSucc 47), (618, Int.negSucc 47),
    (648, Int.negSucc 47), (738, Int.negSucc 47), (768, Int.ofNat 48), (812, Int.negSucc 47),
    (813, Int.ofNat 144), (814, Int.negSucc 47), (815, Int.negSucc 143), (0, Int.ofNat 32), (2,
    Int.negSucc 31), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.ofNat
    16), (32, Int.negSucc 15), (57, Int.ofNat 16), (558, Int.negSucc 15), (588, Int.negSucc 15),
    (708, Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (0, Int.ofNat 48), (2,
    Int.ofNat 48), (3, Int.negSucc 47), (28, Int.negSucc 47), (29, Int.negSucc 23), (31,
    Int.negSucc 23), (32, Int.ofNat 24), (57, Int.ofNat 24), (558, Int.negSucc 23), (618,
    Int.negSucc 23), (738, Int.ofNat 24), (812, Int.negSucc 47), (813, Int.ofNat 24), (798,
    Int.negSucc 135), (813, Int.ofNat 136), (840, Int.negSucc 135), (768, Int.ofNat 48), (798,
    Int.ofNat 48), (812, Int.negSucc 47), (814, Int.negSucc 47), (815, Int.negSucc 47), (840,
    Int.ofNat 96), (738, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (813,
    Int.ofNat 16), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.negSucc 31), (588,
    Int.ofNat 48), (798, Int.ofNat 48), (812, Int.ofNat 48), (813, Int.negSucc 95), (814,
    Int.ofNat 48), (815, Int.negSucc 47), (840, Int.ofNat 96), (618, Int.ofNat 48), (798,
    Int.ofNat 48), (812, Int.ofNat 48), (813, Int.negSucc 95), (814, Int.negSucc 47), (815,
    Int.ofNat 48), (840, Int.ofNat 96), (648, Int.ofNat 32), (798, Int.ofNat 32), (812,
    Int.negSucc 31), (813, Int.negSucc 63), (814, Int.ofNat 32), (815, Int.ofNat 32), (840,
    Int.ofNat 64), (468, Int.ofNat 72), (798, Int.negSucc 71), (815, Int.ofNat 144), (840,
    Int.negSucc 143), (498, Int.ofNat 40), (798, Int.negSucc 39), (814, Int.ofNat 80), (840,
    Int.negSucc 79), (558, Int.ofNat 40), (798, Int.negSucc 39), (812, Int.ofNat 80), (840,
    Int.negSucc 79), (29, Int.negSucc 23), (31, Int.negSucc 23), (32, Int.ofNat 24), (57,
    Int.ofNat 24), (87, Int.ofNat 48), (89, Int.ofNat 48), (90, Int.negSucc 47), (115, Int.negSucc
    47), (738, Int.negSucc 23), (768, Int.ofNat 24), (798, Int.ofNat 24), (813, Int.negSucc 23),
    (840, Int.ofNat 48), (0, Int.negSucc 47), (2, Int.ofNat 48), (3, Int.ofNat 48), (28,
    Int.negSucc 47), (29, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.negSucc 23), (57,
    Int.ofNat 24), (678, Int.negSucc 23), (768, Int.ofNat 24), (798, Int.ofNat 24), (813,
    Int.negSucc 23), (840, Int.ofNat 48), (798, Int.ofNat 48), (812, Int.negSucc 47), (813,
    Int.ofNat 48), (814, Int.negSucc 47), (815, Int.negSucc 47), (840, Int.ofNat 48), (798,
    Int.negSucc 15), (812, Int.ofNat 16), (814, Int.ofNat 16), (815, Int.negSucc 15), (840,
    Int.negSucc 15), (798, Int.ofNat 8), (812, Int.negSucc 7), (814, Int.ofNat 8), (815,
    Int.negSucc 7), (840, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat 8), (840, Int.ofNat
    8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] },
  { color := 8, mode := 3, source := [(8, Int.ofNat 1), (37, Int.negSucc 2), (66, Int.ofNat 1),
    (95, Int.ofNat 3), (122, Int.negSucc 0), (178, Int.negSucc 0), (232, Int.ofNat 1), (233,
    Int.negSucc 2), (234, Int.ofNat 1), (235, Int.ofNat 3), (336, Int.ofNat 1), (367, Int.negSucc
    0), (460, Int.negSucc 0), (504, Int.ofNat 1), (563, Int.negSucc 0), (740, Int.negSucc 0)],
    denominator := Int.ofNat 8,
    target := [(30, Int.negSucc 55), (32, Int.ofNat 112), (88, Int.ofNat 112), (90, Int.negSucc
    223), (132, Int.ofNat 56), (468, Int.ofNat 56), (1, Int.negSucc 19), (3, Int.ofNat 40), (29,
    Int.negSucc 19), (30, Int.ofNat 120), (31, Int.negSucc 19), (32, Int.negSucc 179), (59,
    Int.negSucc 19), (61, Int.ofNat 40), (87, Int.ofNat 40), (88, Int.negSucc 179), (89, Int.ofNat
    40), (90, Int.ofNat 240), (132, Int.negSucc 59), (192, Int.negSucc 19), (252, Int.negSucc 19),
    (468, Int.negSucc 59), (528, Int.negSucc 19), (588, Int.negSucc 19), (30, Int.ofNat 16), (31,
    Int.negSucc 15), (32, Int.negSucc 15), (59, Int.negSucc 15), (61, Int.ofNat 32), (88,
    Int.negSucc 15), (89, Int.ofNat 32), (192, Int.negSucc 7), (252, Int.negSucc 7), (282,
    Int.negSucc 7), (342, Int.ofNat 8), (528, Int.negSucc 7), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (678, Int.ofNat 8), (0, Int.negSucc 71), (1, Int.ofNat 180), (2, Int.negSucc
    71), (3, Int.negSucc 143), (29, Int.ofNat 180), (30, Int.negSucc 431), (31, Int.ofNat 180),
    (32, Int.ofNat 324), (58, Int.negSucc 71), (59, Int.ofNat 180), (60, Int.negSucc 71), (61,
    Int.negSucc 143), (87, Int.negSucc 143), (88, Int.ofNat 324), (89, Int.negSucc 143), (90,
    Int.negSucc 215), (132, Int.ofNat 36), (192, Int.ofNat 108), (252, Int.ofNat 36), (468,
    Int.ofNat 36), (528, Int.ofNat 108), (588, Int.ofNat 36), (0, Int.ofNat 48), (1, Int.negSucc
    143), (2, Int.ofNat 96), (3, Int.ofNat 96), (29, Int.negSucc 143), (30, Int.ofNat 384), (31,
    Int.negSucc 239), (32, Int.negSucc 239), (58, Int.ofNat 96), (59, Int.negSucc 239), (60,
    Int.ofNat 144), (61, Int.ofNat 144), (87, Int.ofNat 96), (88, Int.negSucc 239), (89, Int.ofNat
    144), (90, Int.ofNat 144), (132, Int.negSucc 23), (162, Int.negSucc 23), (192, Int.negSucc
    95), (252, Int.negSucc 23), (282, Int.negSucc 23), (468, Int.negSucc 23), (498, Int.negSucc
    23), (528, Int.negSucc 95), (588, Int.negSucc 23), (618, Int.negSucc 23), (192, Int.negSucc
    7), (252, Int.negSucc 7), (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8),
    (372, Int.ofNat 8), (402, Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588,
    Int.negSucc 7), (618, Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708,
    Int.ofNat 8), (738, Int.ofNat 8), (768, Int.negSucc 7), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 32), (2, Int.negSucc
    63), (29, Int.ofNat 32), (30, Int.negSucc 95), (31, Int.ofNat 112), (32, Int.ofNat 32), (58,
    Int.negSucc 63), (59, Int.ofNat 112), (60, Int.negSucc 63), (61, Int.negSucc 63), (88,
    Int.ofNat 32), (89, Int.negSucc 63), (162, Int.ofNat 16), (192, Int.ofNat 32), (252, Int.ofNat
    8), (282, Int.ofNat 32), (312, Int.ofNat 8), (342, Int.negSucc 7), (402, Int.negSucc 7), (498,
    Int.ofNat 16), (528, Int.ofNat 32), (588, Int.ofNat 8), (618, Int.ofNat 32), (648, Int.ofNat
    8), (678, Int.negSucc 7), (738, Int.negSucc 7), (0, Int.negSucc 15), (1, Int.ofNat 48), (2,
    Int.negSucc 15), (3, Int.negSucc 47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 112), (58, Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47),
    (90, Int.negSucc 79), (132, Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222,
    Int.ofNat 8), (252, Int.ofNat 24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8),
    (462, Int.negSucc 7), (468, Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558,
    Int.ofNat 8), (588, Int.ofNat 24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8),
    (798, Int.negSucc 7), (528, Int.negSucc 63), (588, Int.negSucc 63), (618, Int.negSucc 63),
    (648, Int.negSucc 63), (678, Int.ofNat 64), (708, Int.ofNat 64), (738, Int.ofNat 64), (768,
    Int.negSucc 63), (30, Int.negSucc 31), (57, Int.ofNat 32), (88, Int.ofNat 64), (115,
    Int.negSucc 63), (528, Int.ofNat 32), (588, Int.ofNat 32), (738, Int.negSucc 31), (768,
    Int.ofNat 32), (813, Int.ofNat 32), (815, Int.negSucc 63), (1, Int.ofNat 8), (28, Int.negSucc
    7), (30, Int.negSucc 15), (57, Int.ofNat 16), (59, Int.ofNat 8), (86, Int.negSucc 7), (88,
    Int.ofNat 8), (115, Int.negSucc 7), (528, Int.ofNat 8), (768, Int.ofNat 8), (798, Int.negSucc
    7), (812, Int.negSucc 7), (813, Int.ofNat 16), (814, Int.negSucc 7), (815, Int.negSucc 7),
    (30, Int.negSucc 7), (57, Int.ofNat 8), (59, Int.ofNat 16), (86, Int.negSucc 15), (528,
    Int.ofNat 8), (618, Int.ofNat 8), (708, Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat
    8), (814, Int.negSucc 15), (1, Int.ofNat 16), (28, Int.negSucc 15), (30, Int.negSucc 7), (57,
    Int.ofNat 8), (528, Int.ofNat 8), (648, Int.ofNat 8), (678, Int.negSucc 7), (768, Int.ofNat
    8), (812, Int.negSucc 15), (813, Int.ofNat 8), (29, Int.negSucc 39), (30, Int.ofNat 40), (31,
    Int.negSucc 39), (32, Int.negSucc 39), (57, Int.ofNat 40), (87, Int.ofNat 80), (88,
    Int.negSucc 79), (89, Int.ofNat 80), (90, Int.ofNat 80), (115, Int.negSucc 79), (468,
    Int.negSucc 39), (738, Int.negSucc 39), (768, Int.ofNat 40), (813, Int.ofNat 40), (815,
    Int.negSucc 79), (0, Int.ofNat 32), (1, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32),
    (28, Int.negSucc 31), (29, Int.negSucc 63), (30, Int.ofNat 64), (31, Int.negSucc 63), (32,
    Int.negSucc 63), (57, Int.ofNat 64), (58, Int.ofNat 32), (59, Int.negSucc 31), (60, Int.ofNat
    32), (61, Int.ofNat 32), (86, Int.negSucc 31), (87, Int.ofNat 32), (88, Int.negSucc 31), (89,
    Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 31), (498,
    Int.negSucc 31), (558, Int.negSucc 31), (678, Int.negSucc 31), (708, Int.negSucc 31), (738,
    Int.negSucc 31), (768, Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 64), (814,
    Int.negSucc 31), (815, Int.negSucc 31), (29, Int.negSucc 23), (31, Int.ofNat 24), (32,
    Int.ofNat 24), (57, Int.negSucc 23), (87, Int.ofNat 48), (89, Int.negSucc 47), (90,
    Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 24), (618, Int.ofNat 24), (678,
    Int.negSucc 23), (813, Int.negSucc 23), (815, Int.ofNat 48), (0, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (28, Int.ofNat 16), (29, Int.negSucc 31), (31, Int.ofNat
    32), (32, Int.ofNat 32), (57, Int.negSucc 31), (58, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.negSucc 15), (86, Int.ofNat 16), (87, Int.ofNat 16), (89, Int.negSucc 15), (90,
    Int.negSucc 15), (115, Int.ofNat 16), (468, Int.ofNat 16), (498, Int.ofNat 16), (588,
    Int.ofNat 16), (618, Int.ofNat 16), (812, Int.ofNat 16), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.ofNat 8),
    (57, Int.negSucc 7), (58, Int.ofNat 16), (60, Int.negSucc 15), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (498, Int.ofNat 8), (588, Int.ofNat 8), (678, Int.negSucc 7), (813, Int.negSucc
    7), (814, Int.ofNat 16), (29, Int.ofNat 24), (31, Int.negSucc 23), (32, Int.ofNat 24), (57,
    Int.negSucc 23), (87, Int.negSucc 47), (89, Int.ofNat 48), (90, Int.negSucc 47), (115,
    Int.ofNat 48), (468, Int.ofNat 24), (648, Int.ofNat 24), (708, Int.negSucc 23), (813,
    Int.negSucc 23), (815, Int.ofNat 48), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc
    15), (28, Int.ofNat 16), (29, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.ofNat 32), (57,
    Int.negSucc 31), (58, Int.negSucc 15), (60, Int.ofNat 16), (61, Int.negSucc 15), (86,
    Int.ofNat 16), (87, Int.negSucc 15), (89, Int.ofNat 16), (90, Int.negSucc 15), (115, Int.ofNat
    16), (468, Int.ofNat 16), (558, Int.ofNat 16), (588, Int.ofNat 16), (648, Int.ofNat 16), (812,
    Int.ofNat 16), (813, Int.negSucc 31), (814, Int.ofNat 16), (815, Int.ofNat 16), (0,
    Int.negSucc 31), (2, Int.negSucc 31), (3, Int.ofNat 32), (28, Int.ofNat 32), (29, Int.ofNat
    96), (31, Int.ofNat 96), (32, Int.negSucc 95), (57, Int.negSucc 95), (58, Int.negSucc 31),
    (60, Int.negSucc 31), (61, Int.ofNat 32), (86, Int.ofNat 32), (87, Int.negSucc 95), (89,
    Int.negSucc 95), (90, Int.ofNat 96), (115, Int.ofNat 96), (132, Int.negSucc 31), (498,
    Int.ofNat 32), (558, Int.ofNat 32), (618, Int.ofNat 32), (648, Int.ofNat 32), (738, Int.ofNat
    32), (768, Int.negSucc 31), (812, Int.ofNat 32), (813, Int.negSucc 95), (814, Int.ofNat 32),
    (815, Int.ofNat 96), (0, Int.negSucc 15), (2, Int.ofNat 16), (3, Int.negSucc 15), (28,
    Int.ofNat 16), (29, Int.ofNat 8), (31, Int.negSucc 7), (32, Int.ofNat 8), (57, Int.negSucc 7),
    (558, Int.ofNat 8), (588, Int.ofNat 8), (708, Int.negSucc 7), (812, Int.ofNat 16), (813,
    Int.negSucc 7), (798, Int.ofNat 40), (813, Int.negSucc 39), (840, Int.ofNat 40), (768,
    Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (814, Int.ofNat 16), (815,
    Int.ofNat 16), (840, Int.negSucc 31), (588, Int.negSucc 15), (798, Int.negSucc 15), (812,
    Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15), (815, Int.ofNat 16), (840,
    Int.negSucc 31), (618, Int.negSucc 15), (798, Int.negSucc 15), (812, Int.negSucc 15), (813,
    Int.ofNat 32), (814, Int.ofNat 16), (815, Int.negSucc 15), (840, Int.negSucc 31), (648,
    Int.negSucc 15), (798, Int.negSucc 15), (812, Int.ofNat 16), (813, Int.ofNat 32), (814,
    Int.negSucc 15), (815, Int.negSucc 15), (840, Int.negSucc 31), (468, Int.negSucc 31), (798,
    Int.ofNat 32), (815, Int.negSucc 63), (840, Int.ofNat 64), (498, Int.negSucc 15), (798,
    Int.ofNat 16), (814, Int.negSucc 31), (840, Int.ofNat 32), (558, Int.negSucc 15), (798,
    Int.ofNat 16), (812, Int.negSucc 31), (840, Int.ofNat 32), (29, Int.ofNat 16), (31, Int.ofNat
    16), (32, Int.negSucc 15), (57, Int.negSucc 15), (87, Int.negSucc 31), (89, Int.negSucc 31),
    (90, Int.ofNat 32), (115, Int.ofNat 32), (738, Int.ofNat 16), (768, Int.negSucc 15), (798,
    Int.negSucc 15), (813, Int.ofNat 16), (840, Int.negSucc 31), (798, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.negSucc 15), (814, Int.ofNat 16), (815, Int.ofNat 16), (840,
    Int.negSucc 15), (798, Int.ofNat 8), (812, Int.negSucc 7), (814, Int.negSucc 7), (815,
    Int.ofNat 8), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 13, mode := 2, source := [(13, Int.negSucc 3), (42, Int.ofNat 6), (71, Int.negSucc
    1), (100, Int.negSucc 3), (155, Int.ofNat 2), (268, Int.negSucc 3), (295, Int.ofNat 1), (377,
    Int.negSucc 0), (379, Int.negSucc 0), (380, Int.ofNat 1), (405, Int.ofNat 1), (595, Int.ofNat
    1), (825, Int.ofNat 1)],
    denominator := Int.ofNat 8,
    target := [(30, Int.ofNat 56), (32, Int.negSucc 111), (88, Int.negSucc 111), (90, Int.ofNat
    224), (132, Int.negSucc 55), (468, Int.negSucc 55), (1, Int.ofNat 12), (3, Int.negSucc 23),
    (29, Int.ofNat 12), (30, Int.negSucc 71), (31, Int.ofNat 12), (32, Int.ofNat 108), (59,
    Int.ofNat 12), (61, Int.negSucc 23), (87, Int.negSucc 23), (88, Int.ofNat 108), (89,
    Int.negSucc 23), (90, Int.negSucc 143), (132, Int.ofNat 36), (192, Int.ofNat 12), (252,
    Int.ofNat 12), (468, Int.ofNat 36), (528, Int.ofNat 12), (588, Int.ofNat 12), (30, Int.ofNat
    32), (31, Int.negSucc 31), (32, Int.negSucc 31), (59, Int.negSucc 31), (61, Int.ofNat 64),
    (88, Int.negSucc 31), (89, Int.ofNat 64), (192, Int.negSucc 15), (252, Int.negSucc 15), (282,
    Int.negSucc 15), (342, Int.ofNat 16), (528, Int.negSucc 15), (588, Int.negSucc 15), (618,
    Int.negSucc 15), (678, Int.ofNat 16), (0, Int.negSucc 31), (1, Int.ofNat 80), (2, Int.negSucc
    31), (3, Int.negSucc 63), (29, Int.ofNat 80), (30, Int.negSucc 191), (31, Int.ofNat 80), (32,
    Int.ofNat 144), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 31), (61,
    Int.negSucc 63), (87, Int.negSucc 63), (88, Int.ofNat 144), (89, Int.negSucc 63), (90,
    Int.negSucc 95), (132, Int.ofNat 16), (192, Int.ofNat 48), (252, Int.ofNat 16), (468,
    Int.ofNat 16), (528, Int.ofNat 48), (588, Int.ofNat 16), (0, Int.ofNat 32), (1, Int.negSucc
    95), (2, Int.ofNat 64), (3, Int.ofNat 64), (29, Int.negSucc 95), (30, Int.ofNat 256), (31,
    Int.negSucc 159), (32, Int.negSucc 159), (58, Int.ofNat 64), (59, Int.negSucc 159), (60,
    Int.ofNat 96), (61, Int.ofNat 96), (87, Int.ofNat 64), (88, Int.negSucc 159), (89, Int.ofNat
    96), (90, Int.ofNat 96), (132, Int.negSucc 15), (162, Int.negSucc 15), (192, Int.negSucc 63),
    (252, Int.negSucc 15), (282, Int.negSucc 15), (468, Int.negSucc 15), (498, Int.negSucc 15),
    (528, Int.negSucc 63), (588, Int.negSucc 15), (618, Int.negSucc 15), (0, Int.ofNat 72), (1,
    Int.negSucc 119), (2, Int.ofNat 48), (3, Int.ofNat 72), (29, Int.negSucc 119), (30, Int.ofNat
    192), (31, Int.negSucc 71), (32, Int.negSucc 119), (58, Int.ofNat 48), (59, Int.negSucc 71),
    (60, Int.ofNat 24), (61, Int.ofNat 48), (87, Int.ofNat 72), (88, Int.negSucc 119), (89,
    Int.ofNat 48), (90, Int.ofNat 72), (132, Int.negSucc 11), (192, Int.negSucc 47), (222,
    Int.negSucc 11), (252, Int.negSucc 11), (312, Int.negSucc 11), (468, Int.negSucc 11), (528,
    Int.negSucc 47), (558, Int.negSucc 11), (588, Int.negSucc 11), (648, Int.negSucc 11), (1,
    Int.ofNat 64), (2, Int.negSucc 127), (29, Int.ofNat 64), (30, Int.negSucc 191), (31, Int.ofNat
    224), (32, Int.ofNat 64), (58, Int.negSucc 127), (59, Int.ofNat 224), (60, Int.negSucc 127),
    (61, Int.negSucc 127), (88, Int.ofNat 64), (89, Int.negSucc 127), (162, Int.ofNat 32), (192,
    Int.ofNat 64), (252, Int.ofNat 16), (282, Int.ofNat 64), (312, Int.ofNat 16), (342,
    Int.negSucc 15), (402, Int.negSucc 15), (498, Int.ofNat 32), (528, Int.ofNat 64), (588,
    Int.ofNat 16), (618, Int.ofNat 64), (648, Int.ofNat 16), (678, Int.negSucc 15), (738,
    Int.negSucc 15), (0, Int.negSucc 47), (1, Int.ofNat 36), (2, Int.negSucc 7), (3, Int.negSucc
    7), (29, Int.ofNat 36), (30, Int.negSucc 23), (31, Int.ofNat 4), (32, Int.ofNat 4), (58,
    Int.negSucc 7), (59, Int.ofNat 4), (87, Int.negSucc 7), (88, Int.ofNat 4), (192, Int.ofNat 4),
    (222, Int.ofNat 12), (312, Int.ofNat 4), (528, Int.ofNat 4), (558, Int.ofNat 12), (648,
    Int.ofNat 4), (528, Int.ofNat 80), (588, Int.ofNat 80), (618, Int.ofNat 80), (648, Int.ofNat
    80), (678, Int.negSucc 79), (708, Int.negSucc 79), (738, Int.negSucc 79), (768, Int.ofNat 80),
    (30, Int.ofNat 24), (57, Int.negSucc 23), (88, Int.negSucc 47), (115, Int.ofNat 48), (528,
    Int.negSucc 23), (588, Int.negSucc 23), (738, Int.ofNat 24), (768, Int.negSucc 23), (813,
    Int.negSucc 23), (815, Int.ofNat 48), (1, Int.negSucc 23), (28, Int.ofNat 24), (30, Int.ofNat
    48), (57, Int.negSucc 47), (59, Int.negSucc 23), (86, Int.ofNat 24), (88, Int.negSucc 23),
    (115, Int.ofNat 24), (528, Int.negSucc 23), (768, Int.negSucc 23), (798, Int.ofNat 24), (812,
    Int.ofNat 24), (813, Int.negSucc 47), (814, Int.ofNat 24), (815, Int.ofNat 24), (30, Int.ofNat
    16), (57, Int.negSucc 15), (59, Int.negSucc 31), (86, Int.ofNat 32), (528, Int.negSucc 15),
    (618, Int.negSucc 15), (708, Int.ofNat 16), (768, Int.negSucc 15), (813, Int.negSucc 15),
    (814, Int.ofNat 32), (1, Int.negSucc 31), (28, Int.ofNat 32), (30, Int.ofNat 16), (57,
    Int.negSucc 15), (528, Int.negSucc 15), (648, Int.negSucc 15), (678, Int.ofNat 16), (768,
    Int.negSucc 15), (812, Int.ofNat 32), (813, Int.negSucc 15), (29, Int.ofNat 56), (30,
    Int.negSucc 55), (31, Int.ofNat 56), (32, Int.ofNat 56), (57, Int.negSucc 55), (87,
    Int.negSucc 111), (88, Int.ofNat 112), (89, Int.negSucc 111), (90, Int.negSucc 111), (115,
    Int.ofNat 112), (468, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (813,
    Int.negSucc 55), (815, Int.ofNat 112), (0, Int.negSucc 63), (1, Int.ofNat 64), (2, Int.negSucc
    63), (3, Int.negSucc 63), (28, Int.ofNat 64), (29, Int.ofNat 128), (30, Int.negSucc 127), (31,
    Int.ofNat 128), (32, Int.ofNat 128), (57, Int.negSucc 127), (58, Int.negSucc 63), (59,
    Int.ofNat 64), (60, Int.negSucc 63), (61, Int.negSucc 63), (86, Int.ofNat 64), (87,
    Int.negSucc 63), (88, Int.ofNat 64), (89, Int.negSucc 63), (90, Int.negSucc 63), (115,
    Int.ofNat 64), (468, Int.ofNat 64), (498, Int.ofNat 64), (558, Int.ofNat 64), (678, Int.ofNat
    64), (708, Int.ofNat 64), (738, Int.ofNat 64), (768, Int.negSucc 63), (812, Int.ofNat 64),
    (813, Int.negSucc 127), (814, Int.ofNat 64), (815, Int.ofNat 64), (29, Int.negSucc 31), (30,
    Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat
    64), (59, Int.negSucc 63), (60, Int.ofNat 64), (61, Int.ofNat 64), (86, Int.negSucc 63), (498,
    Int.negSucc 31), (708, Int.negSucc 31), (768, Int.ofNat 32), (813, Int.ofNat 32), (814,
    Int.negSucc 63), (0, Int.negSucc 15), (1, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.negSucc
    15), (28, Int.ofNat 16), (29, Int.ofNat 8), (30, Int.negSucc 7), (31, Int.ofNat 8), (32,
    Int.ofNat 8), (57, Int.negSucc 7), (558, Int.ofNat 8), (678, Int.ofNat 8), (768, Int.negSucc
    7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat 24), (31, Int.negSucc 23), (32,
    Int.negSucc 23), (57, Int.ofNat 24), (87, Int.negSucc 47), (89, Int.ofNat 48), (90, Int.ofNat
    48), (115, Int.negSucc 47), (468, Int.negSucc 23), (618, Int.negSucc 23), (678, Int.ofNat 24),
    (813, Int.ofNat 24), (815, Int.negSucc 47), (0, Int.negSucc 55), (2, Int.ofNat 56), (3,
    Int.ofNat 56), (28, Int.negSucc 55), (29, Int.ofNat 112), (31, Int.negSucc 111), (32,
    Int.negSucc 111), (57, Int.ofNat 112), (58, Int.negSucc 55), (60, Int.ofNat 56), (61,
    Int.ofNat 56), (86, Int.negSucc 55), (87, Int.negSucc 55), (89, Int.ofNat 56), (90, Int.ofNat
    56), (115, Int.negSucc 55), (468, Int.negSucc 55), (498, Int.negSucc 55), (588, Int.negSucc
    55), (618, Int.negSucc 55), (812, Int.negSucc 55), (813, Int.ofNat 112), (814, Int.negSucc
    55), (815, Int.negSucc 55), (29, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (57,
    Int.negSucc 15), (58, Int.ofNat 32), (60, Int.negSucc 31), (61, Int.negSucc 31), (86,
    Int.ofNat 32), (498, Int.ofNat 16), (588, Int.ofNat 16), (678, Int.negSucc 15), (813,
    Int.negSucc 15), (814, Int.ofNat 32), (29, Int.negSucc 23), (31, Int.ofNat 24), (32,
    Int.negSucc 23), (57, Int.ofNat 24), (87, Int.ofNat 48), (89, Int.negSucc 47), (90, Int.ofNat
    48), (115, Int.negSucc 47), (468, Int.negSucc 23), (648, Int.negSucc 23), (708, Int.ofNat 24),
    (813, Int.ofNat 24), (815, Int.negSucc 47), (0, Int.ofNat 32), (2, Int.negSucc 31), (3,
    Int.ofNat 32), (28, Int.negSucc 31), (29, Int.negSucc 63), (31, Int.ofNat 64), (32,
    Int.negSucc 63), (57, Int.ofNat 64), (58, Int.ofNat 32), (60, Int.negSucc 31), (61, Int.ofNat
    32), (86, Int.negSucc 31), (87, Int.ofNat 32), (89, Int.negSucc 31), (90, Int.ofNat 32), (115,
    Int.negSucc 31), (468, Int.negSucc 31), (558, Int.negSucc 31), (588, Int.negSucc 31), (648,
    Int.negSucc 31), (812, Int.negSucc 31), (813, Int.ofNat 64), (814, Int.negSucc 31), (815,
    Int.negSucc 31), (0, Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc 31), (28, Int.negSucc
    31), (29, Int.negSucc 95), (31, Int.negSucc 95), (32, Int.ofNat 96), (57, Int.ofNat 96), (58,
    Int.ofNat 32), (60, Int.ofNat 32), (61, Int.negSucc 31), (86, Int.negSucc 31), (87, Int.ofNat
    96), (89, Int.ofNat 96), (90, Int.negSucc 95), (115, Int.negSucc 95), (132, Int.ofNat 32),
    (498, Int.negSucc 31), (558, Int.negSucc 31), (618, Int.negSucc 31), (648, Int.negSucc 31),
    (738, Int.negSucc 31), (768, Int.ofNat 32), (812, Int.negSucc 31), (813, Int.ofNat 96), (814,
    Int.negSucc 31), (815, Int.negSucc 95), (0, Int.ofNat 16), (2, Int.negSucc 15), (3, Int.ofNat
    16), (28, Int.negSucc 15), (29, Int.negSucc 7), (31, Int.ofNat 8), (32, Int.negSucc 7), (57,
    Int.ofNat 8), (558, Int.negSucc 7), (588, Int.negSucc 7), (708, Int.ofNat 8), (812,
    Int.negSucc 15), (813, Int.ofNat 8), (0, Int.ofNat 32), (2, Int.ofNat 32), (3, Int.negSucc
    31), (28, Int.negSucc 31), (29, Int.negSucc 15), (31, Int.negSucc 15), (32, Int.ofNat 16),
    (57, Int.ofNat 16), (558, Int.negSucc 15), (618, Int.negSucc 15), (738, Int.ofNat 16), (812,
    Int.negSucc 31), (813, Int.ofNat 16), (798, Int.negSucc 87), (813, Int.ofNat 88), (840,
    Int.negSucc 87), (768, Int.ofNat 32), (798, Int.ofNat 32), (812, Int.negSucc 31), (814,
    Int.negSucc 31), (815, Int.negSucc 31), (840, Int.ofNat 64), (738, Int.negSucc 15), (798,
    Int.negSucc 15), (812, Int.ofNat 16), (813, Int.ofNat 16), (814, Int.ofNat 16), (815,
    Int.negSucc 15), (840, Int.negSucc 31), (588, Int.ofNat 32), (798, Int.ofNat 32), (812,
    Int.ofNat 32), (813, Int.negSucc 63), (814, Int.ofNat 32), (815, Int.negSucc 31), (840,
    Int.ofNat 64), (618, Int.ofNat 32), (798, Int.ofNat 32), (812, Int.ofNat 32), (813,
    Int.negSucc 63), (814, Int.negSucc 31), (815, Int.ofNat 32), (840, Int.ofNat 64), (648,
    Int.ofNat 16), (798, Int.ofNat 16), (812, Int.negSucc 15), (813, Int.negSucc 31), (814,
    Int.ofNat 16), (815, Int.ofNat 16), (840, Int.ofNat 32), (468, Int.ofNat 48), (798,
    Int.negSucc 47), (815, Int.ofNat 96), (840, Int.negSucc 95), (498, Int.ofNat 24), (798,
    Int.negSucc 23), (814, Int.ofNat 48), (840, Int.negSucc 47), (558, Int.ofNat 16), (798,
    Int.negSucc 15), (812, Int.ofNat 32), (840, Int.negSucc 31), (29, Int.negSucc 15), (31,
    Int.negSucc 15), (32, Int.ofNat 16), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.ofNat
    32), (90, Int.negSucc 31), (115, Int.negSucc 31), (738, Int.negSucc 15), (768, Int.ofNat 16),
    (798, Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32), (0, Int.negSucc 31), (2,
    Int.ofNat 32), (3, Int.ofNat 32), (28, Int.negSucc 31), (29, Int.ofNat 16), (31, Int.negSucc
    15), (32, Int.negSucc 15), (57, Int.ofNat 16), (678, Int.negSucc 15), (768, Int.ofNat 16),
    (798, Int.ofNat 16), (813, Int.negSucc 15), (840, Int.ofNat 32), (798, Int.ofNat 24), (812,
    Int.negSucc 23), (813, Int.ofNat 24), (814, Int.negSucc 23), (815, Int.negSucc 23), (840,
    Int.ofNat 24), (798, Int.negSucc 7), (812, Int.ofNat 8), (814, Int.ofNat 8), (815, Int.negSucc
    7), (840, Int.negSucc 7), (798, Int.ofNat 8), (812, Int.negSucc 7), (814, Int.ofNat 8), (815,
    Int.negSucc 7), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] },
  { color := 15, mode := 1, source := [(15, Int.ofNat 2), (44, Int.negSucc 5), (73, Int.ofNat 2),
    (102, Int.ofNat 6), (188, Int.negSucc 3), (245, Int.negSucc 2), (273, Int.negSucc 0), (301,
    Int.negSucc 0), (412, Int.negSucc 0), (436, Int.negSucc 0), (463, Int.ofNat 1), (827,
    Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.negSucc 47), (32, Int.ofNat 96), (88, Int.ofNat 96), (90, Int.negSucc
    191), (132, Int.ofNat 48), (468, Int.ofNat 48), (1, Int.negSucc 19), (3, Int.ofNat 40), (29,
    Int.negSucc 19), (30, Int.ofNat 120), (31, Int.negSucc 19), (32, Int.negSucc 179), (59,
    Int.negSucc 19), (61, Int.ofNat 40), (87, Int.ofNat 40), (88, Int.negSucc 179), (89, Int.ofNat
    40), (90, Int.ofNat 240), (132, Int.negSucc 59), (192, Int.negSucc 19), (252, Int.negSucc 19),
    (468, Int.negSucc 59), (528, Int.negSucc 19), (588, Int.negSucc 19), (0, Int.negSucc 55), (1,
    Int.ofNat 140), (2, Int.negSucc 55), (3, Int.negSucc 111), (29, Int.ofNat 140), (30,
    Int.negSucc 335), (31, Int.ofNat 140), (32, Int.ofNat 252), (58, Int.negSucc 55), (59,
    Int.ofNat 140), (60, Int.negSucc 55), (61, Int.negSucc 111), (87, Int.negSucc 111), (88,
    Int.ofNat 252), (89, Int.negSucc 111), (90, Int.negSucc 167), (132, Int.ofNat 28), (192,
    Int.ofNat 84), (252, Int.ofNat 28), (468, Int.ofNat 28), (528, Int.ofNat 84), (588, Int.ofNat
    28), (0, Int.ofNat 32), (1, Int.negSucc 95), (2, Int.ofNat 64), (3, Int.ofNat 64), (29,
    Int.negSucc 95), (30, Int.ofNat 256), (31, Int.negSucc 159), (32, Int.negSucc 159), (58,
    Int.ofNat 64), (59, Int.negSucc 159), (60, Int.ofNat 96), (61, Int.ofNat 96), (87, Int.ofNat
    64), (88, Int.negSucc 159), (89, Int.ofNat 96), (90, Int.ofNat 96), (132, Int.negSucc 15),
    (162, Int.negSucc 15), (192, Int.negSucc 63), (252, Int.negSucc 15), (282, Int.negSucc 15),
    (468, Int.negSucc 15), (498, Int.negSucc 15), (528, Int.negSucc 63), (588, Int.negSucc 15),
    (618, Int.negSucc 15), (1, Int.ofNat 8), (3, Int.negSucc 15), (29, Int.ofNat 8), (30,
    Int.negSucc 7), (32, Int.ofNat 8), (87, Int.negSucc 15), (88, Int.ofNat 8), (192, Int.ofNat
    4), (252, Int.ofNat 4), (312, Int.ofNat 4), (372, Int.negSucc 3), (528, Int.ofNat 4), (588,
    Int.ofNat 4), (648, Int.ofNat 4), (708, Int.negSucc 3), (192, Int.negSucc 3), (252,
    Int.negSucc 3), (282, Int.negSucc 3), (312, Int.negSucc 3), (342, Int.ofNat 4), (372,
    Int.ofNat 4), (402, Int.ofNat 4), (432, Int.negSucc 3), (528, Int.negSucc 3), (588,
    Int.negSucc 3), (618, Int.negSucc 3), (648, Int.negSucc 3), (678, Int.ofNat 4), (708,
    Int.ofNat 4), (738, Int.ofNat 4), (768, Int.negSucc 3), (0, Int.ofNat 48), (1, Int.negSucc
    79), (2, Int.ofNat 32), (3, Int.ofNat 48), (29, Int.negSucc 79), (30, Int.ofNat 128), (31,
    Int.negSucc 47), (32, Int.negSucc 79), (58, Int.ofNat 32), (59, Int.negSucc 47), (60,
    Int.ofNat 16), (61, Int.ofNat 32), (87, Int.ofNat 48), (88, Int.negSucc 79), (89, Int.ofNat
    32), (90, Int.ofNat 48), (132, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7),
    (252, Int.negSucc 7), (312, Int.negSucc 7), (468, Int.negSucc 7), (528, Int.negSucc 31), (558,
    Int.negSucc 7), (588, Int.negSucc 7), (648, Int.negSucc 7), (1, Int.ofNat 16), (2, Int.negSucc
    31), (29, Int.ofNat 16), (30, Int.negSucc 47), (31, Int.ofNat 56), (32, Int.ofNat 16), (58,
    Int.negSucc 31), (59, Int.ofNat 56), (60, Int.negSucc 31), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (162, Int.ofNat 8), (192, Int.ofNat 16), (252, Int.ofNat
    4), (282, Int.ofNat 16), (312, Int.ofNat 4), (342, Int.negSucc 3), (402, Int.negSucc 3), (498,
    Int.ofNat 8), (528, Int.ofNat 16), (588, Int.ofNat 4), (618, Int.ofNat 16), (648, Int.ofNat
    4), (678, Int.negSucc 3), (738, Int.negSucc 3), (0, Int.negSucc 15), (1, Int.ofNat 48), (2,
    Int.negSucc 15), (3, Int.negSucc 47), (29, Int.ofNat 48), (30, Int.negSucc 127), (31,
    Int.ofNat 48), (32, Int.ofNat 112), (58, Int.negSucc 15), (59, Int.ofNat 48), (60, Int.negSucc
    15), (61, Int.negSucc 47), (87, Int.negSucc 47), (88, Int.ofNat 112), (89, Int.negSucc 47),
    (90, Int.negSucc 79), (132, Int.ofNat 24), (162, Int.ofNat 8), (192, Int.ofNat 32), (222,
    Int.ofNat 8), (252, Int.ofNat 24), (282, Int.ofNat 8), (312, Int.ofNat 8), (432, Int.ofNat 8),
    (462, Int.negSucc 7), (468, Int.ofNat 24), (498, Int.ofNat 8), (528, Int.ofNat 32), (558,
    Int.ofNat 8), (588, Int.ofNat 24), (618, Int.ofNat 8), (648, Int.ofNat 8), (768, Int.ofNat 8),
    (798, Int.negSucc 7), (528, Int.negSucc 55), (588, Int.negSucc 55), (618, Int.negSucc 55),
    (648, Int.negSucc 55), (678, Int.ofNat 56), (708, Int.ofNat 56), (738, Int.ofNat 56), (768,
    Int.negSucc 55), (30, Int.negSucc 23), (57, Int.ofNat 24), (88, Int.ofNat 48), (115,
    Int.negSucc 47), (528, Int.ofNat 24), (588, Int.ofNat 24), (738, Int.negSucc 23), (768,
    Int.ofNat 24), (813, Int.ofNat 24), (815, Int.negSucc 47), (30, Int.negSucc 7), (57, Int.ofNat
    8), (59, Int.ofNat 16), (86, Int.negSucc 15), (528, Int.ofNat 8), (618, Int.ofNat 8), (708,
    Int.negSucc 7), (768, Int.ofNat 8), (813, Int.ofNat 8), (814, Int.negSucc 15), (1, Int.ofNat
    16), (28, Int.negSucc 15), (30, Int.negSucc 7), (57, Int.ofNat 8), (528, Int.ofNat 8), (648,
    Int.ofNat 8), (678, Int.negSucc 7), (768, Int.ofNat 8), (812, Int.negSucc 15), (813, Int.ofNat
    8), (29, Int.negSucc 31), (30, Int.ofNat 32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57,
    Int.ofNat 32), (87, Int.ofNat 64), (88, Int.negSucc 63), (89, Int.ofNat 64), (90, Int.ofNat
    64), (115, Int.negSucc 63), (468, Int.negSucc 31), (738, Int.negSucc 31), (768, Int.ofNat 32),
    (813, Int.ofNat 32), (815, Int.negSucc 63), (0, Int.ofNat 24), (1, Int.negSucc 23), (2,
    Int.ofNat 24), (3, Int.ofNat 24), (28, Int.negSucc 23), (29, Int.negSucc 47), (30, Int.ofNat
    48), (31, Int.negSucc 47), (32, Int.negSucc 47), (57, Int.ofNat 48), (58, Int.ofNat 24), (59,
    Int.negSucc 23), (60, Int.ofNat 24), (61, Int.ofNat 24), (86, Int.negSucc 23), (87, Int.ofNat
    24), (88, Int.negSucc 23), (89, Int.ofNat 24), (90, Int.ofNat 24), (115, Int.negSucc 23),
    (468, Int.negSucc 23), (498, Int.negSucc 23), (558, Int.negSucc 23), (678, Int.negSucc 23),
    (708, Int.negSucc 23), (738, Int.negSucc 23), (768, Int.ofNat 24), (812, Int.negSucc 23),
    (813, Int.ofNat 48), (814, Int.negSucc 23), (815, Int.negSucc 23), (29, Int.negSucc 19), (31,
    Int.ofNat 20), (32, Int.ofNat 20), (57, Int.negSucc 19), (87, Int.ofNat 40), (89, Int.negSucc
    39), (90, Int.negSucc 39), (115, Int.ofNat 40), (468, Int.ofNat 20), (618, Int.ofNat 20),
    (678, Int.negSucc 19), (813, Int.negSucc 19), (815, Int.ofNat 40), (0, Int.ofNat 8), (2,
    Int.negSucc 7), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.negSucc 15), (31, Int.ofNat
    16), (32, Int.ofNat 16), (57, Int.negSucc 15), (58, Int.ofNat 8), (60, Int.negSucc 7), (61,
    Int.negSucc 7), (86, Int.ofNat 8), (87, Int.ofNat 8), (89, Int.negSucc 7), (90, Int.negSucc
    7), (115, Int.ofNat 8), (468, Int.ofNat 8), (498, Int.ofNat 8), (588, Int.ofNat 8), (618,
    Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat 8), (815, Int.ofNat
    8), (29, Int.negSucc 3), (31, Int.ofNat 4), (32, Int.ofNat 4), (57, Int.negSucc 3), (58,
    Int.ofNat 8), (60, Int.negSucc 7), (61, Int.negSucc 7), (86, Int.ofNat 8), (498, Int.ofNat 4),
    (588, Int.ofNat 4), (678, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat 8), (29,
    Int.ofNat 20), (31, Int.negSucc 19), (32, Int.ofNat 20), (57, Int.negSucc 19), (87,
    Int.negSucc 39), (89, Int.ofNat 40), (90, Int.negSucc 39), (115, Int.ofNat 40), (468,
    Int.ofNat 20), (648, Int.ofNat 20), (708, Int.negSucc 19), (813, Int.negSucc 19), (815,
    Int.ofNat 40), (0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8),
    (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.ofNat 16), (57, Int.negSucc 15), (58,
    Int.negSucc 7), (60, Int.ofNat 8), (61, Int.negSucc 7), (86, Int.ofNat 8), (87, Int.negSucc
    7), (89, Int.ofNat 8), (90, Int.negSucc 7), (115, Int.ofNat 8), (468, Int.ofNat 8), (558,
    Int.ofNat 8), (588, Int.ofNat 8), (648, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc
    15), (814, Int.ofNat 8), (815, Int.ofNat 8), (0, Int.negSucc 15), (2, Int.negSucc 15), (3,
    Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat 48), (31, Int.ofNat 48), (32, Int.negSucc
    47), (57, Int.negSucc 47), (58, Int.negSucc 15), (60, Int.negSucc 15), (61, Int.ofNat 16),
    (86, Int.ofNat 16), (87, Int.negSucc 47), (89, Int.negSucc 47), (90, Int.ofNat 48), (115,
    Int.ofNat 48), (132, Int.negSucc 15), (498, Int.ofNat 16), (558, Int.ofNat 16), (618,
    Int.ofNat 16), (648, Int.ofNat 16), (738, Int.ofNat 16), (768, Int.negSucc 15), (812,
    Int.ofNat 16), (813, Int.negSucc 47), (814, Int.ofNat 16), (815, Int.ofNat 48), (29, Int.ofNat
    4), (31, Int.ofNat 4), (32, Int.negSucc 3), (57, Int.negSucc 3), (58, Int.negSucc 7), (60,
    Int.negSucc 7), (61, Int.ofNat 8), (86, Int.ofNat 8), (498, Int.ofNat 4), (648, Int.ofNat 4),
    (738, Int.negSucc 3), (813, Int.negSucc 3), (814, Int.ofNat 8), (0, Int.negSucc 7), (2,
    Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.negSucc 3),
    (32, Int.ofNat 4), (57, Int.negSucc 3), (558, Int.ofNat 4), (588, Int.ofNat 4), (708,
    Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3), (0, Int.negSucc 7), (2, Int.negSucc
    7), (3, Int.ofNat 8), (28, Int.ofNat 8), (29, Int.ofNat 4), (31, Int.ofNat 4), (32,
    Int.negSucc 3), (57, Int.negSucc 3), (558, Int.ofNat 4), (618, Int.ofNat 4), (738, Int.negSucc
    3), (812, Int.ofNat 8), (813, Int.negSucc 3), (798, Int.ofNat 8), (813, Int.negSucc 7), (840,
    Int.ofNat 8), (768, Int.negSucc 19), (798, Int.negSucc 19), (812, Int.ofNat 20), (814,
    Int.ofNat 20), (815, Int.ofNat 20), (840, Int.negSucc 39), (738, Int.ofNat 8), (798, Int.ofNat
    8), (812, Int.negSucc 7), (813, Int.negSucc 7), (814, Int.negSucc 7), (815, Int.ofNat 8),
    (840, Int.ofNat 16), (588, Int.negSucc 3), (798, Int.negSucc 3), (812, Int.negSucc 3), (813,
    Int.ofNat 8), (814, Int.negSucc 3), (815, Int.ofNat 4), (840, Int.negSucc 7), (618,
    Int.negSucc 3), (798, Int.negSucc 3), (812, Int.negSucc 3), (813, Int.ofNat 8), (814,
    Int.ofNat 4), (815, Int.negSucc 3), (840, Int.negSucc 7), (648, Int.negSucc 3), (798,
    Int.negSucc 3), (812, Int.ofNat 4), (813, Int.ofNat 8), (814, Int.negSucc 3), (815,
    Int.negSucc 3), (840, Int.negSucc 7), (468, Int.negSucc 15), (798, Int.ofNat 16), (815,
    Int.negSucc 31), (840, Int.ofNat 32), (498, Int.negSucc 7), (798, Int.ofNat 8), (814,
    Int.negSucc 15), (840, Int.ofNat 16), (558, Int.negSucc 7), (798, Int.ofNat 8), (812,
    Int.negSucc 15), (840, Int.ofNat 16), (29, Int.ofNat 8), (31, Int.ofNat 8), (32, Int.negSucc
    7), (57, Int.negSucc 7), (87, Int.negSucc 15), (89, Int.negSucc 15), (90, Int.ofNat 16), (115,
    Int.ofNat 16), (738, Int.ofNat 8), (768, Int.negSucc 7), (798, Int.negSucc 7), (813, Int.ofNat
    8), (840, Int.negSucc 15)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 14, mode := 2, source := [(14, Int.negSucc 1), (43, Int.ofNat 6), (72, Int.negSucc
    1), (101, Int.negSucc 5), (129, Int.ofNat 2), (381, Int.ofNat 2), (406, Int.negSucc 1), (407,
    Int.ofNat 6), (408, Int.negSucc 1), (409, Int.negSucc 5), (453, Int.negSucc 1), (537,
    Int.negSucc 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.ofNat 48), (32, Int.negSucc 95), (88, Int.negSucc 95), (90, Int.ofNat
    192), (132, Int.negSucc 47), (468, Int.negSucc 47), (1, Int.ofNat 20), (3, Int.negSucc 39),
    (29, Int.ofNat 20), (30, Int.negSucc 119), (31, Int.ofNat 20), (32, Int.ofNat 180), (59,
    Int.ofNat 20), (61, Int.negSucc 39), (87, Int.negSucc 39), (88, Int.ofNat 180), (89,
    Int.negSucc 39), (90, Int.negSucc 239), (132, Int.ofNat 60), (192, Int.ofNat 20), (252,
    Int.ofNat 20), (468, Int.ofNat 60), (528, Int.ofNat 20), (588, Int.ofNat 20), (30, Int.negSucc
    15), (31, Int.ofNat 16), (32, Int.ofNat 16), (59, Int.ofNat 16), (61, Int.negSucc 31), (88,
    Int.ofNat 16), (89, Int.negSucc 31), (192, Int.ofNat 8), (252, Int.ofNat 8), (282, Int.ofNat
    8), (342, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat 8), (618, Int.ofNat 8), (678,
    Int.negSucc 7), (0, Int.ofNat 40), (1, Int.negSucc 99), (2, Int.ofNat 40), (3, Int.ofNat 80),
    (29, Int.negSucc 99), (30, Int.ofNat 240), (31, Int.negSucc 99), (32, Int.negSucc 179), (58,
    Int.ofNat 40), (59, Int.negSucc 99), (60, Int.ofNat 40), (61, Int.ofNat 80), (87, Int.ofNat
    80), (88, Int.negSucc 179), (89, Int.ofNat 80), (90, Int.ofNat 120), (132, Int.negSucc 19),
    (192, Int.negSucc 59), (252, Int.negSucc 19), (468, Int.negSucc 19), (528, Int.negSucc 59),
    (588, Int.negSucc 19), (0, Int.negSucc 15), (1, Int.ofNat 48), (2, Int.negSucc 31), (3,
    Int.negSucc 31), (29, Int.ofNat 48), (30, Int.negSucc 127), (31, Int.ofNat 80), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 80), (60, Int.negSucc 47), (61, Int.negSucc 47),
    (87, Int.negSucc 31), (88, Int.ofNat 80), (89, Int.negSucc 47), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (162, Int.ofNat 8), (192, Int.ofNat 32), (252, Int.ofNat 8), (282, Int.ofNat 8),
    (468, Int.ofNat 8), (498, Int.ofNat 8), (528, Int.ofNat 32), (588, Int.ofNat 8), (618,
    Int.ofNat 8), (1, Int.ofNat 16), (3, Int.negSucc 31), (29, Int.ofNat 16), (30, Int.negSucc
    15), (32, Int.ofNat 16), (87, Int.negSucc 31), (88, Int.ofNat 16), (192, Int.ofNat 8), (252,
    Int.ofNat 8), (312, Int.ofNat 8), (372, Int.negSucc 7), (528, Int.ofNat 8), (588, Int.ofNat
    8), (648, Int.ofNat 8), (708, Int.negSucc 7), (192, Int.negSucc 7), (252, Int.negSucc 7),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (342, Int.ofNat 8), (372, Int.ofNat 8), (402,
    Int.ofNat 8), (432, Int.negSucc 7), (528, Int.negSucc 7), (588, Int.negSucc 7), (618,
    Int.negSucc 7), (648, Int.negSucc 7), (678, Int.ofNat 8), (708, Int.ofNat 8), (738, Int.ofNat
    8), (768, Int.negSucc 7), (0, Int.negSucc 47), (1, Int.ofNat 80), (2, Int.negSucc 31), (3,
    Int.negSucc 47), (29, Int.ofNat 80), (30, Int.negSucc 127), (31, Int.ofNat 48), (32, Int.ofNat
    80), (58, Int.negSucc 31), (59, Int.ofNat 48), (60, Int.negSucc 15), (61, Int.negSucc 31),
    (87, Int.negSucc 47), (88, Int.ofNat 80), (89, Int.negSucc 31), (90, Int.negSucc 47), (132,
    Int.ofNat 8), (192, Int.ofNat 32), (222, Int.ofNat 8), (252, Int.ofNat 8), (312, Int.ofNat 8),
    (468, Int.ofNat 8), (528, Int.ofNat 32), (558, Int.ofNat 8), (588, Int.ofNat 8), (648,
    Int.ofNat 8), (0, Int.ofNat 16), (1, Int.negSucc 47), (2, Int.ofNat 16), (3, Int.ofNat 48),
    (29, Int.negSucc 47), (30, Int.ofNat 128), (31, Int.negSucc 47), (32, Int.negSucc 111), (58,
    Int.ofNat 16), (59, Int.negSucc 47), (60, Int.ofNat 16), (61, Int.ofNat 48), (87, Int.ofNat
    48), (88, Int.negSucc 111), (89, Int.ofNat 48), (90, Int.ofNat 80), (132, Int.negSucc 23),
    (162, Int.negSucc 7), (192, Int.negSucc 31), (222, Int.negSucc 7), (252, Int.negSucc 23),
    (282, Int.negSucc 7), (312, Int.negSucc 7), (432, Int.negSucc 7), (462, Int.ofNat 8), (468,
    Int.negSucc 23), (498, Int.negSucc 7), (528, Int.negSucc 31), (558, Int.negSucc 7), (588,
    Int.negSucc 23), (618, Int.negSucc 7), (648, Int.negSucc 7), (768, Int.negSucc 7), (798,
    Int.ofNat 8), (528, Int.ofNat 48), (588, Int.ofNat 48), (618, Int.ofNat 48), (648, Int.ofNat
    48), (678, Int.negSucc 47), (708, Int.negSucc 47), (738, Int.negSucc 47), (768, Int.ofNat 48),
    (30, Int.ofNat 24), (57, Int.negSucc 23), (88, Int.negSucc 47), (115, Int.ofNat 48), (528,
    Int.negSucc 23), (588, Int.negSucc 23), (738, Int.ofNat 24), (768, Int.negSucc 23), (813,
    Int.negSucc 23), (815, Int.ofNat 48), (30, Int.ofNat 8), (57, Int.negSucc 7), (59, Int.negSucc
    15), (86, Int.ofNat 16), (528, Int.negSucc 7), (618, Int.negSucc 7), (708, Int.ofNat 8), (768,
    Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (1, Int.negSucc 15), (28, Int.ofNat
    16), (30, Int.ofNat 8), (57, Int.negSucc 7), (528, Int.negSucc 7), (648, Int.negSucc 7), (678,
    Int.ofNat 8), (768, Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (29, Int.ofNat
    24), (30, Int.negSucc 23), (31, Int.ofNat 24), (32, Int.ofNat 24), (57, Int.negSucc 23), (87,
    Int.negSucc 47), (88, Int.ofNat 48), (89, Int.negSucc 47), (90, Int.negSucc 47), (115,
    Int.ofNat 48), (468, Int.ofNat 24), (738, Int.ofNat 24), (768, Int.negSucc 23), (813,
    Int.negSucc 23), (815, Int.ofNat 48), (0, Int.negSucc 39), (1, Int.ofNat 40), (2, Int.negSucc
    39), (3, Int.negSucc 39), (28, Int.ofNat 40), (29, Int.ofNat 80), (30, Int.negSucc 79), (31,
    Int.ofNat 80), (32, Int.ofNat 80), (57, Int.negSucc 79), (58, Int.negSucc 39), (59, Int.ofNat
    40), (60, Int.negSucc 39), (61, Int.negSucc 39), (86, Int.ofNat 40), (87, Int.negSucc 39),
    (88, Int.ofNat 40), (89, Int.negSucc 39), (90, Int.negSucc 39), (115, Int.ofNat 40), (468,
    Int.ofNat 40), (498, Int.ofNat 40), (558, Int.ofNat 40), (678, Int.ofNat 40), (708, Int.ofNat
    40), (738, Int.ofNat 40), (768, Int.negSucc 39), (812, Int.ofNat 40), (813, Int.negSucc 79),
    (814, Int.ofNat 40), (815, Int.ofNat 40), (29, Int.negSucc 15), (30, Int.ofNat 16), (31,
    Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (58, Int.ofNat 32), (59,
    Int.negSucc 31), (60, Int.ofNat 32), (61, Int.ofNat 32), (86, Int.negSucc 31), (498,
    Int.negSucc 15), (708, Int.negSucc 15), (768, Int.ofNat 16), (813, Int.ofNat 16), (814,
    Int.negSucc 31), (0, Int.ofNat 32), (1, Int.negSucc 31), (2, Int.ofNat 32), (3, Int.ofNat 32),
    (28, Int.negSucc 31), (29, Int.negSucc 15), (30, Int.ofNat 16), (31, Int.negSucc 15), (32,
    Int.negSucc 15), (57, Int.ofNat 16), (558, Int.negSucc 15), (678, Int.negSucc 15), (768,
    Int.ofNat 16), (812, Int.negSucc 31), (813, Int.ofNat 16), (29, Int.ofNat 16), (31,
    Int.negSucc 15), (32, Int.negSucc 15), (57, Int.ofNat 16), (87, Int.negSucc 31), (89,
    Int.ofNat 32), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 15), (618,
    Int.negSucc 15), (678, Int.ofNat 16), (813, Int.ofNat 16), (815, Int.negSucc 31), (0,
    Int.negSucc 15), (2, Int.ofNat 16), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.ofNat
    32), (31, Int.negSucc 31), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.negSucc 15),
    (60, Int.ofNat 16), (61, Int.ofNat 16), (86, Int.negSucc 15), (87, Int.negSucc 15), (89,
    Int.ofNat 16), (90, Int.ofNat 16), (115, Int.negSucc 15), (468, Int.negSucc 15), (498,
    Int.negSucc 15), (588, Int.negSucc 15), (618, Int.negSucc 15), (812, Int.negSucc 15), (813,
    Int.ofNat 32), (814, Int.negSucc 15), (815, Int.negSucc 15), (29, Int.negSucc 15), (31,
    Int.ofNat 16), (32, Int.negSucc 15), (57, Int.ofNat 16), (87, Int.ofNat 32), (89, Int.negSucc
    31), (90, Int.ofNat 32), (115, Int.negSucc 31), (468, Int.negSucc 15), (648, Int.negSucc 15),
    (708, Int.ofNat 16), (813, Int.ofNat 16), (815, Int.negSucc 31), (0, Int.ofNat 16), (2,
    Int.negSucc 15), (3, Int.ofNat 16), (28, Int.negSucc 15), (29, Int.negSucc 31), (31, Int.ofNat
    32), (32, Int.negSucc 31), (57, Int.ofNat 32), (58, Int.ofNat 16), (60, Int.negSucc 15), (61,
    Int.ofNat 16), (86, Int.negSucc 15), (87, Int.ofNat 16), (89, Int.negSucc 15), (90, Int.ofNat
    16), (115, Int.negSucc 15), (468, Int.negSucc 15), (558, Int.negSucc 15), (588, Int.negSucc
    15), (648, Int.negSucc 15), (812, Int.negSucc 15), (813, Int.ofNat 32), (814, Int.negSucc 15),
    (815, Int.negSucc 15), (0, Int.ofNat 24), (2, Int.ofNat 24), (3, Int.negSucc 23), (28,
    Int.negSucc 23), (29, Int.negSucc 71), (31, Int.negSucc 71), (32, Int.ofNat 72), (57,
    Int.ofNat 72), (58, Int.ofNat 24), (60, Int.ofNat 24), (61, Int.negSucc 23), (86, Int.negSucc
    23), (87, Int.ofNat 72), (89, Int.ofNat 72), (90, Int.negSucc 71), (115, Int.negSucc 71),
    (132, Int.ofNat 24), (498, Int.negSucc 23), (558, Int.negSucc 23), (618, Int.negSucc 23),
    (648, Int.negSucc 23), (738, Int.negSucc 23), (768, Int.ofNat 24), (812, Int.negSucc 23),
    (813, Int.ofNat 72), (814, Int.negSucc 23), (815, Int.negSucc 71), (29, Int.ofNat 8), (31,
    Int.ofNat 8), (32, Int.negSucc 7), (57, Int.negSucc 7), (58, Int.negSucc 15), (60, Int.negSucc
    15), (61, Int.ofNat 16), (86, Int.ofNat 16), (498, Int.ofNat 8), (648, Int.ofNat 8), (738,
    Int.negSucc 7), (813, Int.negSucc 7), (814, Int.ofNat 16), (0, Int.negSucc 15), (2,
    Int.negSucc 15), (3, Int.ofNat 16), (28, Int.ofNat 16), (29, Int.ofNat 8), (31, Int.ofNat 8),
    (32, Int.negSucc 7), (57, Int.negSucc 7), (558, Int.ofNat 8), (618, Int.ofNat 8), (738,
    Int.negSucc 7), (812, Int.ofNat 16), (813, Int.negSucc 7), (798, Int.negSucc 15), (813,
    Int.ofNat 16), (840, Int.negSucc 15), (768, Int.ofNat 8), (798, Int.ofNat 8), (812,
    Int.negSucc 7), (814, Int.negSucc 7), (815, Int.negSucc 7), (840, Int.ofNat 16), (588,
    Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (813, Int.negSucc 15), (814, Int.ofNat
    8), (815, Int.negSucc 7), (840, Int.ofNat 16), (618, Int.ofNat 8), (798, Int.ofNat 8), (812,
    Int.ofNat 8), (813, Int.negSucc 15), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat
    16), (648, Int.ofNat 8), (798, Int.ofNat 8), (812, Int.negSucc 7), (813, Int.negSucc 15),
    (814, Int.ofNat 8), (815, Int.ofNat 8), (840, Int.ofNat 16), (468, Int.ofNat 16), (798,
    Int.negSucc 15), (815, Int.ofNat 32), (840, Int.negSucc 31), (498, Int.ofNat 8), (798,
    Int.negSucc 7), (814, Int.ofNat 16), (840, Int.negSucc 15), (558, Int.ofNat 8), (798,
    Int.negSucc 7), (812, Int.ofNat 16), (840, Int.negSucc 15), (29, Int.negSucc 7), (31,
    Int.negSucc 7), (32, Int.ofNat 8), (57, Int.ofNat 8), (87, Int.ofNat 16), (89, Int.ofNat 16),
    (90, Int.negSucc 15), (115, Int.negSucc 15), (738, Int.negSucc 7), (768, Int.ofNat 8), (798,
    Int.ofNat 8), (813, Int.negSucc 7), (840, Int.ofNat 16)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 372, 402, 432, 462, 468, 498, 528, 558, 588, 618, 648,
    678, 708, 738, 768, 798, 812, 813, 814, 815, 840] },
  { color := 2, mode := 3, source := [(1, Int.negSucc 3), (2, Int.ofNat 8), (29, Int.negSucc 3),
    (30, Int.ofNat 12), (31, Int.negSucc 13), (32, Int.negSucc 3), (58, Int.ofNat 8), (59,
    Int.negSucc 13), (60, Int.ofNat 8), (61, Int.ofNat 8), (88, Int.negSucc 3), (89, Int.ofNat 8),
    (162, Int.negSucc 1), (192, Int.negSucc 3), (252, Int.negSucc 0), (282, Int.negSucc 3), (312,
    Int.negSucc 0), (342, Int.ofNat 1), (402, Int.ofNat 1), (498, Int.negSucc 1), (528,
    Int.negSucc 3), (588, Int.negSucc 0), (618, Int.negSucc 3), (648, Int.negSucc 0), (678,
    Int.ofNat 1), (738, Int.ofNat 1)],
    denominator := Int.ofNat 4,
    target := [(30, Int.negSucc 47), (32, Int.ofNat 96), (88, Int.ofNat 96), (90, Int.negSucc
    191), (132, Int.ofNat 48), (468, Int.ofNat 48), (0, Int.ofNat 16), (1, Int.negSucc 39), (2,
    Int.ofNat 16), (3, Int.ofNat 32), (29, Int.negSucc 39), (30, Int.ofNat 96), (31, Int.negSucc
    39), (32, Int.negSucc 71), (58, Int.ofNat 16), (59, Int.negSucc 39), (60, Int.ofNat 16), (61,
    Int.ofNat 32), (87, Int.ofNat 32), (88, Int.negSucc 71), (89, Int.ofNat 32), (90, Int.ofNat
    48), (132, Int.negSucc 7), (192, Int.negSucc 23), (252, Int.negSucc 7), (468, Int.negSucc 7),
    (528, Int.negSucc 23), (588, Int.negSucc 7), (0, Int.negSucc 7), (1, Int.ofNat 24), (2,
    Int.negSucc 15), (3, Int.negSucc 15), (29, Int.ofNat 24), (30, Int.negSucc 63), (31, Int.ofNat
    40), (32, Int.ofNat 40), (58, Int.negSucc 15), (59, Int.ofNat 40), (60, Int.negSucc 23), (61,
    Int.negSucc 23), (87, Int.negSucc 15), (88, Int.ofNat 40), (89, Int.negSucc 23), (90,
    Int.negSucc 23), (132, Int.ofNat 4), (162, Int.ofNat 4), (192, Int.ofNat 16), (252, Int.ofNat
    4), (282, Int.ofNat 4), (468, Int.ofNat 4), (498, Int.ofNat 4), (528, Int.ofNat 16), (588,
    Int.ofNat 4), (618, Int.ofNat 4), (1, Int.negSucc 3), (2, Int.ofNat 8), (29, Int.negSucc 3),
    (30, Int.ofNat 24), (31, Int.negSucc 35), (32, Int.negSucc 3), (58, Int.ofNat 8), (59,
    Int.negSucc 35), (60, Int.ofNat 48), (61, Int.ofNat 8), (88, Int.negSucc 3), (89, Int.ofNat
    8), (162, Int.negSucc 11), (192, Int.negSucc 3), (282, Int.negSucc 3), (498, Int.negSucc 11),
    (528, Int.negSucc 3), (618, Int.negSucc 3), (0, Int.negSucc 71), (1, Int.ofNat 120), (2,
    Int.negSucc 47), (3, Int.negSucc 71), (29, Int.ofNat 120), (30, Int.negSucc 191), (31,
    Int.ofNat 72), (32, Int.ofNat 120), (58, Int.negSucc 47), (59, Int.ofNat 72), (60, Int.negSucc
    23), (61, Int.negSucc 47), (87, Int.negSucc 71), (88, Int.ofNat 120), (89, Int.negSucc 47),
    (90, Int.negSucc 71), (132, Int.ofNat 12), (192, Int.ofNat 48), (222, Int.ofNat 12), (252,
    Int.ofNat 12), (312, Int.ofNat 12), (468, Int.ofNat 12), (528, Int.ofNat 48), (558, Int.ofNat
    12), (588, Int.ofNat 12), (648, Int.ofNat 12), (1, Int.negSucc 15), (2, Int.ofNat 32), (29,
    Int.negSucc 15), (30, Int.ofNat 48), (31, Int.negSucc 55), (32, Int.negSucc 15), (58,
    Int.ofNat 32), (59, Int.negSucc 55), (60, Int.ofNat 32), (61, Int.ofNat 32), (88, Int.negSucc
    15), (89, Int.ofNat 32), (162, Int.negSucc 7), (192, Int.negSucc 15), (252, Int.negSucc 3),
    (282, Int.negSucc 15), (312, Int.negSucc 3), (342, Int.ofNat 4), (402, Int.ofNat 4), (498,
    Int.negSucc 7), (528, Int.negSucc 15), (588, Int.negSucc 3), (618, Int.negSucc 15), (648,
    Int.negSucc 3), (678, Int.ofNat 4), (738, Int.ofNat 4), (0, Int.ofNat 48), (1, Int.negSucc
    35), (2, Int.ofNat 8), (3, Int.ofNat 8), (29, Int.negSucc 35), (30, Int.ofNat 24), (31,
    Int.negSucc 3), (32, Int.negSucc 3), (58, Int.ofNat 8), (59, Int.negSucc 3), (87, Int.ofNat
    8), (88, Int.negSucc 3), (192, Int.negSucc 3), (222, Int.negSucc 11), (312, Int.negSucc 3),
    (528, Int.negSucc 3), (558, Int.negSucc 11), (648, Int.negSucc 3), (528, Int.negSucc 127),
    (588, Int.negSucc 127), (618, Int.negSucc 127), (648, Int.negSucc 127), (678, Int.ofNat 128),
    (708, Int.ofNat 128), (738, Int.ofNat 128), (768, Int.negSucc 127), (30, Int.negSucc 15), (57,
    Int.ofNat 16), (88, Int.ofNat 32), (115, Int.negSucc 31), (528, Int.ofNat 16), (588, Int.ofNat
    16), (738, Int.negSucc 15), (768, Int.ofNat 16), (813, Int.ofNat 16), (815, Int.negSucc 31),
    (1, Int.ofNat 32), (28, Int.negSucc 31), (30, Int.negSucc 63), (57, Int.ofNat 64), (59,
    Int.ofNat 32), (86, Int.negSucc 31), (88, Int.ofNat 32), (115, Int.negSucc 31), (528,
    Int.ofNat 32), (768, Int.ofNat 32), (798, Int.negSucc 31), (812, Int.negSucc 31), (813,
    Int.ofNat 64), (814, Int.negSucc 31), (815, Int.negSucc 31), (30, Int.negSucc 31), (57,
    Int.ofNat 32), (59, Int.ofNat 64), (86, Int.negSucc 63), (528, Int.ofNat 32), (618, Int.ofNat
    32), (708, Int.negSucc 31), (768, Int.ofNat 32), (813, Int.ofNat 32), (814, Int.negSucc 63),
    (1, Int.ofNat 32), (28, Int.negSucc 31), (30, Int.negSucc 15), (57, Int.ofNat 16), (528,
    Int.ofNat 16), (648, Int.ofNat 16), (678, Int.negSucc 15), (768, Int.ofNat 16), (812,
    Int.negSucc 31), (813, Int.ofNat 16), (29, Int.negSucc 75), (30, Int.ofNat 76), (31,
    Int.negSucc 75), (32, Int.negSucc 75), (57, Int.ofNat 76), (87, Int.ofNat 152), (88,
    Int.negSucc 151), (89, Int.ofNat 152), (90, Int.ofNat 152), (115, Int.negSucc 151), (468,
    Int.negSucc 75), (738, Int.negSucc 75), (768, Int.ofNat 76), (813, Int.ofNat 76), (815,
    Int.negSucc 151), (0, Int.ofNat 72), (1, Int.negSucc 71), (2, Int.ofNat 72), (3, Int.ofNat
    72), (28, Int.negSucc 71), (29, Int.negSucc 143), (30, Int.ofNat 144), (31, Int.negSucc 143),
    (32, Int.negSucc 143), (57, Int.ofNat 144), (58, Int.ofNat 72), (59, Int.negSucc 71), (60,
    Int.ofNat 72), (61, Int.ofNat 72), (86, Int.negSucc 71), (87, Int.ofNat 72), (88, Int.negSucc
    71), (89, Int.ofNat 72), (90, Int.ofNat 72), (115, Int.negSucc 71), (468, Int.negSucc 71),
    (498, Int.negSucc 71), (558, Int.negSucc 71), (678, Int.negSucc 71), (708, Int.negSucc 71),
    (738, Int.negSucc 71), (768, Int.ofNat 72), (812, Int.negSucc 71), (813, Int.ofNat 144), (814,
    Int.negSucc 71), (815, Int.negSucc 71), (0, Int.ofNat 40), (1, Int.negSucc 39), (2, Int.ofNat
    40), (3, Int.ofNat 40), (28, Int.negSucc 39), (29, Int.negSucc 19), (30, Int.ofNat 20), (31,
    Int.negSucc 19), (32, Int.negSucc 19), (57, Int.ofNat 20), (558, Int.negSucc 19), (678,
    Int.negSucc 19), (768, Int.ofNat 20), (812, Int.negSucc 39), (813, Int.ofNat 20), (29,
    Int.negSucc 23), (31, Int.ofNat 24), (32, Int.ofNat 24), (57, Int.negSucc 23), (87, Int.ofNat
    48), (89, Int.negSucc 47), (90, Int.negSucc 47), (115, Int.ofNat 48), (468, Int.ofNat 24),
    (618, Int.ofNat 24), (678, Int.negSucc 23), (813, Int.negSucc 23), (815, Int.ofNat 48), (0,
    Int.ofNat 56), (2, Int.negSucc 55), (3, Int.negSucc 55), (28, Int.ofNat 56), (29, Int.negSucc
    111), (31, Int.ofNat 112), (32, Int.ofNat 112), (57, Int.negSucc 111), (58, Int.ofNat 56),
    (60, Int.negSucc 55), (61, Int.negSucc 55), (86, Int.ofNat 56), (87, Int.ofNat 56), (89,
    Int.negSucc 55), (90, Int.negSucc 55), (115, Int.ofNat 56), (468, Int.ofNat 56), (498,
    Int.ofNat 56), (588, Int.ofNat 56), (618, Int.ofNat 56), (812, Int.ofNat 56), (813,
    Int.negSucc 111), (814, Int.ofNat 56), (815, Int.ofNat 56), (29, Int.negSucc 19), (31,
    Int.ofNat 20), (32, Int.ofNat 20), (57, Int.negSucc 19), (58, Int.ofNat 40), (60, Int.negSucc
    39), (61, Int.negSucc 39), (86, Int.ofNat 40), (498, Int.ofNat 20), (588, Int.ofNat 20), (678,
    Int.negSucc 19), (813, Int.negSucc 19), (814, Int.ofNat 40), (29, Int.ofNat 20), (31,
    Int.negSucc 19), (32, Int.ofNat 20), (57, Int.negSucc 19), (87, Int.negSucc 39), (89,
    Int.ofNat 40), (90, Int.negSucc 39), (115, Int.ofNat 40), (468, Int.ofNat 20), (648, Int.ofNat
    20), (708, Int.negSucc 19), (813, Int.negSucc 19), (815, Int.ofNat 40), (0, Int.negSucc 39),
    (2, Int.ofNat 40), (3, Int.negSucc 39), (28, Int.ofNat 40), (29, Int.ofNat 80), (31,
    Int.negSucc 79), (32, Int.ofNat 80), (57, Int.negSucc 79), (58, Int.negSucc 39), (60,
    Int.ofNat 40), (61, Int.negSucc 39), (86, Int.ofNat 40), (87, Int.negSucc 39), (89, Int.ofNat
    40), (90, Int.negSucc 39), (115, Int.ofNat 40), (468, Int.ofNat 40), (558, Int.ofNat 40),
    (588, Int.ofNat 40), (648, Int.ofNat 40), (812, Int.ofNat 40), (813, Int.negSucc 79), (814,
    Int.ofNat 40), (815, Int.ofNat 40), (0, Int.negSucc 55), (2, Int.negSucc 55), (3, Int.ofNat
    56), (28, Int.ofNat 56), (29, Int.ofNat 168), (31, Int.ofNat 168), (32, Int.negSucc 167), (57,
    Int.negSucc 167), (58, Int.negSucc 55), (60, Int.negSucc 55), (61, Int.ofNat 56), (86,
    Int.ofNat 56), (87, Int.negSucc 167), (89, Int.negSucc 167), (90, Int.ofNat 168), (115,
    Int.ofNat 168), (132, Int.negSucc 55), (498, Int.ofNat 56), (558, Int.ofNat 56), (618,
    Int.ofNat 56), (648, Int.ofNat 56), (738, Int.ofNat 56), (768, Int.negSucc 55), (812,
    Int.ofNat 56), (813, Int.negSucc 167), (814, Int.ofNat 56), (815, Int.ofNat 168), (29,
    Int.ofNat 20), (31, Int.ofNat 20), (32, Int.negSucc 19), (57, Int.negSucc 19), (58,
    Int.negSucc 39), (60, Int.negSucc 39), (61, Int.ofNat 40), (86, Int.ofNat 40), (498, Int.ofNat
    20), (648, Int.ofNat 20), (738, Int.negSucc 19), (813, Int.negSucc 19), (814, Int.ofNat 40),
    (0, Int.negSucc 39), (2, Int.ofNat 40), (3, Int.negSucc 39), (28, Int.ofNat 40), (29,
    Int.ofNat 20), (31, Int.negSucc 19), (32, Int.ofNat 20), (57, Int.negSucc 19), (558, Int.ofNat
    20), (588, Int.ofNat 20), (708, Int.negSucc 19), (812, Int.ofNat 40), (813, Int.negSucc 19),
    (0, Int.negSucc 47), (2, Int.negSucc 47), (3, Int.ofNat 48), (28, Int.ofNat 48), (29,
    Int.ofNat 24), (31, Int.ofNat 24), (32, Int.negSucc 23), (57, Int.negSucc 23), (558, Int.ofNat
    24), (618, Int.ofNat 24), (738, Int.negSucc 23), (812, Int.ofNat 48), (813, Int.negSucc 23),
    (798, Int.ofNat 80), (813, Int.negSucc 79), (840, Int.ofNat 80), (768, Int.negSucc 31), (798,
    Int.negSucc 31), (812, Int.ofNat 32), (814, Int.ofNat 32), (815, Int.ofNat 32), (840,
    Int.negSucc 63), (588, Int.negSucc 31), (798, Int.negSucc 31), (812, Int.negSucc 31), (813,
    Int.ofNat 64), (814, Int.negSucc 31), (815, Int.ofNat 32), (840, Int.negSucc 63), (618,
    Int.negSucc 31), (798, Int.negSucc 31), (812, Int.negSucc 31), (813, Int.ofNat 64), (814,
    Int.ofNat 32), (815, Int.negSucc 31), (840, Int.negSucc 63), (648, Int.negSucc 31), (798,
    Int.negSucc 31), (812, Int.ofNat 32), (813, Int.ofNat 64), (814, Int.negSucc 31), (815,
    Int.negSucc 31), (840, Int.negSucc 63), (468, Int.negSucc 47), (798, Int.ofNat 48), (815,
    Int.negSucc 95), (840, Int.ofNat 96), (498, Int.negSucc 47), (798, Int.ofNat 48), (814,
    Int.negSucc 95), (840, Int.ofNat 96), (558, Int.negSucc 47), (798, Int.ofNat 48), (812,
    Int.negSucc 95), (840, Int.ofNat 96), (29, Int.ofNat 16), (31, Int.ofNat 16), (32, Int.negSucc
    15), (57, Int.negSucc 15), (87, Int.negSucc 31), (89, Int.negSucc 31), (90, Int.ofNat 32),
    (115, Int.ofNat 32), (738, Int.ofNat 16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813,
    Int.ofNat 16), (840, Int.negSucc 31), (29, Int.ofNat 16), (31, Int.negSucc 15), (32, Int.ofNat
    16), (57, Int.negSucc 15), (58, Int.negSucc 31), (60, Int.ofNat 32), (61, Int.negSucc 31),
    (86, Int.ofNat 32), (708, Int.ofNat 16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813,
    Int.ofNat 16), (840, Int.negSucc 31), (0, Int.ofNat 32), (2, Int.negSucc 31), (3, Int.negSucc
    31), (28, Int.ofNat 32), (29, Int.negSucc 15), (31, Int.ofNat 16), (32, Int.ofNat 16), (57,
    Int.negSucc 15), (678, Int.ofNat 16), (768, Int.negSucc 15), (798, Int.negSucc 15), (813,
    Int.ofNat 16), (840, Int.negSucc 31), (798, Int.negSucc 39), (812, Int.ofNat 40), (813,
    Int.negSucc 39), (814, Int.ofNat 40), (815, Int.ofNat 40), (840, Int.negSucc 39), (798,
    Int.ofNat 8), (812, Int.negSucc 7), (814, Int.negSucc 7), (815, Int.ofNat 8), (840, Int.ofNat
    8), (798, Int.ofNat 8), (812, Int.negSucc 7), (814, Int.ofNat 8), (815, Int.negSucc 7), (840,
    Int.ofNat 8), (798, Int.ofNat 8), (812, Int.ofNat 8), (814, Int.negSucc 7), (815, Int.negSucc
    7), (840, Int.ofNat 8)],
    coordinates := [0, 1, 2, 3, 28, 29, 30, 31, 32, 57, 58, 59, 60, 61, 86, 87, 88, 89, 90, 115,
    132, 162, 192, 222, 252, 282, 312, 342, 402, 468, 498, 528, 558, 588, 618, 648, 678, 708, 738,
    768, 798, 812, 813, 814, 815, 840] }
]

end VOA.DeligneAudit.D4Two.Certificate

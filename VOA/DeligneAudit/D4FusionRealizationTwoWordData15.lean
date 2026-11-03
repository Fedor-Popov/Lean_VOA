/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData15 : List WordNode := [
  { level := 1, parent := 42, color := 26, mode := 1,
    vector := [(29, Int.ofNat 1), (30, Int.negSucc 0), (31, Int.ofNat 1), (32, Int.ofNat 1), (57,
    Int.negSucc 0), (87, Int.negSucc 1), (88, Int.ofNat 2), (89, Int.negSucc 1), (90, Int.negSucc
    1), (115, Int.ofNat 2), (468, Int.ofNat 1), (738, Int.ofNat 1), (768, Int.negSucc 0), (813,
    Int.negSucc 0), (815, Int.ofNat 2)] },
  { level := 1, parent := 42, color := 27, mode := 1,
    vector := [(35, Int.negSucc 0), (93, Int.ofNat 2), (472, Int.ofNat 1)] },
  { level := 1, parent := 43, color := 24, mode := 1,
    vector := [(522, Int.negSucc 1), (524, Int.ofNat 2), (525, Int.negSucc 1), (550, Int.ofNat 2),
    (584, Int.ofNat 2), (645, Int.negSucc 1), (830, Int.ofNat 2)] },
  { level := 1, parent := 43, color := 26, mode := 1,
    vector := [(527, Int.negSucc 1)] },
  { level := 1, parent := 43, color := 27, mode := 1,
    vector := [(531, Int.negSucc 1), (591, Int.negSucc 1), (651, Int.negSucc 1), (710, Int.ofNat
    2)] },
  { level := 1, parent := 44, color := 23, mode := 1,
    vector := [(19, Int.ofNat 1), (48, Int.negSucc 1), (77, Int.ofNat 1), (106, Int.ofNat 1),
    (551, Int.ofNat 1), (553, Int.negSucc 0), (554, Int.negSucc 0), (579, Int.ofNat 1), (704,
    Int.ofNat 1), (734, Int.ofNat 1), (831, Int.ofNat 1)] },
  { level := 1, parent := 44, color := 24, mode := 1,
    vector := [(17, Int.negSucc 0), (46, Int.ofNat 2), (75, Int.negSucc 0), (104, Int.negSucc 0),
    (493, Int.ofNat 1), (495, Int.negSucc 0), (496, Int.ofNat 1), (521, Int.negSucc 0), (675,
    Int.ofNat 1), (735, Int.ofNat 1), (829, Int.negSucc 0)] },
  { level := 1, parent := 44, color := 25, mode := 1,
    vector := [(16, Int.negSucc 0), (45, Int.ofNat 2), (74, Int.negSucc 0), (103, Int.negSucc 0),
    (464, Int.ofNat 1), (466, Int.ofNat 1), (467, Int.negSucc 0), (492, Int.negSucc 0), (676,
    Int.ofNat 1), (706, Int.ofNat 1), (828, Int.negSucc 0)] },
  { level := 1, parent := 44, color := 26, mode := 1,
    vector := [(0, Int.negSucc 0), (1, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.negSucc 0), (28,
    Int.ofNat 1), (29, Int.ofNat 2), (30, Int.negSucc 1), (31, Int.ofNat 2), (32, Int.ofNat 2),
    (57, Int.negSucc 1), (58, Int.negSucc 0), (59, Int.ofNat 1), (60, Int.negSucc 0), (61,
    Int.negSucc 0), (86, Int.ofNat 1), (87, Int.negSucc 0), (88, Int.ofNat 1), (89, Int.negSucc
    0), (90, Int.negSucc 0), (115, Int.ofNat 1), (468, Int.ofNat 1), (498, Int.ofNat 1), (558,
    Int.ofNat 1), (678, Int.ofNat 1), (708, Int.ofNat 1), (738, Int.ofNat 1), (768, Int.negSucc
    0), (812, Int.ofNat 1), (813, Int.negSucc 1), (814, Int.ofNat 1), (815, Int.ofNat 1)] },
  { level := 1, parent := 44, color := 27, mode := 1,
    vector := [(6, Int.ofNat 1), (35, Int.negSucc 1), (64, Int.ofNat 1), (93, Int.ofNat 1), (472,
    Int.ofNat 1), (502, Int.ofNat 1), (561, Int.negSucc 0), (769, Int.ofNat 1)] },
  { level := 1, parent := 45, color := 25, mode := 1,
    vector := [(522, Int.negSucc 1), (524, Int.negSucc 1), (525, Int.ofNat 2), (550, Int.ofNat 2),
    (614, Int.ofNat 2), (645, Int.negSucc 1), (830, Int.ofNat 2)] },
  { level := 1, parent := 45, color := 26, mode := 1,
    vector := [(526, Int.negSucc 1)] },
  { level := 1, parent := 45, color := 27, mode := 1,
    vector := [(530, Int.negSucc 1), (620, Int.negSucc 1), (650, Int.negSucc 1), (739, Int.ofNat
    2)] },
  { level := 1, parent := 46, color := 23, mode := 1,
    vector := [(48, Int.negSucc 0), (77, Int.ofNat 2), (704, Int.ofNat 1), (765, Int.negSucc 0)]
    },
  { level := 1, parent := 46, color := 25, mode := 1,
    vector := [(45, Int.ofNat 1), (74, Int.negSucc 1), (706, Int.ofNat 1), (767, Int.negSucc 0)]
    },
  { level := 1, parent := 46, color := 26, mode := 1,
    vector := [(29, Int.ofNat 1), (30, Int.negSucc 0), (31, Int.ofNat 1), (32, Int.ofNat 1), (57,
    Int.negSucc 0), (58, Int.negSucc 1), (59, Int.ofNat 2), (60, Int.negSucc 1), (61, Int.negSucc
    1), (86, Int.ofNat 2), (498, Int.ofNat 1), (708, Int.ofNat 1), (768, Int.negSucc 0), (813,
    Int.negSucc 0), (814, Int.ofNat 2)] },
  { level := 1, parent := 46, color := 27, mode := 1,
    vector := [(35, Int.negSucc 0), (64, Int.ofNat 2), (502, Int.ofNat 1)] },
  { level := 1, parent := 47, color := 25, mode := 1,
    vector := [(493, Int.ofNat 1), (495, Int.ofNat 1), (496, Int.negSucc 0), (521, Int.negSucc 0),
    (735, Int.ofNat 1), (829, Int.negSucc 0)] },
  { level := 1, parent := 47, color := 26, mode := 1,
    vector := [(497, Int.ofNat 1), (737, Int.ofNat 1)] },
  { level := 1, parent := 47, color := 27, mode := 1,
    vector := [(501, Int.ofNat 1)] },
  { level := 1, parent := 48, color := 27, mode := 1,
    vector := [(6, Int.ofNat 1), (35, Int.negSucc 2), (64, Int.ofNat 1), (93, Int.ofNat 3), (175,
    Int.negSucc 0), (202, Int.ofNat 1), (472, Int.ofNat 1), (769, Int.ofNat 1), (818, Int.ofNat
    1)] },
  { level := 1, parent := 49, color := 27, mode := 1,
    vector := [(117, Int.ofNat 2), (144, Int.negSucc 1), (530, Int.negSucc 1), (739, Int.ofNat 2),
    (816, Int.negSucc 1)] },
  { level := 1, parent := 50, color := 27, mode := 1,
    vector := [(204, Int.ofNat 1), (231, Int.negSucc 0), (532, Int.ofNat 1), (681, Int.negSucc 0),
    (819, Int.negSucc 0)] },
  { level := 1, parent := 51, color := 27, mode := 1,
    vector := [(146, Int.ofNat 1), (173, Int.negSucc 0), (531, Int.negSucc 0), (710, Int.ofNat 1),
    (817, Int.negSucc 0)] },
  { level := 1, parent := 52, color := 24, mode := 1,
    vector := [(551, Int.ofNat 4), (553, Int.negSucc 3), (554, Int.ofNat 4), (579, Int.negSucc 3),
    (704, Int.negSucc 3), (831, Int.negSucc 3)] },
  { level := 1, parent := 52, color := 26, mode := 1,
    vector := [(556, Int.ofNat 4), (707, Int.negSucc 3)] },
  { level := 1, parent := 52, color := 27, mode := 1,
    vector := [(560, Int.ofNat 4)] },
  { level := 1, parent := 53, color := 27, mode := 1,
    vector := [(649, Int.ofNat 8)] },
  { level := 1, parent := 54, color := 24, mode := 1,
    vector := [(17, Int.negSucc 3), (46, Int.ofNat 2), (675, Int.ofNat 2), (766, Int.negSucc 1)]
    },
  { level := 1, parent := 54, color := 25, mode := 1,
    vector := [(16, Int.negSucc 3), (45, Int.ofNat 2), (676, Int.ofNat 2), (767, Int.negSucc 1)]
    },
  { level := 1, parent := 54, color := 26, mode := 1,
    vector := [(0, Int.negSucc 3), (1, Int.ofNat 4), (2, Int.negSucc 3), (3, Int.negSucc 3), (28,
    Int.ofNat 4), (29, Int.ofNat 2), (30, Int.negSucc 1), (31, Int.ofNat 2), (32, Int.ofNat 2),
    (57, Int.negSucc 1), (558, Int.ofNat 2), (678, Int.ofNat 2), (768, Int.negSucc 1), (812,
    Int.ofNat 4), (813, Int.negSucc 1)] },
  { level := 1, parent := 54, color := 27, mode := 1,
    vector := [(6, Int.ofNat 4), (35, Int.negSucc 1), (561, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

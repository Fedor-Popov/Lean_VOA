/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData16 : List WordNode := [
  { level := 1, parent := 55, color := 25, mode := 1,
    vector := [(551, Int.ofNat 2), (553, Int.ofNat 2), (554, Int.negSucc 1), (579, Int.negSucc 1),
    (734, Int.negSucc 1), (831, Int.negSucc 1)] },
  { level := 1, parent := 55, color := 26, mode := 1,
    vector := [(555, Int.ofNat 2), (736, Int.negSucc 1)] },
  { level := 1, parent := 55, color := 27, mode := 1,
    vector := [(559, Int.ofNat 2)] },
  { level := 1, parent := 56, color := 27, mode := 1,
    vector := [(477, Int.ofNat 2)] },
  { level := 1, parent := 57, color := 23, mode := 1,
    vector := [(29, Int.ofNat 2), (31, Int.negSucc 1), (32, Int.negSucc 1), (57, Int.ofNat 2),
    (87, Int.negSucc 3), (89, Int.ofNat 4), (90, Int.ofNat 4), (115, Int.negSucc 3), (468,
    Int.negSucc 1), (618, Int.negSucc 1), (678, Int.ofNat 2), (813, Int.ofNat 2), (815,
    Int.negSucc 3)] },
  { level := 1, parent := 57, color := 26, mode := 1,
    vector := [(36, Int.ofNat 2), (94, Int.negSucc 3), (622, Int.negSucc 1), (681, Int.ofNat 2)]
    },
  { level := 1, parent := 57, color := 27, mode := 1,
    vector := [(39, Int.negSucc 1), (97, Int.ofNat 4), (476, Int.ofNat 2)] },
  { level := 1, parent := 58, color := 27, mode := 1,
    vector := [(535, Int.negSucc 3), (594, Int.negSucc 3)] },
  { level := 1, parent := 59, color := 23, mode := 1,
    vector := [(0, Int.negSucc 1), (2, Int.ofNat 2), (3, Int.ofNat 2), (28, Int.negSucc 1), (29,
    Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (57, Int.ofNat 4), (58, Int.negSucc
    1), (60, Int.ofNat 2), (61, Int.ofNat 2), (86, Int.negSucc 1), (87, Int.negSucc 1), (89,
    Int.ofNat 2), (90, Int.ofNat 2), (115, Int.negSucc 1), (468, Int.negSucc 1), (498, Int.negSucc
    1), (588, Int.negSucc 1), (618, Int.negSucc 1), (812, Int.negSucc 1), (813, Int.ofNat 4),
    (814, Int.negSucc 1), (815, Int.negSucc 1)] },
  { level := 1, parent := 59, color := 26, mode := 1,
    vector := [(7, Int.negSucc 1), (36, Int.ofNat 4), (65, Int.negSucc 1), (94, Int.negSucc 1),
    (592, Int.negSucc 1), (622, Int.negSucc 1), (681, Int.ofNat 2)] },
  { level := 1, parent := 59, color := 27, mode := 1,
    vector := [(10, Int.ofNat 2), (39, Int.negSucc 3), (68, Int.ofNat 2), (97, Int.ofNat 2), (476,
    Int.ofNat 2), (506, Int.ofNat 2), (682, Int.negSucc 1)] },
  { level := 1, parent := 60, color := 27, mode := 1,
    vector := [(534, Int.negSucc 3), (623, Int.negSucc 3)] },
  { level := 1, parent := 61, color := 23, mode := 1,
    vector := [(29, Int.ofNat 2), (31, Int.negSucc 1), (32, Int.negSucc 1), (57, Int.ofNat 2),
    (58, Int.negSucc 3), (60, Int.ofNat 4), (61, Int.ofNat 4), (86, Int.negSucc 3), (498,
    Int.negSucc 1), (588, Int.negSucc 1), (678, Int.ofNat 2), (813, Int.ofNat 2), (814,
    Int.negSucc 3)] },
  { level := 1, parent := 61, color := 26, mode := 1,
    vector := [(36, Int.ofNat 2), (65, Int.negSucc 3), (592, Int.negSucc 1), (681, Int.ofNat 2)]
    },
  { level := 1, parent := 61, color := 27, mode := 1,
    vector := [(39, Int.negSucc 1), (68, Int.ofNat 4), (506, Int.ofNat 2)] },
  { level := 1, parent := 62, color := 27, mode := 1,
    vector := [(505, Int.ofNat 2)] },
  { level := 1, parent := 63, color := 24, mode := 1,
    vector := [(29, Int.ofNat 1), (31, Int.negSucc 0), (32, Int.ofNat 1), (57, Int.negSucc 0),
    (87, Int.negSucc 1), (89, Int.ofNat 2), (90, Int.negSucc 1), (115, Int.ofNat 2), (468,
    Int.ofNat 1), (648, Int.ofNat 1), (708, Int.negSucc 0), (813, Int.negSucc 0), (815, Int.ofNat
    2)] },
  { level := 1, parent := 63, color := 26, mode := 1,
    vector := [(34, Int.ofNat 1), (92, Int.negSucc 1), (651, Int.ofNat 1), (710, Int.negSucc 0)]
    },
  { level := 1, parent := 63, color := 27, mode := 1,
    vector := [(38, Int.ofNat 1), (96, Int.negSucc 1), (475, Int.negSucc 0)] },
  { level := 1, parent := 65, color := 23, mode := 1,
    vector := [(135, Int.ofNat 2), (736, Int.negSucc 1)] },
  { level := 1, parent := 65, color := 24, mode := 1,
    vector := [(133, Int.negSucc 1), (737, Int.negSucc 1)] },
  { level := 1, parent := 65, color := 26, mode := 1,
    vector := [(33, Int.ofNat 2), (91, Int.negSucc 3), (116, Int.negSucc 1), (117, Int.ofNat 2),
    (118, Int.negSucc 1), (119, Int.negSucc 1), (144, Int.ofNat 2), (739, Int.negSucc 1), (816,
    Int.ofNat 2)] },
  { level := 1, parent := 65, color := 27, mode := 1,
    vector := [(37, Int.ofNat 2), (95, Int.negSucc 3), (122, Int.ofNat 2)] },
  { level := 1, parent := 66, color := 24, mode := 1,
    vector := [(0, Int.negSucc 1), (2, Int.ofNat 2), (3, Int.negSucc 1), (28, Int.ofNat 2), (29,
    Int.ofNat 4), (31, Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (58, Int.negSucc
    1), (60, Int.ofNat 2), (61, Int.negSucc 1), (86, Int.ofNat 2), (87, Int.negSucc 1), (89,
    Int.ofNat 2), (90, Int.negSucc 1), (115, Int.ofNat 2), (468, Int.ofNat 2), (558, Int.ofNat 2),
    (588, Int.ofNat 2), (648, Int.ofNat 2), (812, Int.ofNat 2), (813, Int.negSucc 3), (814,
    Int.ofNat 2), (815, Int.ofNat 2)] },
  { level := 1, parent := 66, color := 26, mode := 1,
    vector := [(5, Int.negSucc 1), (34, Int.ofNat 4), (63, Int.negSucc 1), (92, Int.negSucc 1),
    (591, Int.ofNat 2), (651, Int.ofNat 2), (710, Int.negSucc 1)] },
  { level := 1, parent := 66, color := 27, mode := 1,
    vector := [(9, Int.negSucc 1), (38, Int.ofNat 4), (67, Int.negSucc 1), (96, Int.negSucc 1),
    (475, Int.negSucc 1), (564, Int.ofNat 2), (711, Int.ofNat 2)] },
  { level := 1, parent := 67, color := 27, mode := 1,
    vector := [(533, Int.ofNat 4), (652, Int.ofNat 4)] },
  { level := 1, parent := 68, color := 24, mode := 1,
    vector := [(220, Int.negSucc 0), (500, Int.ofNat 1), (619, Int.negSucc 0), (679, Int.ofNat 1)]
    },
  { level := 1, parent := 68, color := 25, mode := 1,
    vector := [(219, Int.negSucc 0), (471, Int.ofNat 1), (590, Int.negSucc 0), (680, Int.ofNat 1)]
    },
  { level := 1, parent := 68, color := 26, mode := 1,
    vector := [(7, Int.negSucc 2), (36, Int.ofNat 3), (65, Int.negSucc 0), (94, Int.negSucc 0),
    (203, Int.negSucc 0), (204, Int.ofNat 1), (205, Int.negSucc 0), (206, Int.negSucc 0), (231,
    Int.ofNat 1), (592, Int.negSucc 0), (622, Int.negSucc 0), (681, Int.ofNat 2), (819, Int.ofNat
    1)] },
  { level := 1, parent := 68, color := 27, mode := 1,
    vector := [(10, Int.ofNat 3), (39, Int.negSucc 2), (68, Int.ofNat 1), (97, Int.ofNat 1), (209,
    Int.ofNat 1), (476, Int.ofNat 1), (506, Int.ofNat 1), (682, Int.negSucc 0)] },
  { level := 1, parent := 69, color := 23, mode := 1,
    vector := [(164, Int.ofNat 1), (556, Int.negSucc 0), (647, Int.ofNat 1), (707, Int.negSucc 0)]
    }
]

end VOA.DeligneAudit.D4Two.Certificate

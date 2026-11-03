/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData04 : List WordNode := [
  { level := 0, parent := 95, color := 16, mode := 0,
    vector := [(18, Int.ofNat 6), (47, Int.negSucc 7), (76, Int.ofNat 2), (105, Int.ofNat 6),
    (136, Int.negSucc 1), (225, Int.ofNat 2), (522, Int.ofNat 6), (523, Int.negSucc 7), (524,
    Int.ofNat 2), (525, Int.ofNat 6), (584, Int.negSucc 1), (645, Int.ofNat 2)] },
  { level := 0, parent := 96, color := 16, mode := 0,
    vector := [(167, Int.ofNat 2), (643, Int.ofNat 2)] },
  { level := 0, parent := 97, color := 18, mode := 0,
    vector := [(19, Int.negSucc 3), (48, Int.ofNat 10), (77, Int.negSucc 3), (106, Int.negSucc 7),
    (196, Int.negSucc 5), (256, Int.ofNat 2), (551, Int.negSucc 3), (552, Int.ofNat 10), (553,
    Int.negSucc 3), (554, Int.negSucc 7), (644, Int.negSucc 5), (704, Int.ofNat 2)] },
  { level := 0, parent := 98, color := 18, mode := 0,
    vector := [(17, Int.negSucc 3), (46, Int.ofNat 6), (75, Int.negSucc 1), (104, Int.negSucc 3),
    (195, Int.ofNat 4), (255, Int.negSucc 0), (315, Int.negSucc 0), (493, Int.negSucc 3), (494,
    Int.ofNat 6), (495, Int.negSucc 1), (496, Int.negSucc 3), (615, Int.ofNat 4), (675,
    Int.negSucc 0), (735, Int.negSucc 0)] },
  { level := 0, parent := 99, color := 18, mode := 0,
    vector := [(19, Int.negSucc 1), (48, Int.ofNat 6), (77, Int.negSucc 3), (106, Int.negSucc 3),
    (196, Int.negSucc 3), (256, Int.ofNat 1), (286, Int.ofNat 1), (551, Int.negSucc 1), (552,
    Int.ofNat 6), (553, Int.negSucc 3), (554, Int.negSucc 3), (644, Int.negSucc 3), (704,
    Int.ofNat 1), (734, Int.ofNat 1)] },
  { level := 0, parent := 101, color := 16, mode := 0,
    vector := [(18, Int.ofNat 1), (47, Int.negSucc 3), (76, Int.ofNat 1), (105, Int.ofNat 5),
    (136, Int.negSucc 2), (166, Int.negSucc 0), (225, Int.ofNat 1), (433, Int.ofNat 1), (522,
    Int.ofNat 1), (523, Int.negSucc 3), (524, Int.ofNat 1), (525, Int.ofNat 5), (584, Int.negSucc
    2), (614, Int.negSucc 0), (645, Int.ofNat 1), (797, Int.ofNat 1)] },
  { level := 0, parent := 104, color := 18, mode := 0,
    vector := [(19, Int.negSucc 11), (48, Int.ofNat 12), (77, Int.negSucc 3), (106, Int.negSucc
    3), (196, Int.negSucc 3), (551, Int.negSucc 11), (552, Int.ofNat 12), (553, Int.negSucc 3),
    (554, Int.negSucc 3), (644, Int.negSucc 3)] },
  { level := 0, parent := 106, color := 18, mode := 0,
    vector := [(190, Int.ofNat 4), (470, Int.ofNat 4)] },
  { level := 0, parent := 106, color := 16, mode := 0,
    vector := [(30, Int.ofNat 8), (32, Int.negSucc 15), (88, Int.negSucc 15), (90, Int.ofNat 32),
    (132, Int.negSucc 7), (468, Int.negSucc 7)] },
  { level := 0, parent := 107, color := 19, mode := 0,
    vector := [(219, Int.negSucc 1), (310, Int.ofNat 2), (471, Int.negSucc 1), (590, Int.ofNat 2)]
    },
  { level := 0, parent := 107, color := 17, mode := 0,
    vector := [(161, Int.negSucc 1), (281, Int.negSucc 1), (469, Int.negSucc 1), (589, Int.negSucc
    1)] },
  { level := 0, parent := 107, color := 16, mode := 0,
    vector := [(1, Int.negSucc 1), (3, Int.ofNat 4), (29, Int.negSucc 1), (30, Int.ofNat 12), (31,
    Int.negSucc 1), (32, Int.negSucc 17), (59, Int.negSucc 1), (61, Int.ofNat 4), (87, Int.ofNat
    4), (88, Int.negSucc 17), (89, Int.ofNat 4), (90, Int.ofNat 24), (132, Int.negSucc 5), (192,
    Int.negSucc 1), (252, Int.negSucc 1), (468, Int.negSucc 5), (528, Int.negSucc 1), (588,
    Int.negSucc 1)] },
  { level := 0, parent := 108, color := 16, mode := 0,
    vector := [(134, Int.ofNat 12), (526, Int.ofNat 12)] },
  { level := 0, parent := 109, color := 17, mode := 0,
    vector := [(310, Int.ofNat 2), (400, Int.negSucc 1), (590, Int.ofNat 2), (680, Int.negSucc 1)]
    },
  { level := 0, parent := 109, color := 16, mode := 0,
    vector := [(311, Int.ofNat 2), (371, Int.negSucc 1), (619, Int.ofNat 2), (679, Int.negSucc 1)]
    },
  { level := 0, parent := 110, color := 16, mode := 0,
    vector := [(30, Int.ofNat 4), (31, Int.negSucc 3), (32, Int.negSucc 3), (59, Int.negSucc 3),
    (61, Int.ofNat 8), (88, Int.negSucc 3), (89, Int.ofNat 8), (192, Int.negSucc 1), (252,
    Int.negSucc 1), (282, Int.negSucc 1), (342, Int.ofNat 2), (528, Int.negSucc 1), (588,
    Int.negSucc 1), (618, Int.negSucc 1), (678, Int.ofNat 2)] },
  { level := 0, parent := 111, color := 18, mode := 0,
    vector := [(191, Int.ofNat 4), (499, Int.ofNat 4)] },
  { level := 0, parent := 111, color := 16, mode := 0,
    vector := [(133, Int.negSucc 3), (253, Int.negSucc 3), (497, Int.negSucc 3), (617, Int.negSucc
    3)] },
  { level := 0, parent := 113, color := 16, mode := 0,
    vector := [(221, Int.ofNat 4), (529, Int.ofNat 4)] },
  { level := 0, parent := 114, color := 16, mode := 0,
    vector := [(163, Int.ofNat 4), (527, Int.ofNat 4)] },
  { level := 0, parent := 115, color := 18, mode := 0,
    vector := [(0, Int.ofNat 8), (1, Int.negSucc 19), (2, Int.ofNat 8), (3, Int.ofNat 16), (29,
    Int.negSucc 19), (30, Int.ofNat 48), (31, Int.negSucc 19), (32, Int.negSucc 35), (58,
    Int.ofNat 8), (59, Int.negSucc 19), (60, Int.ofNat 8), (61, Int.ofNat 16), (87, Int.ofNat 16),
    (88, Int.negSucc 35), (89, Int.ofNat 16), (90, Int.ofNat 24), (132, Int.negSucc 3), (192,
    Int.negSucc 11), (252, Int.negSucc 3), (468, Int.negSucc 3), (528, Int.negSucc 11), (588,
    Int.negSucc 3)] },
  { level := 0, parent := 116, color := 18, mode := 0,
    vector := [(220, Int.negSucc 1), (311, Int.ofNat 2), (500, Int.negSucc 1), (619, Int.ofNat 2)]
    },
  { level := 0, parent := 117, color := 18, mode := 0,
    vector := [(0, Int.ofNat 4), (1, Int.negSucc 11), (2, Int.ofNat 8), (3, Int.ofNat 8), (29,
    Int.negSucc 11), (30, Int.ofNat 32), (31, Int.negSucc 19), (32, Int.negSucc 19), (58,
    Int.ofNat 8), (59, Int.negSucc 19), (60, Int.ofNat 12), (61, Int.ofNat 12), (87, Int.ofNat 8),
    (88, Int.negSucc 19), (89, Int.ofNat 12), (90, Int.ofNat 12), (132, Int.negSucc 1), (162,
    Int.negSucc 1), (192, Int.negSucc 7), (252, Int.negSucc 1), (282, Int.negSucc 1), (468,
    Int.negSucc 1), (498, Int.negSucc 1), (528, Int.negSucc 7), (588, Int.negSucc 1), (618,
    Int.negSucc 1)] },
  { level := 0, parent := 119, color := 17, mode := 0,
    vector := [(1, Int.negSucc 1), (2, Int.ofNat 4), (29, Int.negSucc 1), (30, Int.ofNat 12), (31,
    Int.negSucc 17), (32, Int.negSucc 1), (58, Int.ofNat 4), (59, Int.negSucc 17), (60, Int.ofNat
    24), (61, Int.ofNat 4), (88, Int.negSucc 1), (89, Int.ofNat 4), (162, Int.negSucc 5), (192,
    Int.negSucc 1), (282, Int.negSucc 1), (498, Int.negSucc 5), (528, Int.negSucc 1), (618,
    Int.negSucc 1)] },
  { level := 0, parent := 120, color := 17, mode := 0,
    vector := [(281, Int.negSucc 0), (401, Int.ofNat 1), (589, Int.negSucc 0), (709, Int.ofNat 1)]
    },
  { level := 0, parent := 120, color := 16, mode := 0,
    vector := [(1, Int.negSucc 1), (3, Int.ofNat 4), (29, Int.negSucc 1), (30, Int.ofNat 2), (32,
    Int.negSucc 1), (87, Int.ofNat 4), (88, Int.negSucc 1), (192, Int.negSucc 0), (252,
    Int.negSucc 0), (312, Int.negSucc 0), (372, Int.ofNat 1), (528, Int.negSucc 0), (588,
    Int.negSucc 0), (648, Int.negSucc 0), (708, Int.ofNat 1)] },
  { level := 0, parent := 121, color := 16, mode := 0,
    vector := [(283, Int.ofNat 1), (343, Int.negSucc 0), (647, Int.ofNat 1), (707, Int.negSucc 0)]
    },
  { level := 0, parent := 122, color := 18, mode := 0,
    vector := [(193, Int.ofNat 2), (557, Int.ofNat 2)] },
  { level := 0, parent := 122, color := 16, mode := 0,
    vector := [(135, Int.negSucc 1), (254, Int.ofNat 2), (555, Int.negSucc 1), (646, Int.ofNat 2)]
    },
  { level := 0, parent := 124, color := 16, mode := 0,
    vector := [(192, Int.negSucc 0), (252, Int.negSucc 0), (282, Int.negSucc 0), (312, Int.negSucc
    0), (342, Int.ofNat 1), (372, Int.ofNat 1), (402, Int.ofNat 1), (432, Int.negSucc 0), (528,
    Int.negSucc 0), (588, Int.negSucc 0), (618, Int.negSucc 0), (648, Int.negSucc 0), (678,
    Int.ofNat 1), (708, Int.ofNat 1), (738, Int.ofNat 1), (768, Int.negSucc 0)] },
  { level := 0, parent := 125, color := 16, mode := 0,
    vector := [(253, Int.negSucc 1), (373, Int.ofNat 2), (617, Int.negSucc 1), (737, Int.ofNat 2)]
    },
  { level := 0, parent := 126, color := 16, mode := 0,
    vector := [(254, Int.ofNat 2), (344, Int.negSucc 1), (646, Int.ofNat 2), (736, Int.negSucc 1)]
    }
]

end VOA.DeligneAudit.D4Two.Certificate

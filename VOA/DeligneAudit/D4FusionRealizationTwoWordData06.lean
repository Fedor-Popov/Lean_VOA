/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData06 : List WordNode := [
  { level := 0, parent := 160, color := 19, mode := 0,
    vector := [(7, Int.ofNat 16), (36, Int.negSucc 21), (65, Int.ofNat 8), (94, Int.ofNat 12),
    (203, Int.ofNat 16), (204, Int.negSucc 21), (205, Int.ofNat 8), (206, Int.ofNat 12), (308,
    Int.negSucc 9), (368, Int.negSucc 1), (532, Int.negSucc 9), (592, Int.negSucc 1)] },
  { level := 0, parent := 160, color := 17, mode := 0,
    vector := [(5, Int.ofNat 8), (34, Int.negSucc 11), (63, Int.ofNat 4), (92, Int.ofNat 8), (145,
    Int.ofNat 8), (146, Int.negSucc 11), (147, Int.ofNat 4), (148, Int.ofNat 8), (279, Int.ofNat
    8), (339, Int.ofNat 2), (399, Int.ofNat 2), (531, Int.ofNat 8), (591, Int.ofNat 2), (651,
    Int.ofNat 2)] },
  { level := 0, parent := 165, color := 17, mode := 0,
    vector := [(393, Int.negSucc 3), (477, Int.negSucc 3)] },
  { level := 0, parent := 165, color := 16, mode := 0,
    vector := [(39, Int.ofNat 4), (97, Int.negSucc 7), (291, Int.ofNat 4), (293, Int.negSucc 7),
    (364, Int.negSucc 3), (476, Int.negSucc 3)] },
  { level := 0, parent := 166, color := 16, mode := 0,
    vector := [(38, Int.negSucc 3), (96, Int.ofNat 8), (262, Int.negSucc 3), (264, Int.ofNat 8),
    (335, Int.ofNat 4), (475, Int.ofNat 4)] },
  { level := 0, parent := 167, color := 18, mode := 0,
    vector := [(180, Int.ofNat 8)] },
  { level := 0, parent := 167, color := 16, mode := 0,
    vector := [(37, Int.negSucc 7), (95, Int.ofNat 16), (122, Int.negSucc 7), (178, Int.negSucc
    7), (233, Int.negSucc 7), (235, Int.ofNat 16)] },
  { level := 0, parent := 168, color := 16, mode := 0,
    vector := [(120, Int.ofNat 96)] },
  { level := 0, parent := 169, color := 16, mode := 0,
    vector := [(395, Int.ofNat 2), (426, Int.ofNat 2), (535, Int.ofNat 2), (594, Int.ofNat 2)] },
  { level := 0, parent := 170, color := 18, mode := 0,
    vector := [(10, Int.negSucc 1), (39, Int.ofNat 6), (68, Int.negSucc 1), (97, Int.negSucc 5),
    (181, Int.negSucc 1), (209, Int.negSucc 1), (290, Int.negSucc 1), (291, Int.ofNat 6), (292,
    Int.negSucc 1), (293, Int.negSucc 5), (364, Int.negSucc 1), (476, Int.negSucc 1)] },
  { level := 0, parent := 170, color := 16, mode := 0,
    vector := [(123, Int.ofNat 4), (207, Int.ofNat 4), (366, Int.ofNat 4), (534, Int.ofNat 4)] },
  { level := 0, parent := 171, color := 18, mode := 0,
    vector := [(9, Int.ofNat 2), (38, Int.negSucc 5), (67, Int.ofNat 2), (96, Int.ofNat 6), (151,
    Int.negSucc 1), (179, Int.negSucc 1), (261, Int.ofNat 2), (262, Int.negSucc 5), (263,
    Int.ofNat 2), (264, Int.ofNat 6), (335, Int.ofNat 2), (475, Int.ofNat 2)] },
  { level := 0, parent := 171, color := 16, mode := 0,
    vector := [(121, Int.ofNat 4), (149, Int.ofNat 4), (337, Int.negSucc 3), (533, Int.negSucc 3)]
    },
  { level := 0, parent := 172, color := 16, mode := 0,
    vector := [(8, Int.ofNat 4), (37, Int.negSucc 23), (66, Int.ofNat 4), (95, Int.ofNat 36),
    (122, Int.negSucc 19), (178, Int.negSucc 19), (232, Int.ofNat 4), (233, Int.negSucc 23), (234,
    Int.ofNat 4), (235, Int.ofNat 36)] },
  { level := 0, parent := 174, color := 18, mode := 0,
    vector := [(10, Int.negSucc 1), (39, Int.ofNat 4), (68, Int.negSucc 1), (97, Int.negSucc 1),
    (290, Int.negSucc 1), (291, Int.ofNat 4), (292, Int.negSucc 1), (293, Int.negSucc 1), (364,
    Int.negSucc 1), (394, Int.negSucc 1), (458, Int.ofNat 2), (476, Int.negSucc 1), (506,
    Int.negSucc 1), (682, Int.ofNat 2)] },
  { level := 0, parent := 174, color := 16, mode := 0,
    vector := [(366, Int.ofNat 4), (427, Int.ofNat 4), (534, Int.ofNat 4), (623, Int.ofNat 4)] },
  { level := 0, parent := 175, color := 17, mode := 0,
    vector := [(39, Int.ofNat 2), (68, Int.negSucc 3), (291, Int.ofNat 2), (292, Int.negSucc 3),
    (394, Int.negSucc 1), (506, Int.negSucc 1)] },
  { level := 0, parent := 175, color := 16, mode := 0,
    vector := [(365, Int.negSucc 1), (505, Int.negSucc 1)] },
  { level := 0, parent := 177, color := 17, mode := 0,
    vector := [(9, Int.ofNat 2), (38, Int.negSucc 9), (67, Int.ofNat 10), (96, Int.ofNat 6), (151,
    Int.negSucc 5), (179, Int.negSucc 5), (261, Int.ofNat 2), (262, Int.negSucc 9), (263,
    Int.ofNat 10), (264, Int.ofNat 6), (335, Int.ofNat 2), (475, Int.ofNat 2)] },
  { level := 0, parent := 177, color := 16, mode := 0,
    vector := [(8, Int.ofNat 2), (37, Int.negSucc 9), (66, Int.ofNat 6), (95, Int.ofNat 10), (122,
    Int.negSucc 5), (178, Int.negSucc 5), (232, Int.ofNat 2), (233, Int.negSucc 9), (234,
    Int.ofNat 6), (235, Int.ofNat 10), (336, Int.ofNat 2), (504, Int.ofNat 2)] },
  { level := 0, parent := 180, color := 19, mode := 0,
    vector := [(210, Int.ofNat 8)] },
  { level := 0, parent := 180, color := 17, mode := 0,
    vector := [(152, Int.ofNat 4), (208, Int.ofNat 4), (395, Int.ofNat 4), (535, Int.ofNat 4)] },
  { level := 0, parent := 181, color := 17, mode := 0,
    vector := [(150, Int.ofNat 8)] },
  { level := 0, parent := 184, color := 18, mode := 0,
    vector := [(9, Int.ofNat 1), (38, Int.negSucc 1), (67, Int.ofNat 1), (96, Int.ofNat 1), (261,
    Int.ofNat 1), (262, Int.negSucc 1), (263, Int.ofNat 1), (264, Int.ofNat 1), (335, Int.ofNat
    1), (396, Int.negSucc 0), (459, Int.negSucc 0), (475, Int.ofNat 1), (564, Int.negSucc 0),
    (711, Int.negSucc 0)] },
  { level := 0, parent := 184, color := 16, mode := 0,
    vector := [(337, Int.negSucc 1), (428, Int.negSucc 1), (533, Int.negSucc 1), (652, Int.negSucc
    1)] },
  { level := 0, parent := 185, color := 19, mode := 0,
    vector := [(10, Int.negSucc 4), (39, Int.ofNat 5), (68, Int.negSucc 0), (97, Int.negSucc 2),
    (181, Int.negSucc 2), (209, Int.negSucc 2), (290, Int.negSucc 4), (291, Int.ofNat 5), (292,
    Int.negSucc 0), (293, Int.negSucc 2), (364, Int.negSucc 0), (476, Int.negSucc 0)] },
  { level := 0, parent := 185, color := 17, mode := 0,
    vector := [(9, Int.ofNat 3), (38, Int.negSucc 3), (67, Int.ofNat 1), (96, Int.ofNat 3), (151,
    Int.negSucc 0), (179, Int.negSucc 0), (261, Int.ofNat 3), (262, Int.negSucc 3), (263,
    Int.ofNat 1), (264, Int.ofNat 3), (335, Int.ofNat 1), (396, Int.negSucc 0), (475, Int.ofNat
    1), (564, Int.negSucc 0)] },
  { level := 0, parent := 185, color := 16, mode := 0,
    vector := [(8, Int.ofNat 3), (37, Int.negSucc 4), (66, Int.ofNat 1), (95, Int.ofNat 5), (122,
    Int.negSucc 2), (178, Int.negSucc 2), (232, Int.ofNat 3), (233, Int.negSucc 4), (234,
    Int.ofNat 1), (235, Int.ofNat 5), (367, Int.negSucc 0), (563, Int.negSucc 0)] },
  { level := 0, parent := 187, color := 16, mode := 0,
    vector := [(338, Int.ofNat 1), (562, Int.ofNat 1)] },
  { level := 0, parent := 190, color := 16, mode := 0,
    vector := [(8, Int.ofNat 1), (37, Int.negSucc 2), (66, Int.ofNat 1), (95, Int.ofNat 3), (122,
    Int.negSucc 0), (178, Int.negSucc 0), (232, Int.ofNat 1), (233, Int.negSucc 2), (234,
    Int.ofNat 1), (235, Int.ofNat 3), (336, Int.ofNat 1), (367, Int.negSucc 0), (460, Int.negSucc
    0), (504, Int.ofNat 1), (563, Int.negSucc 0), (740, Int.negSucc 0)] },
  { level := 0, parent := 194, color := 16, mode := 0,
    vector := [(42, Int.negSucc 3), (100, Int.ofNat 8), (378, Int.negSucc 3), (380, Int.ofNat 8),
    (422, Int.ofNat 4), (478, Int.ofNat 4)] },
  { level := 0, parent := 195, color := 18, mode := 0,
    vector := [(184, Int.ofNat 4), (296, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData17 : List WordNode := [
  { level := 1, parent := 69, color := 25, mode := 1,
    vector := [(161, Int.negSucc 0), (469, Int.ofNat 1), (589, Int.ofNat 1), (709, Int.negSucc 0)]
    },
  { level := 1, parent := 69, color := 26, mode := 1,
    vector := [(5, Int.negSucc 0), (34, Int.ofNat 3), (63, Int.negSucc 2), (92, Int.negSucc 0),
    (145, Int.negSucc 0), (146, Int.ofNat 1), (147, Int.negSucc 0), (148, Int.negSucc 0), (173,
    Int.ofNat 1), (591, Int.ofNat 1), (651, Int.ofNat 1), (710, Int.negSucc 1), (817, Int.ofNat
    1)] },
  { level := 1, parent := 69, color := 27, mode := 1,
    vector := [(9, Int.negSucc 0), (38, Int.ofNat 3), (67, Int.negSucc 2), (96, Int.negSucc 0),
    (151, Int.ofNat 1), (475, Int.negSucc 0), (564, Int.ofNat 1), (711, Int.ofNat 1)] },
  { level := 1, parent := 70, color := 25, mode := 1,
    vector := [(0, Int.negSucc 0), (2, Int.negSucc 0), (3, Int.ofNat 1), (28, Int.ofNat 1), (29,
    Int.ofNat 3), (31, Int.ofNat 3), (32, Int.negSucc 2), (57, Int.negSucc 2), (58, Int.negSucc
    0), (60, Int.negSucc 0), (61, Int.ofNat 1), (86, Int.ofNat 1), (87, Int.negSucc 2), (89,
    Int.negSucc 2), (90, Int.ofNat 3), (115, Int.ofNat 3), (132, Int.negSucc 0), (498, Int.ofNat
    1), (558, Int.ofNat 1), (618, Int.ofNat 1), (648, Int.ofNat 1), (738, Int.ofNat 1), (768,
    Int.negSucc 0), (812, Int.ofNat 1), (813, Int.negSucc 2), (814, Int.ofNat 1), (815, Int.ofNat
    3)] },
  { level := 1, parent := 70, color := 26, mode := 1,
    vector := [(4, Int.negSucc 0), (33, Int.ofNat 3), (62, Int.negSucc 0), (91, Int.negSucc 2),
    (116, Int.negSucc 0), (117, Int.ofNat 1), (118, Int.negSucc 0), (119, Int.negSucc 0), (144,
    Int.ofNat 1), (620, Int.ofNat 1), (650, Int.ofNat 1), (739, Int.negSucc 1), (816, Int.ofNat
    1)] },
  { level := 1, parent := 70, color := 27, mode := 1,
    vector := [(8, Int.negSucc 0), (37, Int.ofNat 3), (66, Int.negSucc 0), (95, Int.negSucc 2),
    (122, Int.ofNat 1), (504, Int.negSucc 0), (563, Int.ofNat 1), (740, Int.ofNat 1)] },
  { level := 1, parent := 71, color := 25, mode := 1,
    vector := [(29, Int.ofNat 1), (31, Int.ofNat 1), (32, Int.negSucc 0), (57, Int.negSucc 0),
    (58, Int.negSucc 1), (60, Int.negSucc 1), (61, Int.ofNat 2), (86, Int.ofNat 2), (498,
    Int.ofNat 1), (648, Int.ofNat 1), (738, Int.negSucc 0), (813, Int.negSucc 0), (814, Int.ofNat
    2)] },
  { level := 1, parent := 71, color := 26, mode := 1,
    vector := [(33, Int.ofNat 1), (62, Int.negSucc 1), (650, Int.ofNat 1), (739, Int.negSucc 0)]
    },
  { level := 1, parent := 71, color := 27, mode := 1,
    vector := [(37, Int.ofNat 1), (66, Int.negSucc 1), (504, Int.negSucc 0)] },
  { level := 1, parent := 72, color := 27, mode := 1,
    vector := [(10, Int.ofNat 1), (39, Int.negSucc 2), (68, Int.ofNat 1), (97, Int.ofNat 3), (209,
    Int.ofNat 1), (291, Int.negSucc 0), (318, Int.ofNat 1), (476, Int.ofNat 1), (682, Int.negSucc
    0), (822, Int.ofNat 1)] },
  { level := 1, parent := 73, color := 27, mode := 1,
    vector := [(9, Int.negSucc 0), (38, Int.ofNat 3), (67, Int.negSucc 0), (96, Int.negSucc 2),
    (151, Int.ofNat 1), (262, Int.ofNat 1), (289, Int.negSucc 0), (475, Int.negSucc 0), (711,
    Int.ofNat 1), (821, Int.negSucc 0)] },
  { level := 1, parent := 74, color := 27, mode := 1,
    vector := [(8, Int.negSucc 0), (37, Int.ofNat 4), (66, Int.negSucc 0), (95, Int.negSucc 4),
    (122, Int.ofNat 3), (233, Int.ofNat 1), (260, Int.negSucc 0), (740, Int.ofNat 1), (820,
    Int.negSucc 0)] },
  { level := 1, parent := 75, color := 24, mode := 1,
    vector := [(0, Int.negSucc 7), (2, Int.ofNat 8), (3, Int.negSucc 7), (28, Int.ofNat 8), (29,
    Int.ofNat 4), (31, Int.negSucc 3), (32, Int.ofNat 4), (57, Int.negSucc 3), (558, Int.ofNat 4),
    (588, Int.ofNat 4), (708, Int.negSucc 3), (812, Int.ofNat 8), (813, Int.negSucc 3)] },
  { level := 1, parent := 75, color := 26, mode := 1,
    vector := [(5, Int.negSucc 7), (34, Int.ofNat 4), (591, Int.ofNat 4), (710, Int.negSucc 3)] },
  { level := 1, parent := 75, color := 27, mode := 1,
    vector := [(9, Int.negSucc 7), (38, Int.ofNat 4), (564, Int.ofNat 4)] },
  { level := 1, parent := 76, color := 27, mode := 1,
    vector := [(562, Int.negSucc 3)] },
  { level := 1, parent := 77, color := 25, mode := 1,
    vector := [(0, Int.negSucc 3), (2, Int.negSucc 3), (3, Int.ofNat 4), (28, Int.ofNat 4), (29,
    Int.ofNat 2), (31, Int.ofNat 2), (32, Int.negSucc 1), (57, Int.negSucc 1), (558, Int.ofNat 2),
    (618, Int.ofNat 2), (738, Int.negSucc 1), (812, Int.ofNat 4), (813, Int.negSucc 1)] },
  { level := 1, parent := 77, color := 26, mode := 1,
    vector := [(4, Int.negSucc 3), (33, Int.ofNat 2), (620, Int.ofNat 2), (739, Int.negSucc 1)] },
  { level := 1, parent := 77, color := 27, mode := 1,
    vector := [(8, Int.negSucc 3), (37, Int.ofNat 2), (563, Int.ofNat 2)] },
  { level := 1, parent := 79, color := 27, mode := 1,
    vector := [(42, Int.ofNat 2), (100, Int.negSucc 3), (478, Int.negSucc 1)] },
  { level := 1, parent := 80, color := 23, mode := 1,
    vector := [(174, Int.ofNat 2), (176, Int.negSucc 1), (177, Int.negSucc 1), (202, Int.ofNat 2),
    (472, Int.negSucc 1), (502, Int.negSucc 1), (818, Int.ofNat 2)] },
  { level := 1, parent := 80, color := 26, mode := 1,
    vector := [(181, Int.ofNat 2), (476, Int.negSucc 1), (506, Int.negSucc 1), (682, Int.ofNat 2)]
    },
  { level := 1, parent := 80, color := 27, mode := 1,
    vector := [(184, Int.negSucc 1)] },
  { level := 1, parent := 81, color := 23, mode := 1,
    vector := [(33, Int.negSucc 3), (91, Int.ofNat 8), (116, Int.negSucc 3), (118, Int.ofNat 4),
    (119, Int.ofNat 4), (144, Int.negSucc 3), (620, Int.ofNat 4), (816, Int.negSucc 3)] },
  { level := 1, parent := 81, color := 26, mode := 1,
    vector := [(123, Int.negSucc 3), (623, Int.ofNat 4)] },
  { level := 1, parent := 81, color := 27, mode := 1,
    vector := [(41, Int.ofNat 4), (99, Int.negSucc 7), (126, Int.ofNat 4)] },
  { level := 1, parent := 82, color := 27, mode := 1,
    vector := [(13, Int.negSucc 3), (42, Int.ofNat 8), (71, Int.negSucc 3), (100, Int.negSucc 3),
    (478, Int.negSucc 3), (595, Int.negSucc 3)] },
  { level := 1, parent := 83, color := 27, mode := 1,
    vector := [(536, Int.ofNat 8)] },
  { level := 1, parent := 84, color := 27, mode := 1,
    vector := [(213, Int.ofNat 2)] },
  { level := 1, parent := 85, color := 23, mode := 1,
    vector := [(5, Int.ofNat 2), (34, Int.negSucc 5), (63, Int.ofNat 6), (92, Int.ofNat 2), (145,
    Int.negSucc 1), (147, Int.ofNat 2), (148, Int.ofNat 2), (173, Int.negSucc 1), (531, Int.ofNat
    2), (591, Int.ofNat 2), (817, Int.negSucc 1)] },
  { level := 1, parent := 85, color := 26, mode := 1,
    vector := [(152, Int.negSucc 1), (535, Int.ofNat 2), (594, Int.ofNat 4)] },
  { level := 1, parent := 85, color := 27, mode := 1,
    vector := [(13, Int.negSucc 1), (42, Int.ofNat 6), (71, Int.negSucc 5), (100, Int.negSucc 1),
    (155, Int.ofNat 2), (478, Int.negSucc 1), (595, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

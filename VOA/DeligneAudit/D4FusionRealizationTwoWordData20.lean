/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData20 : List WordNode := [
  { level := 1, parent := 143, color := 26, mode := 1,
    vector := [(43, Int.ofNat 4), (72, Int.negSucc 3), (101, Int.negSucc 3), (326, Int.ofNat 2),
    (537, Int.negSucc 1)] },
  { level := 1, parent := 143, color := 27, mode := 1,
    vector := [(188, Int.negSucc 1), (245, Int.negSucc 1), (273, Int.negSucc 1), (329, Int.negSucc
    1)] },
  { level := 1, parent := 145, color := 27, mode := 1,
    vector := [(244, Int.negSucc 3)] },
  { level := 1, parent := 146, color := 27, mode := 1,
    vector := [(217, Int.ofNat 4)] },
  { level := 1, parent := 147, color := 27, mode := 1,
    vector := [(159, Int.ofNat 4)] },
  { level := 1, parent := 148, color := 27, mode := 1,
    vector := [(15, Int.ofNat 8), (44, Int.negSucc 19), (73, Int.ofNat 8), (102, Int.ofNat 16),
    (188, Int.negSucc 11), (245, Int.negSucc 3)] },
  { level := 1, parent := 149, color := 27, mode := 1,
    vector := [(302, Int.ofNat 2)] },
  { level := 1, parent := 150, color := 27, mode := 1,
    vector := [(15, Int.ofNat 4), (44, Int.negSucc 11), (73, Int.ofNat 8), (102, Int.ofNat 8),
    (188, Int.negSucc 7), (245, Int.negSucc 1), (273, Int.negSucc 1)] },
  { level := 1, parent := 153, color := 24, mode := 1,
    vector := [(12, Int.negSucc 1), (41, Int.ofNat 2), (99, Int.negSucc 1), (239, Int.negSucc 0),
    (294, Int.ofNat 1), (348, Int.negSucc 0), (350, Int.ofNat 1), (351, Int.negSucc 0), (376,
    Int.ofNat 1), (824, Int.ofNat 1)] },
  { level := 1, parent := 153, color := 26, mode := 1,
    vector := [(14, Int.negSucc 1), (43, Int.ofNat 2), (101, Int.negSucc 1), (353, Int.negSucc 0),
    (537, Int.negSucc 0)] },
  { level := 1, parent := 153, color := 27, mode := 1,
    vector := [(188, Int.negSucc 0), (245, Int.negSucc 0), (301, Int.negSucc 0), (357, Int.negSucc
    0)] },
  { level := 1, parent := 156, color := 27, mode := 1,
    vector := [(243, Int.ofNat 2)] },
  { level := 1, parent := 160, color := 27, mode := 1,
    vector := [(15, Int.ofNat 8), (44, Int.negSucc 11), (73, Int.ofNat 4), (102, Int.ofNat 8),
    (188, Int.negSucc 7), (245, Int.negSucc 1), (301, Int.negSucc 1)] },
  { level := 1, parent := 161, color := 27, mode := 1,
    vector := [(272, Int.ofNat 2)] },
  { level := 1, parent := 162, color := 25, mode := 1,
    vector := [(13, Int.negSucc 3), (42, Int.ofNat 6), (71, Int.negSucc 1), (100, Int.negSucc 3),
    (155, Int.ofNat 2), (268, Int.negSucc 3), (295, Int.ofNat 1), (377, Int.negSucc 0), (379,
    Int.negSucc 0), (380, Int.ofNat 1), (405, Int.ofNat 1), (595, Int.ofNat 1), (825, Int.ofNat
    1)] },
  { level := 1, parent := 162, color := 26, mode := 1,
    vector := [(14, Int.negSucc 3), (43, Int.ofNat 10), (72, Int.negSucc 9), (101, Int.negSucc 3),
    (157, Int.ofNat 2), (326, Int.ofNat 1), (381, Int.negSucc 0), (537, Int.negSucc 3)] },
  { level := 1, parent := 162, color := 27, mode := 1,
    vector := [(44, Int.negSucc 1), (73, Int.ofNat 4), (188, Int.negSucc 3), (245, Int.negSucc 0),
    (273, Int.negSucc 3), (301, Int.negSucc 0), (329, Int.negSucc 0), (385, Int.negSucc 0)] },
  { level := 1, parent := 163, color := 27, mode := 1,
    vector := [(15, Int.ofNat 2), (44, Int.negSucc 5), (73, Int.ofNat 2), (102, Int.ofNat 6),
    (188, Int.negSucc 3), (245, Int.negSucc 2), (273, Int.negSucc 0), (301, Int.negSucc 0), (412,
    Int.negSucc 0), (436, Int.negSucc 0), (463, Int.ofNat 1), (827, Int.ofNat 1)] },
  { level := 1, parent := 170, color := 27, mode := 1,
    vector := [(304, Int.negSucc 1), (361, Int.negSucc 1)] },
  { level := 1, parent := 171, color := 27, mode := 1,
    vector := [(275, Int.ofNat 2), (332, Int.ofNat 2)] },
  { level := 1, parent := 172, color := 27, mode := 1,
    vector := [(189, Int.negSucc 3)] },
  { level := 1, parent := 173, color := 27, mode := 1,
    vector := [(131, Int.ofNat 4), (246, Int.ofNat 4)] },
  { level := 1, parent := 178, color := 27, mode := 1,
    vector := [(246, Int.ofNat 4), (331, Int.ofNat 4)] },
  { level := 1, parent := 180, color := 27, mode := 1,
    vector := [(218, Int.ofNat 4), (304, Int.negSucc 3)] },
  { level := 1, parent := 181, color := 27, mode := 1,
    vector := [(160, Int.ofNat 4), (275, Int.ofNat 4)] },
  { level := 1, parent := 182, color := 27, mode := 1,
    vector := [(304, Int.negSucc 1), (389, Int.negSucc 1)] },
  { level := 1, parent := 186, color := 27, mode := 1,
    vector := [(246, Int.ofNat 2), (359, Int.ofNat 2)] },
  { level := 1, parent := 193, color := 27, mode := 1,
    vector := [(160, Int.ofNat 4), (275, Int.ofNat 8), (332, Int.ofNat 2), (388, Int.ofNat 2)] },
  { level := 1, parent := 201, color := 27, mode := 1,
    vector := [(305, Int.negSucc 1)] },
  { level := 1, parent := 202, color := 27, mode := 1,
    vector := [(362, Int.ofNat 4)] },
  { level := 1, parent := 203, color := 27, mode := 1,
    vector := [(276, Int.ofNat 2)] },
  { level := 1, parent := 204, color := 27, mode := 1,
    vector := [(333, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

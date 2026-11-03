/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData08 : List WordNode := [
  { level := 0, parent := 229, color := 16, mode := 0,
    vector := [(14, Int.negSucc 1), (43, Int.ofNat 6), (72, Int.negSucc 1), (101, Int.negSucc 5),
    (129, Int.ofNat 2), (381, Int.ofNat 2), (406, Int.negSucc 1), (407, Int.ofNat 6), (408,
    Int.negSucc 1), (409, Int.negSucc 5), (453, Int.negSucc 1), (537, Int.negSucc 1)] },
  { level := 0, parent := 231, color := 16, mode := 0,
    vector := [(215, Int.ofNat 4), (355, Int.ofNat 4)] },
  { level := 0, parent := 232, color := 16, mode := 0,
    vector := [(14, Int.negSucc 1), (43, Int.ofNat 8), (72, Int.negSucc 1), (101, Int.negSucc 9),
    (129, Int.ofNat 6), (157, Int.ofNat 2), (214, Int.negSucc 1), (326, Int.negSucc 1), (353,
    Int.ofNat 2), (381, Int.ofNat 6), (406, Int.negSucc 1), (407, Int.ofNat 8), (408, Int.negSucc
    1), (409, Int.negSucc 9)] },
  { level := 0, parent := 234, color := 16, mode := 0,
    vector := [(156, Int.negSucc 3), (324, Int.negSucc 3)] },
  { level := 0, parent := 236, color := 16, mode := 0,
    vector := [(14, Int.negSucc 1), (43, Int.ofNat 8), (72, Int.negSucc 5), (101, Int.negSucc 5),
    (129, Int.ofNat 2), (157, Int.ofNat 2), (353, Int.ofNat 2), (381, Int.ofNat 2), (406,
    Int.negSucc 1), (407, Int.ofNat 8), (408, Int.negSucc 5), (409, Int.negSucc 5), (453,
    Int.negSucc 1), (537, Int.negSucc 1)] },
  { level := 0, parent := 237, color := 18, mode := 0,
    vector := [(186, Int.negSucc 5), (242, Int.negSucc 1), (298, Int.negSucc 1), (354, Int.negSucc
    5), (452, Int.ofNat 4), (508, Int.ofNat 4)] },
  { level := 0, parent := 240, color := 16, mode := 0,
    vector := [(14, Int.negSucc 2), (43, Int.ofNat 4), (72, Int.negSucc 0), (101, Int.negSucc 2),
    (129, Int.ofNat 1), (214, Int.negSucc 0), (326, Int.negSucc 0), (381, Int.ofNat 1), (406,
    Int.negSucc 2), (407, Int.ofNat 4), (408, Int.negSucc 0), (409, Int.negSucc 2), (453,
    Int.negSucc 0), (537, Int.negSucc 0)] },
  { level := 0, parent := 241, color := 18, mode := 0,
    vector := [(185, Int.ofNat 3), (241, Int.ofNat 1), (269, Int.ofNat 1), (325, Int.ofNat 3),
    (454, Int.ofNat 2), (566, Int.ofNat 2)] },
  { level := 0, parent := 244, color := 19, mode := 0,
    vector := [(303, Int.negSucc 3), (387, Int.negSucc 3)] },
  { level := 0, parent := 244, color := 17, mode := 0,
    vector := [(274, Int.ofNat 4), (386, Int.ofNat 4)] },
  { level := 0, parent := 244, color := 16, mode := 0,
    vector := [(44, Int.ofNat 4), (102, Int.negSucc 7), (188, Int.ofNat 4), (245, Int.ofNat 4),
    (385, Int.ofNat 4), (412, Int.ofNat 4), (436, Int.ofNat 4), (438, Int.negSucc 7)] },
  { level := 0, parent := 245, color := 16, mode := 0,
    vector := [(130, Int.negSucc 23), (410, Int.negSucc 23)] },
  { level := 0, parent := 246, color := 16, mode := 0,
    vector := [(302, Int.negSucc 7), (358, Int.negSucc 7)] },
  { level := 0, parent := 247, color := 16, mode := 0,
    vector := [(188, Int.ofNat 4), (245, Int.ofNat 4), (273, Int.ofNat 4), (301, Int.ofNat 4),
    (329, Int.ofNat 4), (357, Int.ofNat 4), (385, Int.ofNat 4), (412, Int.ofNat 4)] },
  { level := 0, parent := 248, color := 16, mode := 0,
    vector := [(244, Int.ofNat 8), (356, Int.ofNat 8)] },
  { level := 0, parent := 250, color := 16, mode := 0,
    vector := [(272, Int.negSucc 7), (328, Int.negSucc 7)] },
  { level := 0, parent := 251, color := 16, mode := 0,
    vector := [(243, Int.negSucc 7), (327, Int.negSucc 7)] },
  { level := 0, parent := 254, color := 16, mode := 0,
    vector := [(217, Int.negSucc 1), (413, Int.negSucc 1)] },
  { level := 0, parent := 255, color := 16, mode := 0,
    vector := [(159, Int.negSucc 1), (411, Int.negSucc 1)] },
  { level := 0, parent := 256, color := 18, mode := 0,
    vector := [(15, Int.negSucc 3), (44, Int.ofNat 10), (73, Int.negSucc 3), (102, Int.negSucc 7),
    (188, Int.ofNat 6), (245, Int.ofNat 2), (385, Int.ofNat 2), (412, Int.ofNat 6), (435,
    Int.negSucc 3), (436, Int.ofNat 10), (437, Int.negSucc 3), (438, Int.negSucc 7)] },
  { level := 0, parent := 260, color := 18, mode := 0,
    vector := [(15, Int.negSucc 3), (44, Int.ofNat 12), (73, Int.negSucc 7), (102, Int.negSucc 7),
    (188, Int.ofNat 8), (245, Int.ofNat 2), (273, Int.ofNat 2), (357, Int.ofNat 2), (385,
    Int.ofNat 2), (412, Int.ofNat 8), (435, Int.negSucc 3), (436, Int.ofNat 12), (437, Int.negSucc
    7), (438, Int.negSucc 7)] },
  { level := 0, parent := 262, color := 18, mode := 0,
    vector := [(15, Int.negSucc 3), (44, Int.ofNat 6), (73, Int.negSucc 1), (102, Int.negSucc 3),
    (188, Int.ofNat 4), (245, Int.ofNat 1), (301, Int.ofNat 1), (329, Int.ofNat 1), (385,
    Int.ofNat 1), (412, Int.ofNat 4), (435, Int.negSucc 3), (436, Int.ofNat 6), (437, Int.negSucc
    1), (438, Int.negSucc 3)] },
  { level := 0, parent := 264, color := 17, mode := 0,
    vector := [(390, Int.ofNat 8)] },
  { level := 0, parent := 264, color := 16, mode := 0,
    vector := [(304, Int.ofNat 4), (361, Int.ofNat 4), (389, Int.ofNat 4), (416, Int.ofNat 4)] },
  { level := 0, parent := 265, color := 16, mode := 0,
    vector := [(275, Int.negSucc 3), (332, Int.negSucc 3), (388, Int.negSucc 3), (415, Int.negSucc
    3)] },
  { level := 0, parent := 266, color := 18, mode := 0,
    vector := [(189, Int.ofNat 8), (441, Int.ofNat 8)] },
  { level := 0, parent := 266, color := 16, mode := 0,
    vector := [(131, Int.negSucc 7), (246, Int.negSucc 7), (414, Int.negSucc 7), (439, Int.negSucc
    7)] },
  { level := 0, parent := 268, color := 16, mode := 0,
    vector := [(360, Int.ofNat 16)] },
  { level := 0, parent := 269, color := 16, mode := 0,
    vector := [(246, Int.negSucc 7), (331, Int.negSucc 7), (359, Int.negSucc 7), (414, Int.negSucc
    7)] },
  { level := 0, parent := 271, color := 16, mode := 0,
    vector := [(330, Int.ofNat 16)] },
  { level := 0, parent := 273, color := 18, mode := 0,
    vector := [(218, Int.negSucc 1), (304, Int.ofNat 2), (416, Int.ofNat 2), (442, Int.negSucc 1)]
    },
  { level := 0, parent := 274, color := 18, mode := 0,
    vector := [(160, Int.negSucc 1), (275, Int.negSucc 1), (415, Int.negSucc 1), (440, Int.negSucc
    1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

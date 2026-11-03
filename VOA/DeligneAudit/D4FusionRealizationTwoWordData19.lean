/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData19 : List WordNode := [
  { level := 1, parent := 111, color := 23, mode := 1,
    vector := [(37, Int.negSucc 1), (95, Int.ofNat 4), (178, Int.negSucc 1), (232, Int.negSucc 1),
    (234, Int.ofNat 2), (235, Int.ofNat 2), (260, Int.negSucc 1), (504, Int.ofNat 2), (820,
    Int.negSucc 1)] },
  { level := 1, parent := 111, color := 26, mode := 1,
    vector := [(41, Int.negSucc 1), (99, Int.ofNat 4), (239, Int.negSucc 1), (507, Int.ofNat 2),
    (624, Int.ofNat 2)] },
  { level := 1, parent := 111, color := 27, mode := 1,
    vector := [(186, Int.ofNat 2), (242, Int.ofNat 2)] },
  { level := 1, parent := 112, color := 27, mode := 1,
    vector := [(128, Int.negSucc 11)] },
  { level := 1, parent := 113, color := 27, mode := 1,
    vector := [(216, Int.negSucc 3)] },
  { level := 1, parent := 114, color := 27, mode := 1,
    vector := [(158, Int.negSucc 3)] },
  { level := 1, parent := 115, color := 27, mode := 1,
    vector := [(14, Int.ofNat 4), (43, Int.negSucc 11), (72, Int.ofNat 4), (101, Int.ofNat 12),
    (129, Int.negSucc 3), (537, Int.ofNat 4)] },
  { level := 1, parent := 116, color := 27, mode := 1,
    vector := [(215, Int.negSucc 1)] },
  { level := 1, parent := 117, color := 27, mode := 1,
    vector := [(14, Int.ofNat 2), (43, Int.negSucc 7), (72, Int.ofNat 6), (101, Int.ofNat 6),
    (129, Int.negSucc 1), (157, Int.negSucc 1), (537, Int.ofNat 2)] },
  { level := 1, parent := 118, color := 27, mode := 1,
    vector := [(186, Int.ofNat 6), (242, Int.ofNat 2), (508, Int.negSucc 3)] },
  { level := 1, parent := 120, color := 24, mode := 1,
    vector := [(10, Int.ofNat 2), (39, Int.negSucc 0), (181, Int.ofNat 1), (290, Int.ofNat 1),
    (292, Int.negSucc 0), (293, Int.ofNat 1), (318, Int.negSucc 0), (476, Int.ofNat 1), (822,
    Int.negSucc 0)] },
  { level := 1, parent := 120, color := 26, mode := 1,
    vector := [(13, Int.ofNat 2), (42, Int.negSucc 0), (295, Int.ofNat 1), (478, Int.ofNat 1),
    (595, Int.ofNat 1)] },
  { level := 1, parent := 120, color := 27, mode := 1,
    vector := [(187, Int.ofNat 1), (299, Int.ofNat 1)] },
  { level := 1, parent := 122, color := 24, mode := 1,
    vector := [(37, Int.ofNat 1), (95, Int.negSucc 1), (178, Int.ofNat 1), (232, Int.negSucc 0),
    (234, Int.ofNat 1), (235, Int.negSucc 0), (260, Int.ofNat 1), (563, Int.ofNat 1), (820,
    Int.ofNat 1)] },
  { level := 1, parent := 122, color := 26, mode := 1,
    vector := [(40, Int.ofNat 1), (98, Int.negSucc 1), (237, Int.negSucc 0), (565, Int.ofNat 1),
    (653, Int.negSucc 0)] },
  { level := 1, parent := 122, color := 27, mode := 1,
    vector := [(185, Int.negSucc 0), (241, Int.negSucc 0)] },
  { level := 1, parent := 123, color := 27, mode := 1,
    vector := [(127, Int.ofNat 6)] },
  { level := 1, parent := 128, color := 27, mode := 1,
    vector := [(14, Int.ofNat 6), (43, Int.negSucc 7), (72, Int.ofNat 2), (101, Int.ofNat 6),
    (129, Int.negSucc 1), (214, Int.ofNat 2), (537, Int.ofNat 2)] },
  { level := 1, parent := 129, color := 27, mode := 1,
    vector := [(156, Int.ofNat 2)] },
  { level := 1, parent := 130, color := 27, mode := 1,
    vector := [(185, Int.negSucc 5), (241, Int.negSucc 1), (566, Int.negSucc 3)] },
  { level := 1, parent := 131, color := 25, mode := 1,
    vector := [(10, Int.ofNat 4), (39, Int.negSucc 5), (68, Int.ofNat 2), (97, Int.ofNat 4), (181,
    Int.ofNat 4), (290, Int.ofNat 1), (292, Int.ofNat 1), (293, Int.negSucc 0), (318, Int.negSucc
    0), (682, Int.ofNat 1), (822, Int.negSucc 0)] },
  { level := 1, parent := 131, color := 26, mode := 1,
    vector := [(12, Int.ofNat 4), (41, Int.negSucc 5), (70, Int.ofNat 2), (99, Int.ofNat 4), (239,
    Int.negSucc 0), (294, Int.ofNat 1), (507, Int.ofNat 4), (624, Int.ofNat 4)] },
  { level := 1, parent := 131, color := 27, mode := 1,
    vector := [(186, Int.ofNat 4), (242, Int.ofNat 1), (298, Int.ofNat 1), (508, Int.negSucc 1)]
    },
  { level := 1, parent := 132, color := 25, mode := 1,
    vector := [(9, Int.negSucc 1), (38, Int.ofNat 6), (67, Int.negSucc 3), (96, Int.negSucc 3),
    (179, Int.ofNat 4), (261, Int.negSucc 0), (263, Int.negSucc 0), (264, Int.ofNat 1), (289,
    Int.ofNat 1), (711, Int.negSucc 0), (821, Int.ofNat 1)] },
  { level := 1, parent := 132, color := 26, mode := 1,
    vector := [(11, Int.negSucc 1), (40, Int.ofNat 6), (69, Int.negSucc 3), (98, Int.negSucc 3),
    (237, Int.negSucc 0), (265, Int.negSucc 0), (565, Int.ofNat 4), (653, Int.negSucc 3)] },
  { level := 1, parent := 132, color := 27, mode := 1,
    vector := [(185, Int.negSucc 3), (241, Int.negSucc 0), (269, Int.negSucc 0), (566, Int.negSucc
    1)] },
  { level := 1, parent := 133, color := 27, mode := 1,
    vector := [(14, Int.ofNat 1), (43, Int.negSucc 3), (72, Int.ofNat 1), (101, Int.ofNat 5),
    (129, Int.negSucc 2), (157, Int.negSucc 0), (214, Int.ofNat 1), (407, Int.negSucc 0), (434,
    Int.ofNat 1), (537, Int.ofNat 1), (826, Int.ofNat 1)] },
  { level := 1, parent := 137, color := 27, mode := 1,
    vector := [(303, Int.ofNat 2)] },
  { level := 1, parent := 138, color := 27, mode := 1,
    vector := [(274, Int.negSucc 1)] },
  { level := 1, parent := 139, color := 27, mode := 1,
    vector := [(44, Int.negSucc 1), (102, Int.ofNat 4), (188, Int.negSucc 1), (245, Int.negSucc
    1)] },
  { level := 1, parent := 140, color := 27, mode := 1,
    vector := [(130, Int.ofNat 12)] },
  { level := 1, parent := 143, color := 23, mode := 1,
    vector := [(40, Int.ofNat 4), (69, Int.negSucc 3), (98, Int.negSucc 3), (237, Int.ofNat 2),
    (265, Int.ofNat 2), (319, Int.ofNat 2), (321, Int.negSucc 1), (322, Int.negSucc 1), (347,
    Int.ofNat 2), (823, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData24 : List WordNode := [
  { level := 2, parent := 387, color := 27, mode := 1,
    vector := [(475, Int.ofNat 1), (821, Int.negSucc 0)] },
  { level := 2, parent := 388, color := 27, mode := 1,
    vector := [(476, Int.ofNat 1), (822, Int.negSucc 0)] },
  { level := 2, parent := 389, color := 27, mode := 1,
    vector := [(478, Int.ofNat 1), (595, Int.negSucc 0), (825, Int.negSucc 1)] },
  { level := 2, parent := 390, color := 27, mode := 1,
    vector := [(479, Int.ofNat 2)] },
  { level := 2, parent := 391, color := 27, mode := 1,
    vector := [(537, Int.negSucc 1), (826, Int.negSucc 1)] },
  { level := 2, parent := 392, color := 24, mode := 1,
    vector := [(493, Int.ofNat 1), (495, Int.negSucc 0), (496, Int.ofNat 1), (521, Int.negSucc 0),
    (766, Int.ofNat 1), (829, Int.ofNat 1)] },
  { level := 2, parent := 392, color := 26, mode := 1,
    vector := [(498, Int.ofNat 1), (798, Int.negSucc 0), (814, Int.ofNat 2), (840, Int.negSucc 1)]
    },
  { level := 2, parent := 392, color := 27, mode := 1,
    vector := [(502, Int.ofNat 1), (769, Int.negSucc 0), (818, Int.negSucc 1)] },
  { level := 2, parent := 393, color := 27, mode := 1,
    vector := [(504, Int.ofNat 1), (820, Int.negSucc 0)] },
  { level := 2, parent := 394, color := 27, mode := 1,
    vector := [(506, Int.ofNat 1), (822, Int.negSucc 0)] },
  { level := 2, parent := 395, color := 27, mode := 1,
    vector := [(507, Int.ofNat 1), (624, Int.negSucc 0), (824, Int.negSucc 1)] },
  { level := 2, parent := 396, color := 27, mode := 1,
    vector := [(508, Int.ofNat 2)] },
  { level := 2, parent := 408, color := 23, mode := 1,
    vector := [(551, Int.negSucc 0), (553, Int.ofNat 1), (554, Int.ofNat 1), (579, Int.negSucc 0),
    (765, Int.negSucc 0), (831, Int.ofNat 1)] },
  { level := 2, parent := 408, color := 26, mode := 1,
    vector := [(558, Int.negSucc 0), (798, Int.ofNat 1), (812, Int.negSucc 1), (840, Int.ofNat 2)]
    },
  { level := 2, parent := 408, color := 27, mode := 1,
    vector := [(561, Int.ofNat 1), (769, Int.ofNat 1), (818, Int.ofNat 2)] },
  { level := 2, parent := 409, color := 27, mode := 1,
    vector := [(563, Int.ofNat 1), (820, Int.ofNat 1)] },
  { level := 2, parent := 410, color := 27, mode := 1,
    vector := [(564, Int.ofNat 1), (821, Int.ofNat 1)] },
  { level := 2, parent := 411, color := 27, mode := 1,
    vector := [(565, Int.ofNat 1), (653, Int.ofNat 1), (823, Int.ofNat 2)] },
  { level := 2, parent := 412, color := 27, mode := 1,
    vector := [(566, Int.ofNat 2)] },
  { level := 2, parent := 438, color := 25, mode := 1,
    vector := [(29, Int.ofNat 1), (31, Int.ofNat 1), (32, Int.negSucc 0), (57, Int.negSucc 0),
    (87, Int.negSucc 1), (89, Int.negSucc 1), (90, Int.ofNat 2), (115, Int.ofNat 2), (738,
    Int.ofNat 1), (768, Int.negSucc 0), (798, Int.negSucc 0), (813, Int.ofNat 1), (840,
    Int.negSucc 1)] },
  { level := 2, parent := 438, color := 26, mode := 1,
    vector := [(33, Int.ofNat 1), (91, Int.negSucc 1), (816, Int.ofNat 2)] },
  { level := 2, parent := 438, color := 27, mode := 1,
    vector := [(37, Int.ofNat 1), (95, Int.negSucc 1), (740, Int.negSucc 0), (820, Int.ofNat 2)]
    },
  { level := 2, parent := 439, color := 27, mode := 1,
    vector := [(40, Int.ofNat 1), (98, Int.negSucc 1), (823, Int.ofNat 1)] },
  { level := 2, parent := 440, color := 27, mode := 1,
    vector := [(41, Int.ofNat 1), (99, Int.negSucc 1), (824, Int.ofNat 1)] },
  { level := 2, parent := 441, color := 27, mode := 1,
    vector := [(43, Int.ofNat 1), (101, Int.negSucc 1), (537, Int.ofNat 1), (826, Int.ofNat 2)] },
  { level := 2, parent := 442, color := 27, mode := 1,
    vector := [(44, Int.ofNat 2), (102, Int.negSucc 3)] },
  { level := 2, parent := 443, color := 27, mode := 1,
    vector := [(15, Int.negSucc 1), (44, Int.ofNat 4), (73, Int.negSucc 1), (102, Int.negSucc 1),
    (827, Int.negSucc 1)] },
  { level := 2, parent := 444, color := 24, mode := 1,
    vector := [(29, Int.ofNat 1), (31, Int.negSucc 0), (32, Int.ofNat 1), (57, Int.negSucc 0),
    (58, Int.negSucc 1), (60, Int.ofNat 2), (61, Int.negSucc 1), (86, Int.ofNat 2), (708,
    Int.ofNat 1), (768, Int.negSucc 0), (798, Int.negSucc 0), (813, Int.ofNat 1), (840,
    Int.negSucc 1)] },
  { level := 2, parent := 444, color := 26, mode := 1,
    vector := [(34, Int.ofNat 1), (63, Int.negSucc 1), (817, Int.ofNat 2)] },
  { level := 2, parent := 444, color := 27, mode := 1,
    vector := [(38, Int.ofNat 1), (67, Int.negSucc 1), (711, Int.negSucc 0), (821, Int.ofNat 2)]
    },
  { level := 2, parent := 445, color := 27, mode := 1,
    vector := [(40, Int.ofNat 1), (69, Int.negSucc 1), (823, Int.ofNat 1)] },
  { level := 2, parent := 446, color := 27, mode := 1,
    vector := [(42, Int.ofNat 1), (71, Int.negSucc 1), (825, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

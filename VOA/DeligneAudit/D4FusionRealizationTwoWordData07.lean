/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData07 : List WordNode := [
  { level := 0, parent := 195, color := 16, mode := 0,
    vector := [(41, Int.negSucc 7), (99, Int.ofNat 16), (126, Int.negSucc 7), (294, Int.negSucc
    7), (349, Int.negSucc 7), (351, Int.ofNat 16)] },
  { level := 0, parent := 196, color := 18, mode := 0,
    vector := [(183, Int.negSucc 3), (267, Int.negSucc 3)] },
  { level := 0, parent := 196, color := 16, mode := 0,
    vector := [(40, Int.ofNat 8), (98, Int.negSucc 15), (125, Int.ofNat 8), (265, Int.ofNat 8),
    (320, Int.ofNat 8), (322, Int.negSucc 15)] },
  { level := 0, parent := 197, color := 16, mode := 0,
    vector := [(182, Int.negSucc 7), (238, Int.negSucc 7)] },
  { level := 0, parent := 198, color := 16, mode := 0,
    vector := [(124, Int.ofNat 24), (236, Int.ofNat 24)] },
  { level := 0, parent := 200, color := 18, mode := 0,
    vector := [(13, Int.ofNat 2), (42, Int.negSucc 3), (71, Int.ofNat 2), (100, Int.ofNat 2),
    (377, Int.ofNat 2), (378, Int.negSucc 3), (379, Int.ofNat 2), (380, Int.ofNat 2), (422,
    Int.ofNat 2), (455, Int.ofNat 2), (478, Int.ofNat 2), (595, Int.ofNat 2)] },
  { level := 0, parent := 200, color := 16, mode := 0,
    vector := [(424, Int.negSucc 3), (536, Int.negSucc 3)] },
  { level := 0, parent := 201, color := 19, mode := 0,
    vector := [(213, Int.negSucc 3), (297, Int.negSucc 3)] },
  { level := 0, parent := 201, color := 17, mode := 0,
    vector := [(13, Int.ofNat 2), (42, Int.negSucc 5), (71, Int.ofNat 2), (100, Int.ofNat 6),
    (155, Int.negSucc 1), (212, Int.ofNat 2), (268, Int.ofNat 2), (295, Int.negSucc 1), (377,
    Int.ofNat 2), (378, Int.negSucc 5), (379, Int.ofNat 2), (380, Int.ofNat 6), (422, Int.ofNat
    2), (478, Int.ofNat 2)] },
  { level := 0, parent := 201, color := 16, mode := 0,
    vector := [(12, Int.ofNat 2), (41, Int.negSucc 7), (70, Int.ofNat 2), (99, Int.ofNat 10),
    (126, Int.negSucc 5), (211, Int.ofNat 2), (239, Int.ofNat 2), (294, Int.negSucc 5), (348,
    Int.ofNat 2), (349, Int.negSucc 7), (350, Int.ofNat 2), (351, Int.ofNat 10)] },
  { level := 0, parent := 203, color := 17, mode := 0,
    vector := [(154, Int.ofNat 4), (266, Int.ofNat 4)] },
  { level := 0, parent := 203, color := 16, mode := 0,
    vector := [(11, Int.negSucc 1), (40, Int.ofNat 8), (69, Int.negSucc 1), (98, Int.negSucc 9),
    (125, Int.ofNat 6), (153, Int.ofNat 2), (237, Int.ofNat 2), (265, Int.ofNat 6), (319,
    Int.negSucc 1), (320, Int.ofNat 8), (321, Int.negSucc 1), (322, Int.negSucc 9)] },
  { level := 0, parent := 206, color := 17, mode := 0,
    vector := [(13, Int.ofNat 2), (42, Int.negSucc 5), (71, Int.ofNat 6), (100, Int.ofNat 2),
    (155, Int.negSucc 1), (295, Int.negSucc 1), (377, Int.ofNat 2), (378, Int.negSucc 5), (379,
    Int.ofNat 6), (380, Int.ofNat 2), (422, Int.ofNat 2), (455, Int.ofNat 2), (478, Int.ofNat 2),
    (595, Int.ofNat 2)] },
  { level := 0, parent := 206, color := 16, mode := 0,
    vector := [(12, Int.ofNat 2), (41, Int.negSucc 5), (70, Int.ofNat 2), (99, Int.ofNat 6), (126,
    Int.negSucc 1), (294, Int.negSucc 1), (348, Int.ofNat 2), (349, Int.negSucc 5), (350,
    Int.ofNat 2), (351, Int.ofNat 6), (423, Int.ofNat 2), (456, Int.ofNat 2), (507, Int.ofNat 2),
    (624, Int.ofNat 2)] },
  { level := 0, parent := 208, color := 16, mode := 0,
    vector := [(41, Int.negSucc 1), (70, Int.ofNat 4), (349, Int.negSucc 1), (350, Int.ofNat 4),
    (423, Int.ofNat 2), (507, Int.ofNat 2)] },
  { level := 0, parent := 210, color := 16, mode := 0,
    vector := [(11, Int.negSucc 1), (40, Int.ofNat 12), (69, Int.negSucc 9), (98, Int.negSucc 9),
    (125, Int.ofNat 6), (153, Int.ofNat 6), (237, Int.ofNat 6), (265, Int.ofNat 6), (319,
    Int.negSucc 1), (320, Int.ofNat 12), (321, Int.negSucc 9), (322, Int.negSucc 9)] },
  { level := 0, parent := 215, color := 19, mode := 0,
    vector := [(13, Int.ofNat 3), (42, Int.negSucc 2), (71, Int.ofNat 1), (100, Int.ofNat 1),
    (212, Int.ofNat 1), (268, Int.ofNat 1), (377, Int.ofNat 3), (378, Int.negSucc 2), (379,
    Int.ofNat 1), (380, Int.ofNat 1), (422, Int.ofNat 1), (455, Int.ofNat 1), (478, Int.ofNat 1),
    (595, Int.ofNat 1)] },
  { level := 0, parent := 215, color := 16, mode := 0,
    vector := [(11, Int.negSucc 0), (40, Int.ofNat 3), (69, Int.negSucc 0), (98, Int.negSucc 2),
    (125, Int.ofNat 1), (265, Int.ofNat 1), (319, Int.negSucc 0), (320, Int.ofNat 3), (321,
    Int.negSucc 0), (322, Int.negSucc 2), (425, Int.ofNat 1), (457, Int.negSucc 0), (565,
    Int.ofNat 1), (653, Int.negSucc 0)] },
  { level := 0, parent := 217, color := 16, mode := 0,
    vector := [(12, Int.ofNat 5), (41, Int.negSucc 5), (70, Int.ofNat 1), (99, Int.ofNat 5), (126,
    Int.negSucc 2), (211, Int.ofNat 3), (239, Int.ofNat 3), (294, Int.negSucc 2), (348, Int.ofNat
    5), (349, Int.negSucc 5), (350, Int.ofNat 1), (351, Int.ofNat 5)] },
  { level := 0, parent := 218, color := 16, mode := 0,
    vector := [(11, Int.negSucc 2), (40, Int.ofNat 5), (69, Int.negSucc 0), (98, Int.negSucc 4),
    (125, Int.ofNat 3), (153, Int.ofNat 1), (237, Int.ofNat 1), (265, Int.ofNat 3), (319,
    Int.negSucc 2), (320, Int.ofNat 5), (321, Int.negSucc 0), (322, Int.negSucc 4), (425,
    Int.ofNat 1), (565, Int.ofNat 1)] },
  { level := 0, parent := 222, color := 18, mode := 0,
    vector := [(187, Int.negSucc 3), (383, Int.negSucc 3), (451, Int.ofNat 4), (479, Int.ofNat 4)]
    },
  { level := 0, parent := 222, color := 16, mode := 0,
    vector := [(43, Int.ofNat 8), (101, Int.negSucc 15), (129, Int.ofNat 8), (381, Int.ofNat 8),
    (407, Int.ofNat 8), (409, Int.negSucc 15)] },
  { level := 0, parent := 223, color := 19, mode := 0,
    vector := [(300, Int.ofNat 8)] },
  { level := 0, parent := 223, color := 17, mode := 0,
    vector := [(187, Int.negSucc 3), (271, Int.negSucc 3), (299, Int.negSucc 3), (383, Int.negSucc
    3)] },
  { level := 0, parent := 223, color := 16, mode := 0,
    vector := [(186, Int.negSucc 3), (242, Int.negSucc 3), (298, Int.negSucc 3), (354, Int.negSucc
    3)] },
  { level := 0, parent := 224, color := 16, mode := 0,
    vector := [(128, Int.ofNat 24), (352, Int.ofNat 24)] },
  { level := 0, parent := 225, color := 17, mode := 0,
    vector := [(270, Int.ofNat 8)] },
  { level := 0, parent := 225, color := 16, mode := 0,
    vector := [(185, Int.ofNat 4), (241, Int.ofNat 4), (269, Int.ofNat 4), (325, Int.ofNat 4)] },
  { level := 0, parent := 226, color := 16, mode := 0,
    vector := [(127, Int.negSucc 23), (323, Int.negSucc 23)] },
  { level := 0, parent := 227, color := 16, mode := 0,
    vector := [(240, Int.ofNat 16)] },
  { level := 0, parent := 229, color := 19, mode := 0,
    vector := [(216, Int.ofNat 2), (384, Int.ofNat 2)] },
  { level := 0, parent := 229, color := 17, mode := 0,
    vector := [(158, Int.ofNat 2), (382, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

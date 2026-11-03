/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData12 : List WordNode := [
  { level := 1, parent := 14, color := 26, mode := 1,
    vector := [(609, Int.ofNat 1), (610, Int.negSucc 0), (611, Int.ofNat 1), (612, Int.ofNat 1),
    (637, Int.negSucc 0), (671, Int.ofNat 1), (732, Int.negSucc 0), (833, Int.negSucc 0)] },
  { level := 1, parent := 14, color := 27, mode := 1,
    vector := [(615, Int.negSucc 0), (675, Int.ofNat 1), (735, Int.ofNat 1), (766, Int.negSucc 0)]
    },
  { level := 1, parent := 15, color := 20, mode := 1,
    vector := [(489, Int.negSucc 0), (754, Int.negSucc 0), (755, Int.ofNat 1), (756, Int.negSucc
    0), (757, Int.ofNat 1), (782, Int.negSucc 0), (789, Int.negSucc 0), (838, Int.negSucc 0)] },
  { level := 1, parent := 15, color := 23, mode := 1,
    vector := [(486, Int.ofNat 1), (599, Int.negSucc 0), (759, Int.ofNat 1), (792, Int.negSucc 0)]
    },
  { level := 1, parent := 15, color := 24, mode := 1,
    vector := [(485, Int.ofNat 1), (597, Int.ofNat 1), (761, Int.negSucc 0), (793, Int.negSucc 0)]
    },
  { level := 1, parent := 15, color := 26, mode := 1,
    vector := [(482, Int.ofNat 1), (580, Int.ofNat 1), (581, Int.negSucc 0), (582, Int.ofNat 1),
    (583, Int.ofNat 1), (608, Int.negSucc 0), (796, Int.negSucc 0), (832, Int.negSucc 0)] },
  { level := 1, parent := 15, color := 27, mode := 1,
    vector := [(465, Int.negSucc 0), (492, Int.ofNat 1), (586, Int.negSucc 0), (767, Int.negSucc
    0), (828, Int.ofNat 1)] },
  { level := 1, parent := 16, color := 27, mode := 1,
    vector := [(523, Int.ofNat 1), (550, Int.negSucc 0), (797, Int.negSucc 0), (830, Int.negSucc
    0)] },
  { level := 1, parent := 17, color := 21, mode := 1,
    vector := [(517, Int.negSucc 0), (754, Int.negSucc 0), (755, Int.ofNat 1), (756, Int.ofNat 1),
    (757, Int.negSucc 0), (782, Int.negSucc 0), (789, Int.negSucc 0), (838, Int.negSucc 0)] },
  { level := 1, parent := 17, color := 23, mode := 1,
    vector := [(515, Int.ofNat 1), (628, Int.negSucc 0), (758, Int.ofNat 1), (791, Int.negSucc 0)]
    },
  { level := 1, parent := 17, color := 25, mode := 1,
    vector := [(513, Int.ofNat 1), (625, Int.ofNat 1), (761, Int.negSucc 0), (793, Int.negSucc 0)]
    },
  { level := 1, parent := 17, color := 26, mode := 1,
    vector := [(511, Int.ofNat 1), (609, Int.ofNat 1), (610, Int.negSucc 0), (611, Int.ofNat 1),
    (612, Int.ofNat 1), (637, Int.negSucc 0), (795, Int.negSucc 0), (833, Int.negSucc 0)] },
  { level := 1, parent := 17, color := 27, mode := 1,
    vector := [(494, Int.negSucc 0), (521, Int.ofNat 1), (615, Int.negSucc 0), (766, Int.negSucc
    0), (829, Int.ofNat 1)] },
  { level := 1, parent := 18, color := 24, mode := 1,
    vector := [(696, Int.negSucc 3), (698, Int.ofNat 4), (699, Int.negSucc 3), (724, Int.ofNat 4),
    (836, Int.ofNat 4)] },
  { level := 1, parent := 18, color := 26, mode := 1,
    vector := [(701, Int.negSucc 3)] },
  { level := 1, parent := 18, color := 27, mode := 1,
    vector := [(705, Int.negSucc 3)] },
  { level := 1, parent := 19, color := 23, mode := 1,
    vector := [(657, Int.ofNat 2)] },
  { level := 1, parent := 19, color := 24, mode := 1,
    vector := [(655, Int.negSucc 1), (725, Int.negSucc 1), (727, Int.ofNat 2), (728, Int.negSucc
    1), (753, Int.ofNat 2), (758, Int.negSucc 1), (837, Int.ofNat 2)] },
  { level := 1, parent := 19, color := 25, mode := 1,
    vector := [(654, Int.negSucc 1), (696, Int.negSucc 1), (698, Int.negSucc 1), (699, Int.ofNat
    2), (724, Int.ofNat 2), (759, Int.negSucc 1), (836, Int.ofNat 2)] },
  { level := 1, parent := 19, color := 26, mode := 1,
    vector := [(638, Int.negSucc 1), (639, Int.ofNat 2), (640, Int.negSucc 1), (641, Int.negSucc
    1), (666, Int.ofNat 2), (700, Int.negSucc 1), (730, Int.negSucc 1), (834, Int.ofNat 2)] },
  { level := 1, parent := 19, color := 27, mode := 1,
    vector := [(644, Int.ofNat 2), (704, Int.negSucc 1), (734, Int.negSucc 1), (765, Int.ofNat 2)]
    },
  { level := 1, parent := 20, color := 25, mode := 1,
    vector := [(725, Int.negSucc 3), (727, Int.negSucc 3), (728, Int.ofNat 4), (753, Int.ofNat 4),
    (837, Int.ofNat 4)] },
  { level := 1, parent := 20, color := 26, mode := 1,
    vector := [(729, Int.negSucc 3)] },
  { level := 1, parent := 20, color := 27, mode := 1,
    vector := [(733, Int.negSucc 3)] },
  { level := 1, parent := 21, color := 22, mode := 1,
    vector := [(574, Int.negSucc 0), (754, Int.negSucc 0), (755, Int.negSucc 0), (756, Int.ofNat
    1), (757, Int.ofNat 1), (782, Int.ofNat 1), (789, Int.ofNat 1), (838, Int.ofNat 1)] },
  { level := 1, parent := 21, color := 24, mode := 1,
    vector := [(572, Int.ofNat 1), (655, Int.negSucc 0), (758, Int.negSucc 0), (791, Int.ofNat 1)]
    },
  { level := 1, parent := 21, color := 25, mode := 1,
    vector := [(571, Int.ofNat 1), (654, Int.negSucc 0), (759, Int.negSucc 0), (792, Int.ofNat 1)]
    },
  { level := 1, parent := 21, color := 26, mode := 1,
    vector := [(569, Int.ofNat 1), (638, Int.negSucc 0), (639, Int.ofNat 1), (640, Int.negSucc 0),
    (641, Int.negSucc 0), (666, Int.ofNat 1), (794, Int.ofNat 1), (834, Int.ofNat 1)] },
  { level := 1, parent := 21, color := 27, mode := 1,
    vector := [(552, Int.negSucc 0), (579, Int.ofNat 1), (644, Int.ofNat 1), (765, Int.ofNat 1),
    (831, Int.ofNat 1)] },
  { level := 1, parent := 22, color := 23, mode := 1,
    vector := [(580, Int.ofNat 2), (582, Int.negSucc 1), (583, Int.negSucc 1), (608, Int.ofNat 2),
    (672, Int.negSucc 1), (832, Int.ofNat 2)] },
  { level := 1, parent := 22, color := 26, mode := 1,
    vector := [(587, Int.ofNat 2)] },
  { level := 1, parent := 22, color := 27, mode := 1,
    vector := [(590, Int.negSucc 1), (680, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

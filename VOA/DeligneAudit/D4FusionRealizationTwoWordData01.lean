/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData01 : List WordNode := [
  { level := 0, parent := 18, color := 16, mode := 0,
    vector := [(662, Int.ofNat 4), (718, Int.ofNat 4)] },
  { level := 0, parent := 19, color := 18, mode := 0,
    vector := [(577, Int.negSucc 1), (773, Int.negSucc 1)] },
  { level := 0, parent := 19, color := 16, mode := 0,
    vector := [(663, Int.ofNat 4), (747, Int.ofNat 4)] },
  { level := 0, parent := 21, color := 19, mode := 0,
    vector := [(27, Int.negSucc 1), (56, Int.ofNat 1), (548, Int.ofNat 1), (661, Int.negSucc 0),
    (689, Int.negSucc 0), (772, Int.ofNat 1), (783, Int.negSucc 1), (784, Int.ofNat 1)] },
  { level := 0, parent := 22, color := 18, mode := 0,
    vector := [(487, Int.ofNat 2), (683, Int.ofNat 2)] },
  { level := 0, parent := 22, color := 17, mode := 0,
    vector := [(600, Int.ofNat 4)] },
  { level := 0, parent := 22, color := 16, mode := 0,
    vector := [(545, Int.negSucc 1), (601, Int.ofNat 2), (629, Int.ofNat 2), (685, Int.negSucc 1)]
    },
  { level := 0, parent := 23, color := 18, mode := 0,
    vector := [(516, Int.ofNat 2), (684, Int.ofNat 2)] },
  { level := 0, parent := 23, color := 16, mode := 0,
    vector := [(630, Int.ofNat 4)] },
  { level := 0, parent := 24, color := 17, mode := 0,
    vector := [(488, Int.negSucc 0), (712, Int.negSucc 0)] },
  { level := 0, parent := 24, color := 16, mode := 0,
    vector := [(55, Int.negSucc 0), (113, Int.ofNat 2), (489, Int.negSucc 0), (741, Int.negSucc
    0), (755, Int.negSucc 0), (757, Int.ofNat 2)] },
  { level := 0, parent := 25, color := 16, mode := 0,
    vector := [(546, Int.ofNat 2), (602, Int.negSucc 1), (658, Int.negSucc 1), (714, Int.ofNat 2)]
    },
  { level := 0, parent := 26, color := 18, mode := 0,
    vector := [(26, Int.ofNat 1), (55, Int.negSucc 1), (84, Int.ofNat 1), (113, Int.ofNat 1),
    (489, Int.negSucc 0), (517, Int.negSucc 0), (574, Int.ofNat 1), (686, Int.ofNat 1), (713,
    Int.negSucc 0), (741, Int.negSucc 0), (754, Int.ofNat 1), (755, Int.negSucc 1), (756,
    Int.ofNat 1), (757, Int.ofNat 1)] },
  { level := 0, parent := 26, color := 16, mode := 0,
    vector := [(547, Int.ofNat 2), (631, Int.negSucc 1), (659, Int.negSucc 1), (743, Int.ofNat 2)]
    },
  { level := 0, parent := 27, color := 17, mode := 0,
    vector := [(55, Int.negSucc 0), (84, Int.ofNat 2), (517, Int.negSucc 0), (713, Int.negSucc 0),
    (755, Int.negSucc 0), (756, Int.ofNat 2)] },
  { level := 0, parent := 27, color := 16, mode := 0,
    vector := [(518, Int.negSucc 0), (742, Int.negSucc 0)] },
  { level := 0, parent := 29, color := 18, mode := 0,
    vector := [(26, Int.ofNat 1), (55, Int.negSucc 2), (84, Int.ofNat 1), (113, Int.ofNat 3),
    (201, Int.ofNat 1), (489, Int.negSucc 0), (741, Int.negSucc 0), (754, Int.ofNat 1), (755,
    Int.negSucc 2), (756, Int.ofNat 1), (757, Int.ofNat 3), (789, Int.ofNat 1)] },
  { level := 0, parent := 29, color := 16, mode := 0,
    vector := [(143, Int.negSucc 1), (547, Int.ofNat 2), (743, Int.ofNat 2), (787, Int.negSucc 1)]
    },
  { level := 0, parent := 30, color := 19, mode := 0,
    vector := [(230, Int.negSucc 0), (545, Int.negSucc 0), (685, Int.negSucc 0), (790, Int.negSucc
    0)] },
  { level := 0, parent := 30, color := 17, mode := 0,
    vector := [(172, Int.negSucc 0), (546, Int.ofNat 1), (714, Int.ofNat 1), (788, Int.negSucc 0)]
    },
  { level := 0, parent := 32, color := 18, mode := 0,
    vector := [(575, Int.negSucc 3), (715, Int.negSucc 3)] },
  { level := 0, parent := 32, color := 16, mode := 0,
    vector := [(660, Int.ofNat 8)] },
  { level := 0, parent := 33, color := 19, mode := 0,
    vector := [(26, Int.ofNat 4), (55, Int.negSucc 1), (574, Int.ofNat 2), (686, Int.ofNat 2),
    (754, Int.ofNat 4), (755, Int.negSucc 1)] },
  { level := 0, parent := 33, color := 16, mode := 0,
    vector := [(576, Int.negSucc 1), (744, Int.negSucc 1)] },
  { level := 0, parent := 36, color := 17, mode := 0,
    vector := [(484, Int.ofNat 2), (596, Int.ofNat 2)] },
  { level := 0, parent := 36, color := 16, mode := 0,
    vector := [(52, Int.ofNat 2), (110, Int.negSucc 3), (485, Int.ofNat 2), (625, Int.ofNat 2),
    (668, Int.ofNat 2), (670, Int.negSucc 3)] },
  { level := 0, parent := 37, color := 16, mode := 0,
    vector := [(542, Int.negSucc 3), (598, Int.negSucc 3)] },
  { level := 0, parent := 38, color := 18, mode := 0,
    vector := [(23, Int.negSucc 1), (52, Int.ofNat 4), (81, Int.negSucc 1), (110, Int.negSucc 1),
    (485, Int.ofNat 2), (513, Int.ofNat 2), (597, Int.ofNat 2), (625, Int.ofNat 2), (667,
    Int.negSucc 1), (668, Int.ofNat 4), (669, Int.negSucc 1), (670, Int.negSucc 1)] },
  { level := 0, parent := 38, color := 16, mode := 0,
    vector := [(543, Int.negSucc 3), (627, Int.negSucc 3)] },
  { level := 0, parent := 39, color := 17, mode := 0,
    vector := [(52, Int.ofNat 2), (81, Int.negSucc 3), (513, Int.ofNat 2), (597, Int.ofNat 2),
    (668, Int.ofNat 2), (669, Int.negSucc 3)] },
  { level := 0, parent := 39, color := 16, mode := 0,
    vector := [(514, Int.ofNat 2), (626, Int.ofNat 2)] },
  { level := 0, parent := 41, color := 16, mode := 0,
    vector := [(53, Int.negSucc 0), (111, Int.ofNat 2), (486, Int.negSucc 0), (654, Int.negSucc
    0), (697, Int.negSucc 0), (699, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

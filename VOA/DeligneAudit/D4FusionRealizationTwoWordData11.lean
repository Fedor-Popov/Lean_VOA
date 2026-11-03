/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData11 : List WordNode := [
  { level := 1, parent := 7, color := 27, mode := 1,
    vector := [(581, Int.negSucc 0), (608, Int.ofNat 1), (796, Int.ofNat 1), (832, Int.ofNat 1)]
    },
  { level := 1, parent := 8, color := 21, mode := 1,
    vector := [(633, Int.negSucc 0), (783, Int.ofNat 1), (784, Int.negSucc 0), (785, Int.negSucc
    0), (786, Int.ofNat 1), (811, Int.ofNat 1), (839, Int.ofNat 1)] },
  { level := 1, parent := 8, color := 23, mode := 1,
    vector := [(631, Int.ofNat 1), (787, Int.negSucc 0)] },
  { level := 1, parent := 8, color := 25, mode := 1,
    vector := [(629, Int.ofNat 1), (790, Int.ofNat 1)] },
  { level := 1, parent := 8, color := 26, mode := 1,
    vector := [(627, Int.ofNat 1)] },
  { level := 1, parent := 8, color := 27, mode := 1,
    vector := [(610, Int.negSucc 0), (637, Int.ofNat 1), (795, Int.ofNat 1), (833, Int.ofNat 1)]
    },
  { level := 1, parent := 9, color := 23, mode := 1,
    vector := [(715, Int.ofNat 2)] },
  { level := 1, parent := 9, color := 24, mode := 1,
    vector := [(713, Int.negSucc 1), (754, Int.negSucc 1), (756, Int.ofNat 2), (757, Int.negSucc
    1), (782, Int.ofNat 2), (838, Int.ofNat 2)] },
  { level := 1, parent := 9, color := 25, mode := 1,
    vector := [(712, Int.negSucc 1)] },
  { level := 1, parent := 9, color := 26, mode := 1,
    vector := [(696, Int.negSucc 1), (697, Int.ofNat 2), (698, Int.negSucc 1), (699, Int.negSucc
    1), (724, Int.ofNat 2), (759, Int.negSucc 1), (836, Int.ofNat 2)] },
  { level := 1, parent := 9, color := 27, mode := 1,
    vector := [(702, Int.ofNat 2), (763, Int.negSucc 1)] },
  { level := 1, parent := 10, color := 23, mode := 1,
    vector := [(744, Int.ofNat 2)] },
  { level := 1, parent := 10, color := 24, mode := 1,
    vector := [(742, Int.negSucc 1)] },
  { level := 1, parent := 10, color := 25, mode := 1,
    vector := [(741, Int.negSucc 1), (754, Int.negSucc 1), (756, Int.negSucc 1), (757, Int.ofNat
    2), (782, Int.ofNat 2), (838, Int.ofNat 2)] },
  { level := 1, parent := 10, color := 26, mode := 1,
    vector := [(725, Int.negSucc 1), (726, Int.ofNat 2), (727, Int.negSucc 1), (728, Int.negSucc
    1), (753, Int.ofNat 2), (758, Int.negSucc 1), (837, Int.ofNat 2)] },
  { level := 1, parent := 10, color := 27, mode := 1,
    vector := [(731, Int.ofNat 2), (762, Int.negSucc 1)] },
  { level := 1, parent := 11, color := 22, mode := 1,
    vector := [(661, Int.ofNat 1), (783, Int.ofNat 1), (784, Int.ofNat 1), (785, Int.negSucc 0),
    (786, Int.negSucc 0), (811, Int.negSucc 0), (839, Int.negSucc 0)] },
  { level := 1, parent := 11, color := 24, mode := 1,
    vector := [(659, Int.negSucc 0), (787, Int.ofNat 1)] },
  { level := 1, parent := 11, color := 25, mode := 1,
    vector := [(658, Int.negSucc 0), (788, Int.ofNat 1)] },
  { level := 1, parent := 11, color := 26, mode := 1,
    vector := [(656, Int.negSucc 0)] },
  { level := 1, parent := 11, color := 27, mode := 1,
    vector := [(639, Int.ofNat 1), (666, Int.negSucc 0), (794, Int.negSucc 0), (834, Int.negSucc
    0)] },
  { level := 1, parent := 12, color := 23, mode := 1,
    vector := [(667, Int.ofNat 2), (669, Int.negSucc 1), (670, Int.negSucc 1), (695, Int.ofNat 2),
    (835, Int.ofNat 2)] },
  { level := 1, parent := 12, color := 26, mode := 1,
    vector := [(674, Int.ofNat 2)] },
  { level := 1, parent := 12, color := 27, mode := 1,
    vector := [(677, Int.negSucc 1)] },
  { level := 1, parent := 13, color := 23, mode := 1,
    vector := [(599, Int.negSucc 0), (696, Int.negSucc 0), (698, Int.ofNat 1), (699, Int.ofNat 1),
    (724, Int.negSucc 0), (759, Int.ofNat 1), (836, Int.negSucc 0)] },
  { level := 1, parent := 13, color := 24, mode := 1,
    vector := [(597, Int.ofNat 1), (667, Int.ofNat 1), (669, Int.negSucc 0), (670, Int.ofNat 1),
    (695, Int.negSucc 0), (761, Int.negSucc 0), (835, Int.negSucc 0)] },
  { level := 1, parent := 13, color := 25, mode := 1,
    vector := [(596, Int.ofNat 1)] },
  { level := 1, parent := 13, color := 26, mode := 1,
    vector := [(580, Int.ofNat 1), (581, Int.negSucc 0), (582, Int.ofNat 1), (583, Int.ofNat 1),
    (608, Int.negSucc 0), (672, Int.ofNat 1), (703, Int.negSucc 0), (832, Int.negSucc 0)] },
  { level := 1, parent := 13, color := 27, mode := 1,
    vector := [(586, Int.negSucc 0), (676, Int.ofNat 1), (706, Int.ofNat 1), (767, Int.negSucc 0)]
    },
  { level := 1, parent := 14, color := 23, mode := 1,
    vector := [(628, Int.negSucc 0), (725, Int.negSucc 0), (727, Int.ofNat 1), (728, Int.ofNat 1),
    (753, Int.negSucc 0), (758, Int.ofNat 1), (837, Int.negSucc 0)] },
  { level := 1, parent := 14, color := 24, mode := 1,
    vector := [(626, Int.ofNat 1)] },
  { level := 1, parent := 14, color := 25, mode := 1,
    vector := [(625, Int.ofNat 1), (667, Int.ofNat 1), (669, Int.ofNat 1), (670, Int.negSucc 0),
    (695, Int.negSucc 0), (761, Int.negSucc 0), (835, Int.negSucc 0)] }
]

end VOA.DeligneAudit.D4Two.Certificate

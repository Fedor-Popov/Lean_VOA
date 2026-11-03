/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData00 : List WordNode := [
  { level := 0, parent := 0, color := 0, mode := 0,
    vector := [(810, Int.ofNat 1)] },
  { level := 0, parent := 0, color := 18, mode := 0,
    vector := [(781, Int.negSucc 0), (809, Int.negSucc 0)] },
  { level := 0, parent := 1, color := 19, mode := 0,
    vector := [(694, Int.ofNat 1), (806, Int.ofNat 1)] },
  { level := 0, parent := 1, color := 18, mode := 0,
    vector := [(780, Int.ofNat 2)] },
  { level := 0, parent := 1, color := 17, mode := 0,
    vector := [(723, Int.negSucc 0), (807, Int.negSucc 0)] },
  { level := 0, parent := 1, color := 16, mode := 0,
    vector := [(752, Int.negSucc 0), (808, Int.negSucc 0)] },
  { level := 0, parent := 2, color := 18, mode := 0,
    vector := [(693, Int.negSucc 0), (777, Int.negSucc 0)] },
  { level := 0, parent := 2, color := 17, mode := 0,
    vector := [(607, Int.ofNat 1), (803, Int.ofNat 1)] },
  { level := 0, parent := 2, color := 16, mode := 0,
    vector := [(636, Int.ofNat 1), (804, Int.ofNat 1)] },
  { level := 0, parent := 3, color := 17, mode := 0,
    vector := [(722, Int.ofNat 2), (778, Int.ofNat 2)] },
  { level := 0, parent := 3, color := 16, mode := 0,
    vector := [(751, Int.ofNat 2), (779, Int.ofNat 2)] },
  { level := 0, parent := 4, color := 16, mode := 0,
    vector := [(665, Int.negSucc 0), (805, Int.negSucc 0)] },
  { level := 0, parent := 6, color := 19, mode := 0,
    vector := [(690, Int.ofNat 2)] },
  { level := 0, parent := 6, color := 17, mode := 0,
    vector := [(606, Int.negSucc 0), (691, Int.negSucc 0), (719, Int.negSucc 0), (774, Int.negSucc
    0)] },
  { level := 0, parent := 6, color := 16, mode := 0,
    vector := [(635, Int.negSucc 0), (692, Int.negSucc 0), (748, Int.negSucc 0), (775, Int.negSucc
    0)] },
  { level := 0, parent := 7, color := 18, mode := 0,
    vector := [(491, Int.ofNat 1), (606, Int.negSucc 0), (774, Int.negSucc 0), (799, Int.ofNat 1)]
    },
  { level := 0, parent := 7, color := 16, mode := 0,
    vector := [(549, Int.negSucc 0), (801, Int.negSucc 0)] },
  { level := 0, parent := 8, color := 18, mode := 0,
    vector := [(520, Int.ofNat 1), (635, Int.negSucc 0), (775, Int.negSucc 0), (800, Int.ofNat 1)]
    },
  { level := 0, parent := 9, color := 17, mode := 0,
    vector := [(720, Int.ofNat 4)] },
  { level := 0, parent := 9, color := 16, mode := 0,
    vector := [(664, Int.ofNat 2), (721, Int.ofNat 2), (749, Int.ofNat 2), (776, Int.ofNat 2)] },
  { level := 0, parent := 10, color := 16, mode := 0,
    vector := [(750, Int.ofNat 4)] },
  { level := 0, parent := 11, color := 18, mode := 0,
    vector := [(578, Int.ofNat 1), (664, Int.ofNat 1), (776, Int.ofNat 1), (802, Int.ofNat 1)] },
  { level := 0, parent := 12, color := 17, mode := 0,
    vector := [(603, Int.ofNat 2), (687, Int.ofNat 2)] },
  { level := 0, parent := 12, color := 16, mode := 0,
    vector := [(632, Int.ofNat 2), (688, Int.ofNat 2)] },
  { level := 0, parent := 13, color := 18, mode := 0,
    vector := [(490, Int.negSucc 0), (770, Int.negSucc 0)] },
  { level := 0, parent := 13, color := 17, mode := 0,
    vector := [(604, Int.negSucc 1), (716, Int.negSucc 1)] },
  { level := 0, parent := 13, color := 16, mode := 0,
    vector := [(548, Int.ofNat 1), (605, Int.negSucc 0), (633, Int.negSucc 0), (661, Int.negSucc
    0), (689, Int.negSucc 0), (717, Int.negSucc 0), (745, Int.negSucc 0), (772, Int.ofNat 1)] },
  { level := 0, parent := 14, color := 18, mode := 0,
    vector := [(519, Int.negSucc 0), (771, Int.negSucc 0)] },
  { level := 0, parent := 14, color := 16, mode := 0,
    vector := [(634, Int.negSucc 1), (746, Int.negSucc 1)] },
  { level := 0, parent := 15, color := 16, mode := 0,
    vector := [(56, Int.ofNat 1), (114, Int.negSucc 1), (548, Int.ofNat 1), (605, Int.negSucc 0),
    (745, Int.negSucc 0), (772, Int.ofNat 1), (784, Int.ofNat 1), (786, Int.negSucc 1)] },
  { level := 0, parent := 16, color := 18, mode := 0,
    vector := [(27, Int.negSucc 0), (56, Int.ofNat 2), (85, Int.negSucc 0), (114, Int.negSucc 0),
    (548, Int.ofNat 1), (772, Int.ofNat 1), (783, Int.negSucc 0), (784, Int.ofNat 2), (785,
    Int.negSucc 0), (786, Int.negSucc 0)] },
  { level := 0, parent := 17, color := 17, mode := 0,
    vector := [(56, Int.ofNat 1), (85, Int.negSucc 1), (548, Int.ofNat 1), (633, Int.negSucc 0),
    (717, Int.negSucc 0), (772, Int.ofNat 1), (784, Int.ofNat 1), (785, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData10 : List WordNode := [
  { level := 1, parent := 2, color := 24, mode := 1,
    vector := [(688, Int.ofNat 1)] },
  { level := 1, parent := 2, color := 25, mode := 1,
    vector := [(687, Int.ofNat 1)] },
  { level := 1, parent := 2, color := 26, mode := 1,
    vector := [(685, Int.ofNat 1), (790, Int.ofNat 1)] },
  { level := 1, parent := 2, color := 27, mode := 1,
    vector := [(668, Int.negSucc 0), (695, Int.ofNat 1), (793, Int.negSucc 0), (835, Int.ofNat 1)]
    },
  { level := 1, parent := 3, color := 23, mode := 1,
    vector := [(773, Int.ofNat 2)] },
  { level := 1, parent := 3, color := 24, mode := 1,
    vector := [(771, Int.negSucc 1)] },
  { level := 1, parent := 3, color := 25, mode := 1,
    vector := [(770, Int.negSucc 1)] },
  { level := 1, parent := 3, color := 26, mode := 1,
    vector := [(754, Int.negSucc 1), (755, Int.ofNat 2), (756, Int.negSucc 1), (757, Int.negSucc
    1), (782, Int.ofNat 2), (838, Int.ofNat 2)] },
  { level := 1, parent := 3, color := 27, mode := 1,
    vector := [(760, Int.ofNat 2)] },
  { level := 1, parent := 4, color := 20, mode := 1,
    vector := [(721, Int.ofNat 1), (802, Int.negSucc 0)] },
  { level := 1, parent := 4, color := 22, mode := 1,
    vector := [(719, Int.ofNat 1), (799, Int.ofNat 1)] },
  { level := 1, parent := 4, color := 23, mode := 1,
    vector := [(718, Int.negSucc 0)] },
  { level := 1, parent := 4, color := 24, mode := 1,
    vector := [(717, Int.negSucc 0), (783, Int.ofNat 1), (785, Int.negSucc 0), (786, Int.ofNat 1),
    (811, Int.negSucc 0), (839, Int.negSucc 0)] },
  { level := 1, parent := 4, color := 25, mode := 1,
    vector := [(716, Int.negSucc 0)] },
  { level := 1, parent := 4, color := 26, mode := 1,
    vector := [(714, Int.negSucc 0), (788, Int.ofNat 1)] },
  { level := 1, parent := 4, color := 27, mode := 1,
    vector := [(697, Int.ofNat 1), (724, Int.negSucc 0), (792, Int.ofNat 1), (836, Int.negSucc 0)]
    },
  { level := 1, parent := 5, color := 21, mode := 1,
    vector := [(749, Int.ofNat 1), (802, Int.negSucc 0)] },
  { level := 1, parent := 5, color := 22, mode := 1,
    vector := [(748, Int.ofNat 1), (800, Int.ofNat 1)] },
  { level := 1, parent := 5, color := 23, mode := 1,
    vector := [(747, Int.negSucc 0)] },
  { level := 1, parent := 5, color := 24, mode := 1,
    vector := [(746, Int.negSucc 0)] },
  { level := 1, parent := 5, color := 25, mode := 1,
    vector := [(745, Int.negSucc 0), (783, Int.ofNat 1), (785, Int.ofNat 1), (786, Int.negSucc 0),
    (811, Int.negSucc 0), (839, Int.negSucc 0)] },
  { level := 1, parent := 5, color := 26, mode := 1,
    vector := [(743, Int.negSucc 0), (787, Int.ofNat 1)] },
  { level := 1, parent := 5, color := 27, mode := 1,
    vector := [(726, Int.ofNat 1), (753, Int.negSucc 0), (791, Int.ofNat 1), (837, Int.negSucc 0)]
    },
  { level := 1, parent := 6, color := 23, mode := 1,
    vector := [(686, Int.negSucc 0), (754, Int.negSucc 0), (756, Int.ofNat 1), (757, Int.ofNat 1),
    (782, Int.negSucc 0), (838, Int.negSucc 0)] },
  { level := 1, parent := 6, color := 24, mode := 1,
    vector := [(684, Int.ofNat 1)] },
  { level := 1, parent := 6, color := 25, mode := 1,
    vector := [(683, Int.ofNat 1)] },
  { level := 1, parent := 6, color := 26, mode := 1,
    vector := [(667, Int.ofNat 1), (668, Int.negSucc 0), (669, Int.ofNat 1), (670, Int.ofNat 1),
    (695, Int.negSucc 0), (761, Int.negSucc 0), (835, Int.negSucc 0)] },
  { level := 1, parent := 6, color := 27, mode := 1,
    vector := [(673, Int.negSucc 0), (764, Int.ofNat 1)] },
  { level := 1, parent := 7, color := 20, mode := 1,
    vector := [(605, Int.negSucc 0), (783, Int.ofNat 1), (784, Int.negSucc 0), (785, Int.ofNat 1),
    (786, Int.negSucc 0), (811, Int.ofNat 1), (839, Int.ofNat 1)] },
  { level := 1, parent := 7, color := 23, mode := 1,
    vector := [(602, Int.ofNat 1), (788, Int.negSucc 0)] },
  { level := 1, parent := 7, color := 24, mode := 1,
    vector := [(601, Int.ofNat 1), (790, Int.ofNat 1)] },
  { level := 1, parent := 7, color := 26, mode := 1,
    vector := [(598, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

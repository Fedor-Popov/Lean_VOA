/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData14 : List WordNode := [
  { level := 1, parent := 31, color := 27, mode := 1,
    vector := [(30, Int.negSucc 0), (57, Int.ofNat 1), (59, Int.ofNat 2), (86, Int.negSucc 1),
    (528, Int.ofNat 1), (618, Int.ofNat 1), (708, Int.negSucc 0), (768, Int.ofNat 1), (813,
    Int.ofNat 1), (814, Int.negSucc 1)] },
  { level := 1, parent := 32, color := 24, mode := 1,
    vector := [(638, Int.negSucc 3), (640, Int.ofNat 4), (641, Int.negSucc 3), (666, Int.ofNat 4),
    (700, Int.negSucc 3), (834, Int.ofNat 4)] },
  { level := 1, parent := 32, color := 26, mode := 1,
    vector := [(643, Int.negSucc 3)] },
  { level := 1, parent := 32, color := 27, mode := 1,
    vector := [(647, Int.negSucc 3), (707, Int.ofNat 4)] },
  { level := 1, parent := 33, color := 24, mode := 1,
    vector := [(568, Int.ofNat 2), (762, Int.negSucc 1)] },
  { level := 1, parent := 33, color := 25, mode := 1,
    vector := [(567, Int.ofNat 2), (763, Int.negSucc 1)] },
  { level := 1, parent := 33, color := 26, mode := 1,
    vector := [(551, Int.ofNat 2), (552, Int.negSucc 1), (553, Int.ofNat 2), (554, Int.ofNat 2),
    (579, Int.negSucc 1), (765, Int.negSucc 1), (831, Int.negSucc 1)] },
  { level := 1, parent := 33, color := 27, mode := 1,
    vector := [(557, Int.negSucc 1)] },
  { level := 1, parent := 34, color := 25, mode := 1,
    vector := [(638, Int.negSucc 3), (640, Int.negSucc 3), (641, Int.ofNat 4), (666, Int.ofNat 4),
    (730, Int.negSucc 3), (834, Int.ofNat 4)] },
  { level := 1, parent := 34, color := 26, mode := 1,
    vector := [(642, Int.negSucc 3)] },
  { level := 1, parent := 34, color := 27, mode := 1,
    vector := [(646, Int.negSucc 3), (736, Int.ofNat 4)] },
  { level := 1, parent := 35, color := 22, mode := 1,
    vector := [(23, Int.ofNat 2), (52, Int.negSucc 0), (667, Int.ofNat 1), (668, Int.ofNat 1),
    (669, Int.negSucc 0), (670, Int.negSucc 0), (695, Int.negSucc 0), (761, Int.negSucc 0), (793,
    Int.ofNat 1), (835, Int.negSucc 0)] },
  { level := 1, parent := 35, color := 24, mode := 1,
    vector := [(21, Int.negSucc 1), (50, Int.ofNat 1), (539, Int.negSucc 0), (671, Int.ofNat 1),
    (795, Int.ofNat 1)] },
  { level := 1, parent := 35, color := 25, mode := 1,
    vector := [(20, Int.negSucc 1), (49, Int.ofNat 1), (538, Int.negSucc 0), (672, Int.ofNat 1),
    (796, Int.ofNat 1)] },
  { level := 1, parent := 35, color := 26, mode := 1,
    vector := [(18, Int.negSucc 1), (47, Int.ofNat 1), (522, Int.negSucc 0), (523, Int.ofNat 1),
    (524, Int.negSucc 0), (525, Int.negSucc 0), (550, Int.ofNat 1), (645, Int.negSucc 0), (797,
    Int.ofNat 1), (830, Int.ofNat 1)] },
  { level := 1, parent := 35, color := 27, mode := 1,
    vector := [(1, Int.ofNat 2), (28, Int.negSucc 1), (30, Int.negSucc 0), (57, Int.ofNat 1),
    (528, Int.ofNat 1), (648, Int.ofNat 1), (678, Int.negSucc 0), (768, Int.ofNat 1), (812,
    Int.negSucc 1), (813, Int.ofNat 1)] },
  { level := 1, parent := 36, color := 23, mode := 1,
    vector := [(464, Int.ofNat 2), (466, Int.negSucc 1), (467, Int.negSucc 1), (492, Int.ofNat 2),
    (676, Int.negSucc 1), (828, Int.ofNat 2)] },
  { level := 1, parent := 36, color := 26, mode := 1,
    vector := [(471, Int.ofNat 2), (680, Int.negSucc 1)] },
  { level := 1, parent := 36, color := 27, mode := 1,
    vector := [(474, Int.negSucc 1)] },
  { level := 1, parent := 37, color := 27, mode := 1,
    vector := [(593, Int.ofNat 4)] },
  { level := 1, parent := 38, color := 23, mode := 1,
    vector := [(522, Int.negSucc 1), (524, Int.ofNat 2), (525, Int.ofNat 2), (550, Int.negSucc 1),
    (584, Int.negSucc 1), (614, Int.negSucc 1), (830, Int.negSucc 1)] },
  { level := 1, parent := 38, color := 26, mode := 1,
    vector := [(529, Int.negSucc 1)] },
  { level := 1, parent := 38, color := 27, mode := 1,
    vector := [(532, Int.ofNat 2), (592, Int.ofNat 2), (622, Int.ofNat 2), (681, Int.negSucc 1)]
    },
  { level := 1, parent := 39, color := 23, mode := 1,
    vector := [(493, Int.ofNat 2), (495, Int.negSucc 1), (496, Int.negSucc 1), (521, Int.ofNat 2),
    (675, Int.negSucc 1), (829, Int.ofNat 2)] },
  { level := 1, parent := 39, color := 26, mode := 1,
    vector := [(500, Int.ofNat 2), (679, Int.negSucc 1)] },
  { level := 1, parent := 39, color := 27, mode := 1,
    vector := [(503, Int.negSucc 1)] },
  { level := 1, parent := 40, color := 27, mode := 1,
    vector := [(621, Int.ofNat 4)] },
  { level := 1, parent := 41, color := 24, mode := 1,
    vector := [(464, Int.ofNat 1), (466, Int.negSucc 0), (467, Int.ofNat 1), (492, Int.negSucc 0),
    (706, Int.ofNat 1), (828, Int.negSucc 0)] },
  { level := 1, parent := 41, color := 26, mode := 1,
    vector := [(469, Int.ofNat 1), (709, Int.ofNat 1)] },
  { level := 1, parent := 41, color := 27, mode := 1,
    vector := [(473, Int.ofNat 1)] },
  { level := 1, parent := 42, color := 23, mode := 1,
    vector := [(48, Int.negSucc 0), (106, Int.ofNat 2), (734, Int.ofNat 1), (765, Int.negSucc 0)]
    },
  { level := 1, parent := 42, color := 24, mode := 1,
    vector := [(46, Int.ofNat 1), (104, Int.negSucc 1), (735, Int.ofNat 1), (766, Int.negSucc 0)]
    }
]

end VOA.DeligneAudit.D4Two.Certificate

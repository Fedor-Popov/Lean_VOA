/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData23 : List WordNode := [
  { level := 2, parent := 337, color := 23, mode := 1,
    vector := [(725, Int.ofNat 1), (727, Int.negSucc 0), (728, Int.negSucc 0), (753, Int.ofNat 1),
    (791, Int.negSucc 0)] },
  { level := 2, parent := 337, color := 26, mode := 1,
    vector := [(732, Int.ofNat 1), (795, Int.negSucc 0)] },
  { level := 2, parent := 337, color := 27, mode := 1,
    vector := [(735, Int.negSucc 0), (829, Int.ofNat 1)] },
  { level := 2, parent := 338, color := 27, mode := 1,
    vector := [(736, Int.negSucc 0)] },
  { level := 2, parent := 339, color := 27, mode := 1,
    vector := [(737, Int.negSucc 0)] },
  { level := 2, parent := 340, color := 27, mode := 1,
    vector := [(738, Int.negSucc 0), (798, Int.negSucc 0), (812, Int.ofNat 1), (813, Int.ofNat 1),
    (814, Int.ofNat 1), (815, Int.negSucc 0), (840, Int.negSucc 1)] },
  { level := 2, parent := 341, color := 27, mode := 1,
    vector := [(739, Int.negSucc 0), (816, Int.ofNat 1)] },
  { level := 2, parent := 342, color := 27, mode := 1,
    vector := [(740, Int.negSucc 1), (820, Int.ofNat 2)] },
  { level := 2, parent := 348, color := 25, mode := 1,
    vector := [(580, Int.ofNat 1), (582, Int.ofNat 1), (583, Int.negSucc 0), (608, Int.negSucc 0),
    (796, Int.negSucc 0), (832, Int.ofNat 1)] },
  { level := 2, parent := 348, color := 26, mode := 1,
    vector := [(584, Int.ofNat 1), (830, Int.ofNat 1)] },
  { level := 2, parent := 348, color := 27, mode := 1,
    vector := [(588, Int.ofNat 1), (798, Int.ofNat 1), (812, Int.ofNat 1), (813, Int.negSucc 1),
    (814, Int.ofNat 1), (815, Int.negSucc 0), (840, Int.ofNat 2)] },
  { level := 2, parent := 349, color := 27, mode := 1,
    vector := [(591, Int.ofNat 1), (817, Int.negSucc 0)] },
  { level := 2, parent := 350, color := 27, mode := 1,
    vector := [(592, Int.ofNat 1), (819, Int.ofNat 1)] },
  { level := 2, parent := 351, color := 27, mode := 1,
    vector := [(594, Int.ofNat 1)] },
  { level := 2, parent := 352, color := 27, mode := 1,
    vector := [(595, Int.ofNat 2), (825, Int.ofNat 2)] },
  { level := 2, parent := 353, color := 24, mode := 1,
    vector := [(609, Int.ofNat 1), (611, Int.negSucc 0), (612, Int.ofNat 1), (637, Int.negSucc 0),
    (795, Int.negSucc 0), (833, Int.ofNat 1)] },
  { level := 2, parent := 353, color := 26, mode := 1,
    vector := [(614, Int.ofNat 1), (830, Int.ofNat 1)] },
  { level := 2, parent := 353, color := 27, mode := 1,
    vector := [(618, Int.ofNat 1), (798, Int.ofNat 1), (812, Int.ofNat 1), (813, Int.negSucc 1),
    (814, Int.negSucc 0), (815, Int.ofNat 1), (840, Int.ofNat 2)] },
  { level := 2, parent := 354, color := 27, mode := 1,
    vector := [(620, Int.ofNat 1), (816, Int.negSucc 0)] },
  { level := 2, parent := 355, color := 27, mode := 1,
    vector := [(622, Int.ofNat 1), (819, Int.ofNat 1)] },
  { level := 2, parent := 356, color := 27, mode := 1,
    vector := [(623, Int.ofNat 1)] },
  { level := 2, parent := 357, color := 27, mode := 1,
    vector := [(624, Int.ofNat 2), (824, Int.ofNat 2)] },
  { level := 2, parent := 368, color := 23, mode := 1,
    vector := [(638, Int.ofNat 1), (640, Int.negSucc 0), (641, Int.negSucc 0), (666, Int.ofNat 1),
    (794, Int.ofNat 1), (834, Int.negSucc 0)] },
  { level := 2, parent := 368, color := 26, mode := 1,
    vector := [(645, Int.ofNat 1), (830, Int.negSucc 0)] },
  { level := 2, parent := 368, color := 27, mode := 1,
    vector := [(648, Int.negSucc 0), (798, Int.negSucc 0), (812, Int.ofNat 1), (813, Int.ofNat 2),
    (814, Int.negSucc 0), (815, Int.negSucc 0), (840, Int.negSucc 1)] },
  { level := 2, parent := 369, color := 27, mode := 1,
    vector := [(650, Int.negSucc 0), (816, Int.ofNat 1)] },
  { level := 2, parent := 370, color := 27, mode := 1,
    vector := [(651, Int.negSucc 0), (817, Int.ofNat 1)] },
  { level := 2, parent := 371, color := 27, mode := 1,
    vector := [(652, Int.negSucc 0)] },
  { level := 2, parent := 372, color := 27, mode := 1,
    vector := [(653, Int.negSucc 1), (823, Int.negSucc 1)] },
  { level := 2, parent := 386, color := 25, mode := 1,
    vector := [(464, Int.ofNat 1), (466, Int.ofNat 1), (467, Int.negSucc 0), (492, Int.negSucc 0),
    (767, Int.ofNat 1), (828, Int.ofNat 1)] },
  { level := 2, parent := 386, color := 26, mode := 1,
    vector := [(468, Int.ofNat 1), (798, Int.negSucc 0), (815, Int.ofNat 2), (840, Int.negSucc 1)]
    },
  { level := 2, parent := 386, color := 27, mode := 1,
    vector := [(472, Int.ofNat 1), (769, Int.negSucc 0), (818, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

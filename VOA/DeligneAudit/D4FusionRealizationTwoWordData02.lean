/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

def wordData02 : List WordNode := [
  { level := 0, parent := 42, color := 18, mode := 0,
    vector := [(200, Int.negSucc 0), (760, Int.negSucc 0)] },
  { level := 0, parent := 42, color := 16, mode := 0,
    vector := [(54, Int.negSucc 1), (112, Int.ofNat 4), (142, Int.ofNat 2), (726, Int.negSucc 1),
    (728, Int.ofNat 4), (758, Int.ofNat 2)] },
  { level := 0, parent := 43, color := 18, mode := 0,
    vector := [(24, Int.ofNat 2), (53, Int.negSucc 3), (82, Int.ofNat 2), (111, Int.ofNat 2),
    (486, Int.negSucc 1), (571, Int.ofNat 2), (599, Int.ofNat 2), (654, Int.negSucc 1), (696,
    Int.ofNat 2), (697, Int.negSucc 3), (698, Int.ofNat 2), (699, Int.ofNat 2)] },
  { level := 0, parent := 43, color := 16, mode := 0,
    vector := [(544, Int.ofNat 4), (656, Int.ofNat 4)] },
  { level := 0, parent := 44, color := 19, mode := 0,
    vector := [(23, Int.negSucc 2), (52, Int.ofNat 3), (81, Int.negSucc 0), (110, Int.negSucc 0),
    (229, Int.ofNat 1), (485, Int.ofNat 1), (513, Int.ofNat 1), (597, Int.ofNat 1), (625,
    Int.ofNat 1), (667, Int.negSucc 2), (668, Int.ofNat 3), (669, Int.negSucc 0), (670,
    Int.negSucc 0), (761, Int.ofNat 1)] },
  { level := 0, parent := 44, color := 17, mode := 0,
    vector := [(24, Int.ofNat 1), (53, Int.negSucc 2), (82, Int.ofNat 3), (111, Int.ofNat 1),
    (171, Int.ofNat 1), (486, Int.negSucc 0), (571, Int.ofNat 1), (599, Int.ofNat 1), (654,
    Int.negSucc 0), (696, Int.ofNat 1), (697, Int.negSucc 2), (698, Int.ofNat 3), (699, Int.ofNat
    1), (759, Int.ofNat 1)] },
  { level := 0, parent := 44, color := 16, mode := 0,
    vector := [(25, Int.ofNat 1), (54, Int.negSucc 2), (83, Int.ofNat 1), (112, Int.ofNat 3),
    (142, Int.ofNat 1), (515, Int.negSucc 0), (572, Int.ofNat 1), (628, Int.ofNat 1), (655,
    Int.negSucc 0), (725, Int.ofNat 1), (726, Int.negSucc 2), (727, Int.ofNat 1), (728, Int.ofNat
    3), (758, Int.ofNat 1)] },
  { level := 0, parent := 46, color := 16, mode := 0,
    vector := [(54, Int.negSucc 0), (83, Int.ofNat 2), (515, Int.negSucc 0), (655, Int.negSucc 0),
    (726, Int.negSucc 0), (727, Int.ofNat 2)] },
  { level := 0, parent := 48, color := 19, mode := 0,
    vector := [(23, Int.negSucc 0), (52, Int.ofNat 3), (81, Int.negSucc 0), (110, Int.negSucc 2),
    (229, Int.ofNat 1), (317, Int.ofNat 1), (485, Int.ofNat 1), (625, Int.ofNat 1), (667,
    Int.negSucc 0), (668, Int.ofNat 3), (669, Int.negSucc 0), (670, Int.negSucc 2), (761,
    Int.ofNat 1), (793, Int.ofNat 1)] },
  { level := 0, parent := 48, color := 17, mode := 0,
    vector := [(24, Int.ofNat 1), (53, Int.negSucc 2), (82, Int.ofNat 1), (111, Int.ofNat 3),
    (171, Int.ofNat 1), (288, Int.negSucc 0), (486, Int.negSucc 0), (654, Int.negSucc 0), (696,
    Int.ofNat 1), (697, Int.negSucc 2), (698, Int.ofNat 1), (699, Int.ofNat 3), (759, Int.ofNat
    1), (792, Int.negSucc 0)] },
  { level := 0, parent := 48, color := 16, mode := 0,
    vector := [(25, Int.ofNat 1), (54, Int.negSucc 3), (83, Int.ofNat 1), (112, Int.ofNat 5),
    (142, Int.ofNat 3), (259, Int.negSucc 0), (725, Int.ofNat 1), (726, Int.negSucc 3), (727,
    Int.ofNat 1), (728, Int.ofNat 5), (758, Int.ofNat 3), (791, Int.negSucc 0)] },
  { level := 0, parent := 52, color := 19, mode := 0,
    vector := [(24, Int.ofNat 8), (53, Int.negSucc 3), (571, Int.ofNat 4), (599, Int.ofNat 4),
    (696, Int.ofNat 8), (697, Int.negSucc 3)] },
  { level := 0, parent := 52, color := 16, mode := 0,
    vector := [(573, Int.negSucc 3), (657, Int.negSucc 3)] },
  { level := 0, parent := 54, color := 16, mode := 0,
    vector := [(25, Int.ofNat 4), (54, Int.negSucc 1), (572, Int.ofNat 2), (628, Int.ofNat 2),
    (725, Int.ofNat 4), (726, Int.negSucc 1)] },
  { level := 0, parent := 56, color := 18, mode := 0,
    vector := [(480, Int.ofNat 4)] },
  { level := 0, parent := 56, color := 16, mode := 0,
    vector := [(49, Int.ofNat 2), (107, Int.negSucc 3), (482, Int.negSucc 1), (538, Int.negSucc
    1), (581, Int.ofNat 2), (583, Int.negSucc 3)] },
  { level := 0, parent := 57, color := 18, mode := 0,
    vector := [(197, Int.ofNat 2), (481, Int.ofNat 2), (509, Int.ofNat 2), (673, Int.ofNat 2)] },
  { level := 0, parent := 57, color := 16, mode := 0,
    vector := [(50, Int.ofNat 4), (108, Int.negSucc 7), (139, Int.negSucc 3), (610, Int.ofNat 4),
    (612, Int.negSucc 7), (671, Int.negSucc 3)] },
  { level := 0, parent := 58, color := 18, mode := 0,
    vector := [(20, Int.negSucc 3), (49, Int.ofNat 8), (78, Int.negSucc 3), (107, Int.negSucc 3),
    (482, Int.negSucc 3), (538, Int.negSucc 3), (580, Int.negSucc 3), (581, Int.ofNat 8), (582,
    Int.negSucc 3), (583, Int.negSucc 3)] },
  { level := 0, parent := 58, color := 16, mode := 0,
    vector := [(540, Int.ofNat 8)] },
  { level := 0, parent := 59, color := 19, mode := 0,
    vector := [(226, Int.negSucc 1), (674, Int.negSucc 1)] },
  { level := 0, parent := 59, color := 17, mode := 0,
    vector := [(20, Int.negSucc 1), (49, Int.ofNat 6), (78, Int.negSucc 5), (107, Int.negSucc 1),
    (168, Int.negSucc 1), (482, Int.negSucc 1), (538, Int.negSucc 1), (580, Int.negSucc 1), (581,
    Int.ofNat 6), (582, Int.negSucc 5), (583, Int.negSucc 1), (672, Int.negSucc 1)] },
  { level := 0, parent := 59, color := 16, mode := 0,
    vector := [(21, Int.negSucc 1), (50, Int.ofNat 6), (79, Int.negSucc 1), (108, Int.negSucc 5),
    (139, Int.negSucc 1), (511, Int.negSucc 1), (539, Int.negSucc 1), (609, Int.negSucc 1), (610,
    Int.ofNat 6), (611, Int.negSucc 1), (612, Int.negSucc 5), (671, Int.negSucc 1)] },
  { level := 0, parent := 61, color := 16, mode := 0,
    vector := [(50, Int.ofNat 2), (79, Int.negSucc 3), (511, Int.negSucc 1), (539, Int.negSucc 1),
    (610, Int.ofNat 2), (611, Int.negSucc 3)] },
  { level := 0, parent := 62, color := 18, mode := 0,
    vector := [(510, Int.ofNat 4)] },
  { level := 0, parent := 63, color := 18, mode := 0,
    vector := [(198, Int.negSucc 0), (483, Int.ofNat 1), (567, Int.ofNat 1), (702, Int.negSucc 0)]
    },
  { level := 0, parent := 63, color := 16, mode := 0,
    vector := [(51, Int.negSucc 1), (109, Int.ofNat 4), (140, Int.ofNat 2), (639, Int.negSucc 1),
    (641, Int.ofNat 4), (700, Int.ofNat 2)] },
  { level := 0, parent := 64, color := 19, mode := 0,
    vector := [(197, Int.ofNat 1), (316, Int.negSucc 0), (673, Int.ofNat 1), (764, Int.negSucc 0)]
    },
  { level := 0, parent := 64, color := 17, mode := 0,
    vector := [(198, Int.negSucc 0), (287, Int.ofNat 1), (702, Int.negSucc 0), (763, Int.ofNat 1)]
    },
  { level := 0, parent := 64, color := 16, mode := 0,
    vector := [(199, Int.negSucc 0), (258, Int.ofNat 1), (731, Int.negSucc 0), (762, Int.ofNat 1)]
    },
  { level := 0, parent := 65, color := 16, mode := 0,
    vector := [(141, Int.ofNat 6), (729, Int.ofNat 6)] },
  { level := 0, parent := 66, color := 19, mode := 0,
    vector := [(20, Int.negSucc 5), (49, Int.ofNat 6), (78, Int.negSucc 1), (107, Int.negSucc 1),
    (227, Int.ofNat 2), (482, Int.negSucc 1), (538, Int.negSucc 1), (580, Int.negSucc 5), (581,
    Int.ofNat 6), (582, Int.negSucc 1), (583, Int.negSucc 1), (703, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

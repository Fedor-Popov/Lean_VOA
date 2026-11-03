/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordTypes

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.D4Two.Certificate

set_option maxHeartbeats 2000000 in
-- Literal action payloads require additional elaboration steps.
def actionData237 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 6), (130, Int.negSucc 1), (404,
    Int.negSucc 9), (412, Int.ofNat 8), (454, Int.negSucc 10), (478, Int.ofNat 2), (485,
    Int.negSucc 7), (504, Int.ofNat 4), (512, Int.ofNat 7), (780, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (131,
    Int.negSucc 1), (385, Int.negSucc 23), (396, Int.ofNat 8), (433, Int.negSucc 23), (471,
    Int.negSucc 8), (479, Int.negSucc 1), (486, Int.ofNat 8), (497, Int.ofNat 14), (508, Int.ofNat
    1), (773, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 12), (130, Int.negSucc 1), (132,
    Int.negSucc 3), (404, Int.negSucc 23), (412, Int.ofNat 16), (454, Int.negSucc 23), (478,
    Int.ofNat 4), (485, Int.negSucc 15), (493, Int.negSucc 3), (504, Int.ofNat 9), (512, Int.ofNat
    14), (780, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 4), (115, Int.ofNat 1), (117,
    Int.negSucc 1), (128, Int.negSucc 1), (391, Int.ofNat 36), (429, Int.negSucc 51), (441,
    Int.ofNat 20), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.negSucc 21), (482,
    Int.ofNat 22), (490, Int.ofNat 14), (695, Int.ofNat 20), (745, Int.negSucc 19), (752,
    Int.negSucc 19), (759, Int.ofNat 20)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (404,
    Int.negSucc 5), (412, Int.ofNat 4), (454, Int.negSucc 5), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 2), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 2), (430, Int.negSucc 31), (442,
    Int.ofNat 32), (480, Int.negSucc 15), (516, Int.negSucc 15), (528, Int.ofNat 32), (766,
    Int.negSucc 15), (787, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 1), (415, Int.negSucc 0), (540,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (425, Int.negSucc 0), (544,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (139, Int.ofNat 4), (148,
    Int.negSucc 0), (430, Int.negSucc 59), (442, Int.ofNat 44), (443, Int.ofNat 8), (480,
    Int.negSucc 27), (488, Int.negSucc 19), (516, Int.negSucc 19), (520, Int.negSucc 7), (528,
    Int.ofNat 40), (535, Int.ofNat 8), (547, Int.ofNat 12), (696, Int.ofNat 8), (709, Int.ofNat
    8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 27),
    (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat 20)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (149, Int.negSucc 1), (418,
    Int.negSucc 3), (472, Int.negSucc 3), (539, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.ofNat 2), (148, Int.ofNat 3), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 15), (448, Int.ofNat 8), (480, Int.ofNat
    4), (488, Int.negSucc 7), (495, Int.negSucc 11), (524, Int.negSucc 7), (528, Int.negSucc 3),
    (535, Int.ofNat 4), (550, Int.ofNat 12), (774, Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (498, Int.ofNat 4), (532,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 5), (139, Int.ofNat 6), (148,
    Int.negSucc 1), (430, Int.negSucc 51), (442, Int.ofNat 12), (443, Int.ofNat 16), (480,
    Int.negSucc 27), (488, Int.negSucc 43), (516, Int.negSucc 3), (520, Int.negSucc 15), (528,
    Int.ofNat 8), (535, Int.ofNat 16), (547, Int.ofNat 28), (696, Int.ofNat 16), (709, Int.ofNat
    16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 19),
    (774, Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 2), (472,
    Int.negSucc 1), (539, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 11), (139, Int.ofNat 12), (148,
    Int.negSucc 0), (150, Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 127), (442,
    Int.ofNat 24), (443, Int.ofNat 32), (448, Int.ofNat 8), (480, Int.negSucc 55), (488,
    Int.negSucc 95), (495, Int.negSucc 15), (516, Int.negSucc 7), (520, Int.negSucc 31), (524,
    Int.negSucc 7), (528, Int.ofNat 16), (535, Int.ofNat 36), (547, Int.ofNat 56), (550, Int.ofNat
    16), (696, Int.ofNat 32), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31),
    (760, Int.ofNat 32), (766, Int.negSucc 39), (774, Int.negSucc 39), (781, Int.ofNat 32), (787,
    Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 3), (150, Int.negSucc 5), (151,
    Int.ofNat 2), (430, Int.negSucc 23), (448, Int.ofNat 8), (488, Int.negSucc 7), (495,
    Int.negSucc 15), (524, Int.negSucc 7), (535, Int.ofNat 4), (550, Int.ofNat 16), (774,
    Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 3), (153, Int.ofNat 4), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 15), (463, Int.ofNat 8), (480, Int.ofNat
    4), (488, Int.negSucc 7), (510, Int.negSucc 5), (516, Int.ofNat 2), (520, Int.negSucc 3),
    (556, Int.ofNat 4), (560, Int.ofNat 6), (781, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 1), (161, Int.negSucc 0), (451,
    Int.negSucc 0), (505, Int.negSucc 0), (543, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 0), (513, Int.ofNat 1), (531,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.ofNat 2), (148, Int.negSucc 1), (150,
    Int.ofNat 4), (157, Int.ofNat 2), (162, Int.negSucc 3), (430, Int.negSucc 3), (495,
    Int.negSucc 3), (510, Int.negSucc 1), (524, Int.negSucc 1), (556, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(159, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 11), (139, Int.ofNat 12), (148,
    Int.negSucc 0), (160, Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 127), (442,
    Int.ofNat 24), (443, Int.ofNat 32), (463, Int.ofNat 8), (480, Int.negSucc 55), (488,
    Int.negSucc 95), (510, Int.negSucc 7), (516, Int.negSucc 7), (520, Int.negSucc 35), (528,
    Int.ofNat 16), (535, Int.ofNat 32), (547, Int.ofNat 56), (556, Int.ofNat 4), (560, Int.ofNat
    8), (696, Int.ofNat 32), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31),
    (760, Int.ofNat 32), (766, Int.negSucc 39), (774, Int.negSucc 31), (781, Int.ofNat 40), (787,
    Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.negSucc 1), (451, Int.negSucc 2), (505,
    Int.negSucc 1), (543, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(143, Int.ofNat 4), (148, Int.ofNat 4), (150,
    Int.negSucc 7), (151, Int.ofNat 4), (162, Int.negSucc 3), (430, Int.negSucc 47), (448,
    Int.ofNat 16), (480, Int.ofNat 4), (488, Int.negSucc 15), (495, Int.negSucc 31), (510,
    Int.negSucc 1), (524, Int.negSucc 17), (528, Int.negSucc 3), (535, Int.ofNat 8), (550,
    Int.ofNat 28), (556, Int.ofNat 1), (774, Int.negSucc 15), (795, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 9), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.negSucc 3), (157, Int.ofNat 4), (162,
    Int.negSucc 3), (430, Int.negSucc 87), (442, Int.ofNat 32), (443, Int.ofNat 24), (480,
    Int.negSucc 31), (488, Int.negSucc 55), (495, Int.negSucc 7), (510, Int.negSucc 3), (516,
    Int.negSucc 9), (520, Int.negSucc 23), (524, Int.negSucc 1), (528, Int.ofNat 20), (535,
    Int.ofNat 24), (547, Int.ofNat 32), (550, Int.ofNat 4), (556, Int.ofNat 1), (560, Int.ofNat
    2), (696, Int.ofNat 24), (709, Int.ofNat 24), (746, Int.negSucc 23), (753, Int.negSucc 23),
    (760, Int.ofNat 24), (766, Int.negSucc 31), (774, Int.negSucc 23), (781, Int.ofNat 24), (787,
    Int.ofNat 8)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData360 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(122, Int.negSucc 1), (126, Int.ofNat 1), (404,
    Int.negSucc 0), (454, Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(128, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 11), (468, Int.negSucc 3), (482, Int.ofNat 3), (490, Int.ofNat 4), (695, Int.ofNat
    6), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4), (823, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.negSucc 0), (404, Int.negSucc 9), (412,
    Int.ofNat 8), (454, Int.negSucc 8), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 7), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(131, Int.ofNat 2), (385, Int.negSucc 15), (396,
    Int.ofNat 16), (433, Int.negSucc 3), (471, Int.negSucc 4), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 10), (508, Int.ofNat 1), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 4), (130, Int.negSucc 5), (132,
    Int.ofNat 4), (404, Int.negSucc 31), (412, Int.ofNat 32), (454, Int.negSucc 31), (478,
    Int.negSucc 3), (485, Int.negSucc 15), (493, Int.ofNat 4), (504, Int.ofNat 11), (512,
    Int.ofNat 26), (780, Int.ofNat 32), (817, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.negSucc 1), (391, Int.ofNat 8), (429, Int.negSucc 23), (441,
    Int.negSucc 3), (447, Int.ofNat 4), (462, Int.negSucc 3), (468, Int.negSucc 7), (482,
    Int.ofNat 4), (490, Int.ofNat 12), (695, Int.ofNat 12), (745, Int.negSucc 7), (752,
    Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (404,
    Int.negSucc 7), (412, Int.ofNat 8), (454, Int.negSucc 7), (485, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 6), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 2), (465,
    Int.negSucc 1), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 0), (544,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 15), (442, Int.ofNat 8), (480, Int.negSucc 15), (488, Int.negSucc 3), (516,
    Int.negSucc 5), (528, Int.ofNat 12), (547, Int.ofNat 4), (766, Int.negSucc 7), (787, Int.ofNat
    8), (824, Int.ofNat 4), (826, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 1), (141, Int.ofNat 1), (415,
    Int.negSucc 3), (465, Int.negSucc 3), (540, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 1), (430, Int.negSucc 11), (442, Int.ofNat 8), (480, Int.negSucc 13), (488,
    Int.negSucc 3), (495, Int.ofNat 2), (516, Int.negSucc 5), (528, Int.ofNat 10), (547, Int.ofNat
    4), (550, Int.negSucc 1), (766, Int.negSucc 7), (787, Int.ofNat 8), (824, Int.ofNat 4), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 2), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (498, Int.ofNat 4), (532, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (148, Int.negSucc 0), (430,
    Int.negSucc 47), (442, Int.ofNat 8), (443, Int.ofNat 16), (480, Int.negSucc 39), (488,
    Int.negSucc 35), (516, Int.negSucc 5), (520, Int.negSucc 11), (528, Int.ofNat 12), (535,
    Int.ofNat 12), (547, Int.ofNat 28), (696, Int.ofNat 20), (709, Int.ofNat 16), (746,
    Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23), (774,
    Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 8), (824, Int.ofNat 12), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 13), (139, Int.ofNat 4), (148,
    Int.negSucc 4), (150, Int.ofNat 2), (151, Int.ofNat 2), (430, Int.negSucc 175), (442,
    Int.ofNat 16), (443, Int.ofNat 64), (448, Int.ofNat 32), (480, Int.negSucc 127), (488,
    Int.negSucc 127), (495, Int.negSucc 7), (516, Int.negSucc 11), (520, Int.negSucc 47), (524,
    Int.negSucc 11), (528, Int.ofNat 24), (535, Int.ofNat 44), (547, Int.ofNat 104), (550,
    Int.ofNat 24), (696, Int.ofNat 80), (709, Int.ofNat 64), (746, Int.negSucc 63), (753,
    Int.negSucc 63), (760, Int.ofNat 64), (766, Int.negSucc 79), (774, Int.negSucc 79), (781,
    Int.ofNat 64), (787, Int.ofNat 16), (795, Int.ofNat 16), (824, Int.ofNat 48), (826,
    Int.negSucc 7), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (139, Int.ofNat 4), (148,
    Int.ofNat 1), (150, Int.negSucc 5), (151, Int.ofNat 10), (430, Int.negSucc 175), (443,
    Int.ofNat 32), (448, Int.ofNat 128), (480, Int.negSucc 47), (488, Int.negSucc 55), (495,
    Int.negSucc 71), (520, Int.negSucc 23), (524, Int.negSucc 59), (535, Int.ofNat 20), (547,
    Int.ofNat 48), (550, Int.ofNat 120), (696, Int.ofNat 40), (709, Int.ofNat 32), (746,
    Int.negSucc 31), (753, Int.negSucc 31), (760, Int.ofNat 32), (766, Int.negSucc 31), (774,
    Int.negSucc 111), (781, Int.ofNat 32), (795, Int.ofNat 80), (824, Int.ofNat 56), (829,
    Int.negSucc 39)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (430, Int.negSucc 3), (480,
    Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 0), (458, Int.negSucc 0), (513,
    Int.negSucc 0), (531, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(153, Int.negSucc 1), (157, Int.ofNat 1), (430,
    Int.negSucc 1), (480, Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 1), (159, Int.ofNat 1), (458,
    Int.negSucc 0), (513, Int.negSucc 1), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (148, Int.ofNat 1), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 127), (442, Int.ofNat 16), (443,
    Int.ofNat 32), (463, Int.ofNat 16), (480, Int.negSucc 79), (488, Int.negSucc 79), (510,
    Int.negSucc 11), (516, Int.negSucc 11), (520, Int.negSucc 27), (528, Int.ofNat 24), (535,
    Int.ofNat 24), (547, Int.ofNat 56), (556, Int.ofNat 6), (560, Int.ofNat 12), (696, Int.ofNat
    40), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31), (760, Int.ofNat 32),
    (766, Int.negSucc 47), (774, Int.negSucc 31), (781, Int.ofNat 48), (787, Int.ofNat 16), (802,
    Int.ofNat 16), (824, Int.ofNat 32), (826, Int.negSucc 7), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.negSucc 1), (451, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (148, Int.ofNat 2), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (160, Int.negSucc 5), (162, Int.ofNat 4), (164, Int.ofNat
    1), (430, Int.negSucc 127), (442, Int.ofNat 16), (443, Int.ofNat 32), (448, Int.ofNat 32),
    (463, Int.ofNat 16), (480, Int.negSucc 75), (488, Int.negSucc 71), (510, Int.negSucc 9), (516,
    Int.negSucc 11), (520, Int.negSucc 27), (524, Int.negSucc 9), (528, Int.ofNat 20), (535,
    Int.ofNat 20), (547, Int.ofNat 56), (550, Int.ofNat 20), (556, Int.ofNat 5), (560, Int.ofNat
    12), (696, Int.ofNat 40), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31),
    (760, Int.ofNat 32), (766, Int.negSucc 47), (774, Int.negSucc 47), (781, Int.ofNat 48), (787,
    Int.ofNat 16), (795, Int.ofNat 16), (802, Int.ofNat 16), (824, Int.ofNat 40), (826,
    Int.negSucc 7), (829, Int.negSucc 7), (832, Int.negSucc 7)] }
]

end VOA.DeligneAudit.D4Two.Certificate

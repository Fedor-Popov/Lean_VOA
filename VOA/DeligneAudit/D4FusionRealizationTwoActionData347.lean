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
def actionData347 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 11), (468, Int.negSucc 2), (482, Int.ofNat 4), (490, Int.ofNat 4), (695, Int.ofNat
    6), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4), (823, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 19), (396,
    Int.ofNat 8), (433, Int.negSucc 17), (471, Int.negSucc 5), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 14), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 15), (396, Int.ofNat 8), (433, Int.negSucc 15), (471, Int.negSucc 5), (486,
    Int.ofNat 4), (497, Int.ofNat 12), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (120,
    Int.ofNat 2), (380, Int.negSucc 11), (390, Int.ofNat 8), (421, Int.negSucc 13), (464,
    Int.negSucc 4), (475, Int.ofNat 12), (487, Int.ofNat 4), (509, Int.negSucc 0), (765, Int.ofNat
    8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (454, Int.ofNat 1), (478,
    Int.negSucc 1), (512, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.ofNat 2), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (124, Int.ofNat 1), (380,
    Int.negSucc 1), (421, Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (125, Int.ofNat 1), (385,
    Int.negSucc 1), (433, Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(126, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (128, Int.ofNat 1), (391,
    Int.ofNat 16), (429, Int.negSucc 23), (462, Int.ofNat 4), (468, Int.negSucc 7), (482,
    Int.ofNat 9), (490, Int.ofNat 10), (695, Int.ofNat 18), (745, Int.negSucc 11), (752,
    Int.negSucc 11), (759, Int.ofNat 12), (823, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.ofNat 1), (404, Int.negSucc 7), (412,
    Int.ofNat 16), (454, Int.negSucc 2), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 5), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (131,
    Int.ofNat 2), (385, Int.negSucc 31), (396, Int.ofNat 16), (433, Int.negSucc 31), (471,
    Int.negSucc 10), (479, Int.ofNat 2), (486, Int.ofNat 8), (497, Int.ofNat 26), (508,
    Int.negSucc 0), (773, Int.ofNat 16), (820, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.ofNat 4), (404, Int.negSucc 15), (412,
    Int.ofNat 32), (454, Int.negSucc 3), (478, Int.negSucc 3), (485, Int.negSucc 7), (493,
    Int.negSucc 3), (504, Int.ofNat 5), (512, Int.ofNat 10), (780, Int.ofNat 16), (817, Int.ofNat
    8)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (117,
    Int.negSucc 1), (128, Int.ofNat 2), (391, Int.ofNat 8), (429, Int.negSucc 23), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.ofNat 4), (468, Int.negSucc 3), (482,
    Int.ofNat 8), (490, Int.ofNat 12), (695, Int.ofNat 12), (745, Int.negSucc 7), (752,
    Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (134,
    Int.ofNat 2), (404, Int.negSucc 19), (412, Int.ofNat 40), (454, Int.negSucc 11), (485,
    Int.negSucc 3), (504, Int.ofNat 9), (512, Int.ofNat 18), (780, Int.ofNat 24), (817, Int.ofNat
    12)] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 0), (540,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 2), (476,
    Int.negSucc 3), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 15), (442, Int.ofNat 8), (480, Int.negSucc 15), (488, Int.negSucc 3), (516,
    Int.negSucc 5), (528, Int.ofNat 12), (547, Int.ofNat 4), (766, Int.negSucc 7), (787, Int.ofNat
    8), (824, Int.ofNat 4), (826, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 0), (430, Int.negSucc 3), (480,
    Int.negSucc 1), (495, Int.negSucc 1), (528, Int.ofNat 2), (550, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (437, Int.negSucc 3), (498,
    Int.negSucc 3), (532, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (148, Int.negSucc 0), (430,
    Int.negSucc 47), (442, Int.ofNat 8), (443, Int.ofNat 16), (480, Int.negSucc 39), (488,
    Int.negSucc 35), (516, Int.negSucc 5), (520, Int.negSucc 11), (528, Int.ofNat 12), (535,
    Int.ofNat 12), (547, Int.ofNat 28), (696, Int.ofNat 20), (709, Int.ofNat 16), (746,
    Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23), (774,
    Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 8), (824, Int.ofNat 12), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (148, Int.ofNat 1), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 127), (442, Int.ofNat 16), (443,
    Int.ofNat 32), (448, Int.ofNat 16), (480, Int.negSucc 79), (488, Int.negSucc 79), (495,
    Int.negSucc 23), (516, Int.negSucc 11), (520, Int.negSucc 23), (524, Int.negSucc 11), (528,
    Int.ofNat 24), (535, Int.ofNat 28), (547, Int.ofNat 56), (550, Int.ofNat 24), (696, Int.ofNat
    40), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31), (760, Int.ofNat 32),
    (766, Int.negSucc 47), (774, Int.negSucc 47), (781, Int.ofNat 32), (787, Int.ofNat 16), (795,
    Int.ofNat 16), (824, Int.ofNat 32), (826, Int.negSucc 7), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 3), (150, Int.negSucc 5), (151,
    Int.ofNat 2), (430, Int.negSucc 31), (448, Int.ofNat 16), (488, Int.negSucc 7), (495,
    Int.negSucc 23), (524, Int.negSucc 11), (535, Int.ofNat 4), (550, Int.ofNat 24), (774,
    Int.negSucc 15), (795, Int.ofNat 16), (824, Int.ofNat 8), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (152, Int.ofNat 1), (425,
    Int.negSucc 1), (476, Int.negSucc 3), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (153,
    Int.ofNat 2), (430, Int.negSucc 11), (442, Int.ofNat 8), (480, Int.negSucc 13), (488,
    Int.negSucc 3), (510, Int.ofNat 1), (516, Int.negSucc 4), (528, Int.ofNat 12), (547, Int.ofNat
    4), (560, Int.negSucc 0), (766, Int.negSucc 7), (787, Int.ofNat 8), (824, Int.ofNat 4), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 1), (513, Int.ofNat 1), (531,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 0), (157, Int.ofNat 1), (430,
    Int.negSucc 1), (480, Int.negSucc 1), (495, Int.negSucc 1), (528, Int.ofNat 2), (550,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (158, Int.ofNat 1), (437,
    Int.negSucc 1), (498, Int.negSucc 3), (532, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(159, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 13), (139, Int.ofNat 4), (148,
    Int.negSucc 4), (160, Int.ofNat 2), (164, Int.ofNat 1), (430, Int.negSucc 175), (442,
    Int.ofNat 16), (443, Int.ofNat 64), (463, Int.ofNat 32), (480, Int.negSucc 127), (488,
    Int.negSucc 127), (510, Int.negSucc 3), (516, Int.negSucc 11), (520, Int.negSucc 43), (528,
    Int.ofNat 24), (535, Int.ofNat 48), (547, Int.ofNat 104), (556, Int.ofNat 6), (560, Int.ofNat
    12), (696, Int.ofNat 80), (709, Int.ofNat 64), (746, Int.negSucc 63), (753, Int.negSucc 63),
    (760, Int.ofNat 64), (766, Int.negSucc 79), (774, Int.negSucc 63), (781, Int.ofNat 80), (787,
    Int.ofNat 16), (802, Int.ofNat 16), (824, Int.ofNat 48), (826, Int.negSucc 7), (832,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.ofNat 2), (451, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(143, Int.negSucc 3), (148, Int.ofNat 8), (150,
    Int.negSucc 15), (151, Int.ofNat 4), (162, Int.ofNat 4), (430, Int.negSucc 63), (448,
    Int.ofNat 32), (480, Int.negSucc 3), (488, Int.negSucc 15), (495, Int.negSucc 47), (510,
    Int.ofNat 2), (524, Int.negSucc 21), (528, Int.ofNat 4), (535, Int.ofNat 8), (550, Int.ofNat
    52), (556, Int.negSucc 0), (774, Int.negSucc 31), (795, Int.ofNat 32), (824, Int.ofNat 16),
    (829, Int.negSucc 15)] }
]

end VOA.DeligneAudit.D4Two.Certificate

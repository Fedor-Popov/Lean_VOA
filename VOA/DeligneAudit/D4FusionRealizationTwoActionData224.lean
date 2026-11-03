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
def actionData224 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(81, Int.negSucc 2), (86, Int.ofNat 2), (98, Int.negSucc
    3), (102, Int.ofNat 4), (357, Int.negSucc 27), (384, Int.ofNat 28), (416, Int.ofNat 14), (427,
    Int.negSucc 15), (435, Int.negSucc 13), (440, Int.ofNat 12), (460, Int.ofNat 4), (751,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 5), (97, Int.ofNat 2), (99, Int.negSucc
    3), (103, Int.ofNat 4), (372, Int.negSucc 27), (403, Int.ofNat 14), (426, Int.ofNat 16), (439,
    Int.negSucc 11), (445, Int.negSucc 3), (449, Int.negSucc 6), (456, Int.negSucc 6), (758,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.ofNat 1), (372, Int.negSucc 7), (403,
    Int.ofNat 8), (411, Int.negSucc 3), (426, Int.ofNat 8), (449, Int.negSucc 1), (456,
    Int.negSucc 1), (758, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(105, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (380, Int.ofNat 8), (390,
    Int.negSucc 7), (421, Int.ofNat 4), (464, Int.ofNat 4), (475, Int.negSucc 7), (765,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 1), (380,
    Int.ofNat 16), (390, Int.negSucc 9), (421, Int.ofNat 12), (464, Int.ofNat 6), (475,
    Int.negSucc 11), (487, Int.negSucc 3), (765, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (391, Int.negSucc 7), (429,
    Int.ofNat 16), (441, Int.negSucc 3), (468, Int.ofNat 4), (482, Int.negSucc 3), (490,
    Int.negSucc 5), (695, Int.negSucc 3), (745, Int.ofNat 4), (752, Int.ofNat 4), (759,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(375, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (380,
    Int.ofNat 16), (390, Int.negSucc 3), (421, Int.ofNat 12), (464, Int.ofNat 4), (475,
    Int.negSucc 7), (487, Int.negSucc 3), (494, Int.negSucc 3), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (385,
    Int.ofNat 16), (396, Int.negSucc 3), (433, Int.ofNat 12), (471, Int.ofNat 4), (479,
    Int.negSucc 3), (486, Int.negSucc 3), (497, Int.negSucc 7), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (115, Int.ofNat 2), (391,
    Int.negSucc 15), (429, Int.ofNat 40), (441, Int.negSucc 3), (468, Int.ofNat 12), (482,
    Int.negSucc 11), (490, Int.negSucc 13), (695, Int.negSucc 11), (745, Int.ofNat 12), (752,
    Int.ofNat 12), (759, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (117,
    Int.ofNat 2), (391, Int.negSucc 23), (429, Int.ofNat 56), (441, Int.negSucc 3), (447,
    Int.negSucc 3), (468, Int.ofNat 16), (482, Int.negSucc 17), (490, Int.negSucc 17), (695,
    Int.negSucc 15), (745, Int.ofNat 16), (752, Int.ofNat 16), (759, Int.negSucc 15)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 2), (118, Int.ofNat 3), (385,
    Int.ofNat 64), (396, Int.negSucc 27), (433, Int.ofNat 52), (471, Int.ofNat 20), (479,
    Int.negSucc 3), (486, Int.negSucc 19), (497, Int.negSucc 39), (773, Int.negSucc 19)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (119,
    Int.negSucc 0), (385, Int.ofNat 16), (396, Int.negSucc 9), (433, Int.ofNat 12), (471,
    Int.ofNat 6), (486, Int.negSucc 3), (497, Int.negSucc 11), (773, Int.negSucc 5)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (380,
    Int.ofNat 16), (390, Int.negSucc 3), (421, Int.ofNat 12), (464, Int.ofNat 4), (475,
    Int.negSucc 7), (487, Int.negSucc 3), (509, Int.negSucc 1), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(399, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (404,
    Int.ofNat 8), (412, Int.negSucc 3), (454, Int.ofNat 6), (478, Int.ofNat 4), (485, Int.ofNat
    4), (504, Int.negSucc 1), (512, Int.negSucc 3), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(123, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(110, Int.ofNat 1), (120, Int.ofNat 2), (124,
    Int.negSucc 1), (380, Int.ofNat 6), (421, Int.ofNat 4), (464, Int.ofNat 1), (475, Int.negSucc
    1), (494, Int.negSucc 1), (509, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (125,
    Int.negSucc 1), (131, Int.ofNat 2), (385, Int.ofNat 6), (433, Int.ofNat 4), (471, Int.ofNat
    1), (479, Int.negSucc 1), (497, Int.negSucc 1), (508, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 4), (126, Int.negSucc 3), (130,
    Int.negSucc 1), (132, Int.ofNat 4), (404, Int.ofNat 6), (454, Int.ofNat 4), (478, Int.ofNat
    4), (493, Int.ofNat 4), (504, Int.negSucc 0), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(407, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (128,
    Int.ofNat 2), (391, Int.negSucc 23), (429, Int.ofNat 56), (441, Int.negSucc 3), (462,
    Int.negSucc 3), (468, Int.ofNat 18), (482, Int.negSucc 15), (490, Int.negSucc 17), (695,
    Int.negSucc 15), (745, Int.ofNat 16), (752, Int.ofNat 16), (759, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 5), (130, Int.ofNat 3), (404,
    Int.ofNat 32), (412, Int.negSucc 27), (454, Int.ofNat 26), (478, Int.ofNat 4), (485, Int.ofNat
    20), (504, Int.negSucc 9), (512, Int.negSucc 19), (780, Int.negSucc 19)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (385,
    Int.ofNat 40), (396, Int.negSucc 15), (433, Int.ofNat 32), (471, Int.ofNat 12), (479,
    Int.negSucc 1), (486, Int.negSucc 11), (497, Int.negSucc 23), (508, Int.negSucc 0), (773,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (404,
    Int.ofNat 10), (412, Int.negSucc 7), (454, Int.ofNat 8), (478, Int.ofNat 1), (485, Int.ofNat
    6), (493, Int.ofNat 1), (504, Int.negSucc 2), (512, Int.negSucc 5), (780, Int.negSucc 5)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (133,
    Int.ofNat 4), (391, Int.negSucc 23), (429, Int.ofNat 56), (441, Int.negSucc 7), (468,
    Int.ofNat 16), (482, Int.negSucc 15), (490, Int.negSucc 19), (695, Int.negSucc 15), (745,
    Int.ofNat 16), (752, Int.ofNat 16), (759, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.negSucc 3), (130, Int.ofNat 2), (134,
    Int.negSucc 0), (404, Int.ofNat 16), (412, Int.negSucc 19), (454, Int.ofNat 12), (485,
    Int.ofNat 8), (504, Int.negSucc 5), (512, Int.negSucc 11), (780, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.negSucc 0), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 0), (430, Int.ofNat 16), (442,
    Int.negSucc 15), (480, Int.ofNat 8), (516, Int.ofNat 8), (528, Int.negSucc 15), (766,
    Int.ofNat 8), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 1), (415, Int.ofNat 4), (465, Int.ofNat
    2), (540, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (425, Int.ofNat 4), (476, Int.ofNat
    4), (544, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 1), (139, Int.ofNat 2), (148,
    Int.ofNat 1), (430, Int.ofNat 96), (442, Int.negSucc 55), (443, Int.negSucc 7), (480,
    Int.ofNat 64), (488, Int.ofNat 32), (516, Int.ofNat 32), (520, Int.ofNat 8), (528, Int.negSucc
    63), (535, Int.negSucc 7), (547, Int.negSucc 23), (696, Int.negSucc 7), (709, Int.negSucc 7),
    (746, Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 40), (774,
    Int.ofNat 8), (781, Int.negSucc 7), (787, Int.negSucc 31)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 1), (415, Int.ofNat 3), (465, Int.ofNat
    2), (540, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 3), (472, Int.ofNat
    2), (539, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (148,
    Int.negSucc 2), (150, Int.ofNat 6), (151, Int.negSucc 1), (430, Int.ofNat 48), (442,
    Int.negSucc 7), (448, Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 16), (495,
    Int.ofNat 16), (516, Int.ofNat 8), (524, Int.ofNat 8), (528, Int.negSucc 15), (535,
    Int.negSucc 3), (547, Int.negSucc 7), (550, Int.negSucc 15), (766, Int.ofNat 8), (774,
    Int.ofNat 8), (787, Int.negSucc 7), (795, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.negSucc 0), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 4), (532,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.ofNat 2), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 2), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 12), (139, Int.negSucc 5), (148,
    Int.ofNat 5), (430, Int.ofNat 160), (442, Int.negSucc 23), (443, Int.negSucc 39), (480,
    Int.ofNat 112), (488, Int.ofNat 128), (516, Int.ofNat 16), (520, Int.ofNat 40), (528,
    Int.negSucc 31), (535, Int.negSucc 39), (547, Int.negSucc 87), (696, Int.negSucc 39), (709,
    Int.negSucc 39), (746, Int.ofNat 40), (753, Int.ofNat 40), (760, Int.negSucc 39), (766,
    Int.ofNat 56), (774, Int.ofNat 40), (781, Int.negSucc 39), (787, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 4), (472, Int.ofNat
    2), (539, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 15), (139, Int.negSucc 7), (148,
    Int.ofNat 2), (150, Int.ofNat 8), (151, Int.negSucc 3), (430, Int.ofNat 224), (442,
    Int.negSucc 23), (443, Int.negSucc 47), (448, Int.negSucc 23), (480, Int.ofNat 128), (488,
    Int.ofNat 160), (495, Int.ofNat 24), (516, Int.ofNat 16), (520, Int.ofNat 48), (524, Int.ofNat
    16), (528, Int.negSucc 31), (535, Int.negSucc 51), (547, Int.negSucc 103), (550, Int.negSucc
    31), (696, Int.negSucc 47), (709, Int.negSucc 47), (746, Int.ofNat 48), (753, Int.ofNat 48),
    (760, Int.negSucc 47), (766, Int.ofNat 64), (774, Int.ofNat 64), (781, Int.negSucc 47), (787,
    Int.negSucc 15), (795, Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 3), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (150, Int.ofNat 12), (151, Int.negSucc 7), (430, Int.ofNat 96), (443,
    Int.negSucc 7), (448, Int.negSucc 55), (480, Int.ofNat 16), (488, Int.ofNat 32), (495,
    Int.ofNat 40), (520, Int.ofNat 8), (524, Int.ofNat 32), (535, Int.negSucc 11), (547,
    Int.negSucc 15), (550, Int.negSucc 63), (696, Int.negSucc 7), (709, Int.negSucc 7), (746,
    Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat
    40), (781, Int.negSucc 7), (795, Int.negSucc 31)] },
  { denominator := Int.ofNat 2, terms := [(138, Int.ofNat 1), (425, Int.ofNat 3), (476, Int.ofNat
    4), (544, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

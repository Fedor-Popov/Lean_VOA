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
def actionData218 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 15), (468, Int.negSucc 3), (482, Int.ofNat 4), (490, Int.ofNat 6), (695, Int.ofNat
    4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (391, Int.ofNat 2), (429,
    Int.negSucc 9), (468, Int.negSucc 1), (482, Int.ofNat 3), (490, Int.ofNat 3), (695, Int.ofNat
    2), (745, Int.negSucc 1), (752, Int.negSucc 1), (759, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 15), (396,
    Int.ofNat 4), (433, Int.negSucc 13), (471, Int.negSucc 3), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 10), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 11), (396, Int.ofNat 4), (433, Int.negSucc 11), (471, Int.negSucc 3), (486,
    Int.ofNat 4), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (120,
    Int.ofNat 2), (380, Int.negSucc 7), (390, Int.ofNat 4), (421, Int.negSucc 9), (464,
    Int.negSucc 2), (475, Int.ofNat 8), (487, Int.ofNat 4), (509, Int.negSucc 0), (765, Int.ofNat
    4)] },
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
    Int.ofNat 10), (429, Int.negSucc 17), (462, Int.ofNat 4), (468, Int.negSucc 4), (482,
    Int.ofNat 6), (490, Int.ofNat 7), (695, Int.ofNat 6), (745, Int.negSucc 5), (752, Int.negSucc
    5), (759, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.ofNat 1), (404, Int.negSucc 5), (412,
    Int.ofNat 12), (454, Int.negSucc 0), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 3), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (131,
    Int.ofNat 2), (385, Int.negSucc 23), (396, Int.ofNat 8), (433, Int.negSucc 23), (471,
    Int.negSucc 6), (479, Int.ofNat 2), (486, Int.ofNat 8), (497, Int.ofNat 18), (508, Int.negSucc
    0), (773, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.ofNat 4), (404, Int.negSucc 11), (412,
    Int.ofNat 24), (478, Int.negSucc 3), (485, Int.negSucc 7), (493, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 6), (780, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (117,
    Int.negSucc 1), (128, Int.ofNat 2), (391, Int.ofNat 4), (429, Int.negSucc 19), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.ofNat 4), (468, Int.negSucc 1), (482,
    Int.ofNat 6), (490, Int.ofNat 10), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (134,
    Int.ofNat 2), (404, Int.negSucc 13), (412, Int.ofNat 28), (454, Int.negSucc 5), (485,
    Int.negSucc 3), (504, Int.ofNat 6), (512, Int.ofNat 12), (780, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 0), (540,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 2), (476,
    Int.negSucc 3), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 11), (442, Int.ofNat 4), (480, Int.negSucc 11), (488, Int.negSucc 3), (516,
    Int.negSucc 3), (528, Int.ofNat 8), (547, Int.ofNat 4), (766, Int.negSucc 3), (787, Int.ofNat
    4)] },
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
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (148, Int.negSucc 0), (430,
    Int.negSucc 35), (442, Int.ofNat 4), (443, Int.ofNat 8), (480, Int.negSucc 27), (488,
    Int.negSucc 27), (516, Int.negSucc 3), (520, Int.negSucc 7), (528, Int.ofNat 8), (535,
    Int.ofNat 8), (547, Int.ofNat 20), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc
    7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 11), (774, Int.negSucc 7),
    (781, Int.ofNat 8), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 3), (148, Int.ofNat 1), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 95), (442, Int.ofNat 8), (443, Int.ofNat
    16), (448, Int.ofNat 8), (480, Int.negSucc 55), (488, Int.negSucc 63), (495, Int.negSucc 15),
    (516, Int.negSucc 7), (520, Int.negSucc 15), (524, Int.negSucc 7), (528, Int.ofNat 16), (535,
    Int.ofNat 20), (547, Int.ofNat 40), (550, Int.ofNat 16), (696, Int.ofNat 16), (709, Int.ofNat
    16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23),
    (774, Int.negSucc 23), (781, Int.ofNat 16), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 3), (150, Int.negSucc 5), (151,
    Int.ofNat 2), (430, Int.negSucc 23), (448, Int.ofNat 8), (488, Int.negSucc 7), (495,
    Int.negSucc 15), (524, Int.negSucc 7), (535, Int.ofNat 4), (550, Int.ofNat 16), (774,
    Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (152, Int.ofNat 1), (425,
    Int.negSucc 1), (476, Int.negSucc 3), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (153,
    Int.ofNat 2), (430, Int.negSucc 7), (442, Int.ofNat 4), (480, Int.negSucc 9), (488,
    Int.negSucc 3), (510, Int.ofNat 1), (516, Int.negSucc 2), (528, Int.ofNat 8), (547, Int.ofNat
    4), (560, Int.negSucc 0), (766, Int.negSucc 3), (787, Int.ofNat 4)] },
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
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 9), (139, Int.ofNat 4), (148,
    Int.negSucc 4), (160, Int.ofNat 2), (164, Int.ofNat 1), (430, Int.negSucc 127), (442,
    Int.ofNat 8), (443, Int.ofNat 32), (463, Int.ofNat 24), (480, Int.negSucc 87), (488,
    Int.negSucc 95), (516, Int.negSucc 7), (520, Int.negSucc 27), (528, Int.ofNat 16), (535,
    Int.ofNat 32), (547, Int.ofNat 72), (556, Int.ofNat 4), (560, Int.ofNat 8), (696, Int.ofNat
    32), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31), (760, Int.ofNat 32),
    (766, Int.negSucc 39), (774, Int.negSucc 31), (781, Int.ofNat 40), (787, Int.ofNat 8), (802,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.ofNat 2), (451, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(143, Int.negSucc 3), (148, Int.ofNat 8), (150,
    Int.negSucc 15), (151, Int.ofNat 4), (162, Int.ofNat 4), (430, Int.negSucc 47), (448,
    Int.ofNat 16), (480, Int.negSucc 3), (488, Int.negSucc 15), (495, Int.negSucc 31), (510,
    Int.ofNat 2), (524, Int.negSucc 13), (528, Int.ofNat 4), (535, Int.ofNat 8), (550, Int.ofNat
    36), (556, Int.negSucc 0), (774, Int.negSucc 15), (795, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.negSucc 3), (157, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.negSucc 3), (430, Int.negSucc 55), (442, Int.ofNat 8), (443, Int.ofNat 8), (463,
    Int.ofNat 8), (480, Int.negSucc 47), (488, Int.negSucc 23), (495, Int.negSucc 7), (516,
    Int.negSucc 9), (520, Int.negSucc 3), (524, Int.negSucc 1), (528, Int.ofNat 20), (535,
    Int.ofNat 8), (547, Int.ofNat 24), (550, Int.ofNat 4), (556, Int.ofNat 1), (560, Int.ofNat 2),
    (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760,
    Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat
    8)] }
]

end VOA.DeligneAudit.D4Two.Certificate

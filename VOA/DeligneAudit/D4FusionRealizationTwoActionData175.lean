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
def actionData175 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(131, Int.negSucc 1), (385, Int.negSucc 15), (396,
    Int.ofNat 8), (433, Int.negSucc 15), (471, Int.negSucc 4), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 10), (508, Int.ofNat 1), (707, Int.negSucc 7), (713, Int.negSucc 1), (738,
    Int.ofNat 2), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 7), (66, Int.negSucc 3), (69,
    Int.negSucc 3), (73, Int.ofNat 4), (335, Int.negSucc 19), (361, Int.negSucc 3), (376,
    Int.ofNat 4), (387, Int.negSucc 15), (397, Int.negSucc 0), (402, Int.ofNat 2), (410, Int.ofNat
    12), (688, Int.negSucc 15), (701, Int.negSucc 19), (722, Int.negSucc 7), (725, Int.negSucc 3)]
    },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372,
    Int.negSucc 9), (403, Int.ofNat 6), (411, Int.negSucc 1), (426, Int.ofNat 4), (439,
    Int.negSucc 0), (445, Int.negSucc 0), (449, Int.negSucc 1), (456, Int.negSucc 1), (692,
    Int.negSucc 3), (723, Int.negSucc 0), (734, Int.negSucc 0), (758, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.negSucc 3), (404, Int.negSucc 15), (412,
    Int.ofNat 16), (454, Int.negSucc 15), (478, Int.negSucc 3), (485, Int.negSucc 7), (493,
    Int.negSucc 3), (504, Int.ofNat 5), (512, Int.ofNat 10), (706, Int.ofNat 16), (724,
    Int.negSucc 3), (735, Int.negSucc 3), (780, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 7), (391, Int.ofNat 8), (429, Int.negSucc
    19), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 1), (482,
    Int.ofNat 2), (490, Int.ofNat 6), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 1), (465,
    Int.negSucc 1), (540, Int.ofNat 2), (719, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 1), (476,
    Int.negSucc 3), (544, Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 11), (442, Int.ofNat 8), (480, Int.negSucc 11), (488, Int.negSucc 3), (516,
    Int.negSucc 3), (528, Int.ofNat 8), (547, Int.ofNat 4), (709, Int.ofNat 4), (741, Int.negSucc
    3), (766, Int.negSucc 3), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (403, Int.ofNat 2), (411, Int.ofNat 4), (426, Int.ofNat 4), (449, Int.negSucc 0), (456,
    Int.negSucc 0), (692, Int.ofNat 4), (723, Int.ofNat 4), (734, Int.ofNat 4), (758, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 5), (429, Int.ofNat 8), (441,
    Int.negSucc 1), (447, Int.negSucc 1), (468, Int.ofNat 2), (482, Int.negSucc 1), (490,
    Int.negSucc 1), (695, Int.negSucc 1), (745, Int.ofNat 2), (752, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 0), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (495, Int.negSucc 1), (528, Int.ofNat 2), (550, Int.ofNat 2), (709, Int.ofNat
    2), (729, Int.negSucc 1), (741, Int.negSucc 1), (760, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (437, Int.negSucc 1), (498,
    Int.negSucc 3), (532, Int.ofNat 2), (740, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (148, Int.negSucc 0), (430,
    Int.negSucc 35), (442, Int.ofNat 8), (443, Int.ofNat 16), (480, Int.negSucc 27), (488,
    Int.negSucc 27), (516, Int.negSucc 3), (520, Int.negSucc 7), (528, Int.ofNat 8), (535,
    Int.ofNat 8), (547, Int.ofNat 20), (696, Int.ofNat 16), (709, Int.ofNat 20), (741, Int.negSucc
    3), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 11),
    (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 1), (539, Int.ofNat 2), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 3), (148, Int.ofNat 1), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 95), (442, Int.ofNat 16), (443,
    Int.ofNat 32), (448, Int.ofNat 16), (480, Int.negSucc 55), (488, Int.negSucc 63), (495,
    Int.negSucc 15), (516, Int.negSucc 7), (520, Int.negSucc 15), (524, Int.negSucc 7), (528,
    Int.ofNat 16), (535, Int.ofNat 20), (547, Int.ofNat 40), (550, Int.ofNat 16), (696, Int.ofNat
    32), (709, Int.ofNat 48), (729, Int.negSucc 7), (741, Int.negSucc 7), (746, Int.negSucc 15),
    (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23), (774, Int.negSucc 23),
    (781, Int.ofNat 16), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (98, Int.negSucc 1), (102,
    Int.ofNat 2), (384, Int.negSucc 1), (395, Int.negSucc 1), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 1), (693, Int.ofNat 2), (712, Int.negSucc 1), (737, Int.ofNat
    2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 2), (429, Int.ofNat 4), (441,
    Int.negSucc 0), (462, Int.negSucc 0), (468, Int.ofNat 1), (482, Int.negSucc 0), (490,
    Int.negSucc 0), (695, Int.negSucc 0), (745, Int.ofNat 1), (759, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560, Int.ofNat 1), (709,
    Int.ofNat 2), (717, Int.ofNat 2), (741, Int.negSucc 1), (753, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 1), (458, Int.negSucc 0), (513,
    Int.negSucc 1), (531, Int.negSucc 1), (739, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 3), (148, Int.ofNat 1), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 95), (442, Int.ofNat 16), (443,
    Int.ofNat 32), (463, Int.ofNat 16), (480, Int.negSucc 55), (488, Int.negSucc 63), (510,
    Int.negSucc 7), (516, Int.negSucc 7), (520, Int.negSucc 19), (528, Int.ofNat 16), (535,
    Int.ofNat 16), (547, Int.ofNat 40), (556, Int.ofNat 4), (560, Int.ofNat 8), (696, Int.ofNat
    32), (709, Int.ofNat 48), (717, Int.ofNat 8), (741, Int.negSucc 7), (746, Int.negSucc 15),
    (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23), (774, Int.negSucc 15),
    (781, Int.ofNat 24), (787, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.negSucc 0), (451, Int.negSucc 0), (505,
    Int.negSucc 0), (543, Int.negSucc 1), (728, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 3), (82, Int.ofNat 1), (85, Int.negSucc
    5), (95, Int.negSucc 1), (101, Int.ofNat 4), (352, Int.negSucc 19), (379, Int.negSucc 3),
    (389, Int.negSucc 15), (413, Int.ofNat 2), (423, Int.ofNat 2), (428, Int.ofNat 4), (446,
    Int.ofNat 12), (694, Int.ofNat 8), (715, Int.negSucc 3), (726, Int.ofNat 16), (744,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.negSucc 19), (429, Int.ofNat 32), (441, Int.negSucc 1), (447, Int.negSucc 3), (462,
    Int.negSucc 1), (468, Int.ofNat 8), (482, Int.negSucc 9), (490, Int.negSucc 7), (695,
    Int.negSucc 11), (745, Int.ofNat 6), (752, Int.ofNat 8), (759, Int.negSucc 5)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 1), (150, Int.negSucc 1), (151,
    Int.ofNat 2), (162, Int.negSucc 3), (430, Int.negSucc 31), (448, Int.ofNat 16), (480,
    Int.negSucc 3), (488, Int.negSucc 7), (495, Int.negSucc 23), (510, Int.negSucc 1), (524,
    Int.negSucc 9), (528, Int.ofNat 4), (535, Int.ofNat 4), (550, Int.ofNat 20), (556, Int.ofNat
    1), (709, Int.ofNat 16), (717, Int.ofNat 4), (729, Int.negSucc 15), (741, Int.negSucc 3),
    (746, Int.negSucc 3), (760, Int.ofNat 4), (774, Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (139, Int.ofNat 10), (148,
    Int.negSucc 6), (150, Int.ofNat 8), (153, Int.negSucc 3), (157, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.negSucc 3), (163, Int.negSucc 7), (430, Int.negSucc 55), (442, Int.ofNat 24),
    (448, Int.ofNat 8), (463, Int.ofNat 8), (480, Int.negSucc 31), (488, Int.negSucc 23), (516,
    Int.negSucc 9), (520, Int.negSucc 3), (524, Int.negSucc 1), (528, Int.ofNat 20), (535,
    Int.ofNat 4), (547, Int.ofNat 16), (550, Int.ofNat 4), (556, Int.ofNat 1), (560, Int.ofNat 2),
    (696, Int.ofNat 4), (709, Int.ofNat 20), (741, Int.negSucc 7), (746, Int.negSucc 3), (753,
    Int.negSucc 3), (760, Int.ofNat 4), (766, Int.negSucc 15), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (470, Int.negSucc 1), (517,
    Int.negSucc 1), (541, Int.negSucc 1), (590, Int.ofNat 2), (720, Int.ofNat 2), (755,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (484, Int.negSucc 1), (529,
    Int.negSucc 3), (545, Int.negSucc 1), (593, Int.ofNat 2), (731, Int.ofNat 2), (762,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 6), (172, Int.ofNat 3), (481,
    Int.negSucc 27), (489, Int.negSucc 11), (500, Int.ofNat 24), (564, Int.negSucc 3), (578,
    Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 10), (767, Int.negSucc 3), (775, Int.negSucc
    3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (492,
    Int.negSucc 5), (501, Int.ofNat 4), (548, Int.negSucc 3), (567, Int.negSucc 1), (581,
    Int.ofNat 4), (742, Int.ofNat 4), (788, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(178, Int.negSucc 0), (492, Int.negSucc 1), (533,
    Int.negSucc 1), (551, Int.negSucc 3), (581, Int.ofNat 2), (742, Int.ofNat 4), (761,
    Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

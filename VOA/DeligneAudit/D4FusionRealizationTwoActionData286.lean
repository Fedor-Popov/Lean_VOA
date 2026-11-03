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
def actionData286 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (118, Int.negSucc 1), (119,
    Int.ofNat 1), (131, Int.ofNat 2), (385, Int.negSucc 3), (396, Int.ofNat 4), (433, Int.negSucc
    3), (471, Int.negSucc 1), (486, Int.ofNat 2), (497, Int.ofNat 4), (508, Int.negSucc 0), (773,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 8), (404, Int.ofNat 4), (412, Int.ofNat 4), (454, Int.ofNat
    8), (504, Int.negSucc 1), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 4), (417, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 1), (117, Int.ofNat 2), (128,
    Int.ofNat 2), (391, Int.ofNat 12), (429, Int.negSucc 11), (447, Int.ofNat 4), (462, Int.ofNat
    4), (468, Int.negSucc 3), (482, Int.ofNat 4), (490, Int.ofNat 4), (695, Int.ofNat 4), (745,
    Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 4), (450, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (404, Int.negSucc 3), (412, Int.ofNat 8), (454,
    Int.negSucc 3), (478, Int.ofNat 4), (485, Int.negSucc 7), (493, Int.ofNat 4), (504, Int.ofNat
    2), (512, Int.ofNat 2), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(457, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 8), (385, Int.ofNat 8), (396, Int.ofNat 4), (433, Int.ofNat
    16), (471, Int.ofNat 4), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (134, Int.ofNat 1), (404, Int.negSucc 3), (412, Int.ofNat
    12), (485, Int.negSucc 3), (493, Int.ofNat 4), (504, Int.ofNat 2), (512, Int.ofNat 2), (780,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 2), (153, Int.ofNat 4), (157, Int.negSucc 3), (430, Int.negSucc 7), (442, Int.ofNat
    8), (480, Int.negSucc 7), (488, Int.negSucc 3), (495, Int.ofNat 4), (510, Int.ofNat 2), (516,
    Int.negSucc 3), (528, Int.ofNat 8), (547, Int.ofNat 4), (550, Int.negSucc 3), (560,
    Int.negSucc 1), (766, Int.negSucc 3), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 2), (158, Int.negSucc 3), (498,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 4), (159, Int.negSucc 3), (513,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (160, Int.ofNat 4), (163, Int.negSucc 7), (430,
    Int.negSucc 23), (442, Int.ofNat 8), (448, Int.ofNat 8), (463, Int.ofNat 8), (488, Int.negSucc
    23), (495, Int.ofNat 8), (510, Int.ofNat 4), (520, Int.negSucc 7), (535, Int.ofNat 8), (547,
    Int.ofNat 8), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc
    7), (760, Int.ofNat 8), (766, Int.negSucc 7), (774, Int.negSucc 7), (781, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 2), (418, Int.ofNat 2), (472, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (143, Int.ofNat 2), (148,
    Int.negSucc 2), (150, Int.ofNat 2), (153, Int.ofNat 4), (157, Int.negSucc 3), (160, Int.ofNat
    2), (430, Int.negSucc 19), (442, Int.ofNat 8), (443, Int.ofNat 4), (448, Int.ofNat 4), (463,
    Int.ofNat 4), (480, Int.negSucc 15), (488, Int.negSucc 15), (495, Int.ofNat 8), (510,
    Int.ofNat 4), (516, Int.negSucc 3), (520, Int.negSucc 3), (528, Int.ofNat 8), (535, Int.ofNat
    4), (547, Int.ofNat 12), (550, Int.negSucc 3), (560, Int.negSucc 1), (696, Int.ofNat 4), (709,
    Int.ofNat 4), (746, Int.negSucc 3), (753, Int.negSucc 3), (760, Int.ofNat 4), (766,
    Int.negSucc 7), (774, Int.negSucc 3), (781, Int.ofNat 4), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 3), (158, Int.negSucc 3), (437,
    Int.ofNat 2), (498, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 2), (451, Int.ofNat 1), (505, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (159, Int.negSucc 3), (458,
    Int.ofNat 1), (513, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 11), (151, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.ofNat 8), (163, Int.negSucc 7), (430, Int.negSucc 39), (442, Int.ofNat 8), (448,
    Int.ofNat 24), (463, Int.ofNat 8), (488, Int.negSucc 31), (510, Int.ofNat 8), (520,
    Int.negSucc 7), (524, Int.negSucc 7), (535, Int.ofNat 12), (547, Int.ofNat 8), (550, Int.ofNat
    16), (556, Int.negSucc 1), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753,
    Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 7), (774, Int.negSucc 15), (781,
    Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 1), (158, Int.negSucc 1), (437,
    Int.ofNat 2), (498, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.negSucc 0), (158, Int.ofNat 2), (532,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (458, Int.ofNat 3), (513, Int.ofNat
    6)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 7), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 3), (160, Int.negSucc 3), (162,
    Int.ofNat 8), (163, Int.negSucc 7), (164, Int.ofNat 2), (430, Int.negSucc 39), (442, Int.ofNat
    8), (448, Int.ofNat 8), (463, Int.ofNat 24), (488, Int.negSucc 31), (495, Int.ofNat 16), (520,
    Int.negSucc 11), (524, Int.ofNat 4), (535, Int.ofNat 8), (547, Int.ofNat 8), (556, Int.ofNat
    4), (560, Int.ofNat 8), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753,
    Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 7), (774, Int.negSucc 7), (781,
    Int.ofNat 16), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 2), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.ofNat 3), (437, Int.ofNat 6), (498, Int.ofNat
    12)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 4), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 6), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 0), (172, Int.negSucc 0), (177,
    Int.ofNat 4), (185, Int.ofNat 8), (190, Int.negSucc 7), (481, Int.negSucc 23), (489,
    Int.negSucc 23), (496, Int.ofNat 8), (500, Int.ofNat 28), (511, Int.ofNat 4), (564,
    Int.negSucc 7), (578, Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 16), (767,
    Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 2), (173, Int.negSucc 1), (178,
    Int.ofNat 2), (186, Int.ofNat 4), (191, Int.negSucc 3), (492, Int.negSucc 7), (501, Int.ofNat
    8), (533, Int.ofNat 4), (548, Int.negSucc 7), (551, Int.ofNat 8), (561, Int.ofNat 4), (567,
    Int.negSucc 3), (581, Int.ofNat 8), (788, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 4), (473, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 2), (177, Int.ofNat 2), (185,
    Int.ofNat 4), (481, Int.negSucc 23), (489, Int.negSucc 11), (496, Int.ofNat 4), (500,
    Int.ofNat 20), (511, Int.ofNat 2), (564, Int.negSucc 3), (578, Int.ofNat 8), (596, Int.ofNat
    4), (710, Int.ofNat 8), (767, Int.negSucc 3), (775, Int.negSucc 3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(187, Int.ofNat 8), (506, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 2), (514, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(170, Int.negSucc 2), (180, Int.negSucc 6), (182,
    Int.ofNat 2), (192, Int.ofNat 3), (470, Int.negSucc 11), (502, Int.ofNat 8), (517, Int.negSucc
    3), (521, Int.negSucc 9), (525, Int.ofNat 2), (585, Int.ofNat 4), (590, Int.ofNat 8), (803,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 4), (181, Int.negSucc 8), (183,
    Int.ofNat 3), (193, Int.ofNat 2), (484, Int.negSucc 11), (503, Int.ofNat 8), (529, Int.negSucc
    7), (536, Int.negSucc 9), (557, Int.ofNat 1), (573, Int.negSucc 3), (593, Int.ofNat 8), (796,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (178,
    Int.ofNat 1), (186, Int.ofNat 2), (191, Int.negSucc 1), (492, Int.negSucc 1), (501, Int.ofNat
    4), (551, Int.ofNat 4), (561, Int.ofNat 2), (567, Int.negSucc 1), (581, Int.ofNat 4), (788,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.ofNat 11), (173, Int.negSucc 11), (178,
    Int.ofNat 9), (186, Int.ofNat 18), (191, Int.negSucc 11), (492, Int.negSucc 29), (501,
    Int.ofNat 30), (533, Int.ofNat 12), (548, Int.negSucc 35), (551, Int.ofNat 36), (561,
    Int.ofNat 18), (567, Int.negSucc 17), (581, Int.ofNat 36), (788, Int.negSucc 35)] },
  { denominator := Int.ofNat 2, terms := [(188, Int.ofNat 4), (507, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (186,
    Int.ofNat 2), (492, Int.negSucc 1), (501, Int.ofNat 4), (533, Int.negSucc 1), (551, Int.ofNat
    4), (561, Int.ofNat 2), (567, Int.negSucc 1), (581, Int.ofNat 6), (788, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.ofNat 1), (499, Int.ofNat 12)] },
  { denominator := Int.ofNat 4, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (178,
    Int.ofNat 1), (492, Int.negSucc 1), (501, Int.ofNat 4), (533, Int.negSucc 1), (551, Int.ofNat
    4), (561, Int.ofNat 2), (567, Int.negSucc 2), (581, Int.ofNat 4), (788, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(189, Int.ofNat 1), (514, Int.ofNat 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

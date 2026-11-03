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
def actionData410 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (115, Int.negSucc 0), (128,
    Int.ofNat 2), (391, Int.ofNat 16), (429, Int.negSucc 15), (441, Int.ofNat 4), (462, Int.ofNat
    4), (468, Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745,
    Int.negSucc 7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 14), (130, Int.ofNat 1), (404, Int.ofNat
    8), (412, Int.ofNat 4), (454, Int.ofNat 10), (512, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 2), (120, Int.ofNat 4), (124, Int.negSucc 3), (380, Int.negSucc 11), (390, Int.ofNat
    12), (421, Int.negSucc 11), (464, Int.negSucc 5), (475, Int.ofNat 8), (487, Int.ofNat 8),
    (494, Int.negSucc 3), (509, Int.negSucc 1), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 16), (429, Int.negSucc
    15), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 4), (490, Int.ofNat 6), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc
    7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (124, Int.negSucc 1), (421,
    Int.ofNat 2), (475, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 4), (385, Int.negSucc 11), (396, Int.ofNat 12), (433,
    Int.negSucc 11), (471, Int.negSucc 5), (479, Int.negSucc 3), (486, Int.ofNat 4), (497,
    Int.ofNat 12), (508, Int.negSucc 1), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.negSucc 3), (399, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 0), (132, Int.ofNat 4), (404, Int.ofNat 4), (412, Int.ofNat 4), (454, Int.ofNat
    8), (504, Int.negSucc 0), (512, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 2), (414, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(450, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (120, Int.ofNat 12), (380,
    Int.negSucc 3), (390, Int.ofNat 16), (464, Int.negSucc 1), (475, Int.ofNat 12), (487,
    Int.ofNat 4), (509, Int.negSucc 1), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 14), (130, Int.negSucc 0), (134,
    Int.ofNat 1), (404, Int.negSucc 1), (412, Int.ofNat 16), (478, Int.ofNat 4), (485, Int.negSucc
    3), (504, Int.ofNat 3), (512, Int.ofNat 2), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 10), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (404, Int.negSucc 3), (412, Int.ofNat 12), (454,
    Int.negSucc 3), (478, Int.ofNat 4), (485, Int.negSucc 7), (493, Int.ofNat 4), (504, Int.ofNat
    2), (512, Int.ofNat 4), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 1), (152, Int.ofNat 4), (425,
    Int.negSucc 1), (476, Int.negSucc 3), (544, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 3), (139, Int.negSucc 3), (153,
    Int.ofNat 8), (430, Int.negSucc 23), (442, Int.ofNat 24), (480, Int.negSucc 23), (488,
    Int.negSucc 7), (510, Int.ofNat 4), (516, Int.negSucc 11), (528, Int.ofNat 24), (547,
    Int.ofNat 8), (560, Int.negSucc 3), (766, Int.negSucc 15), (787, Int.ofNat 16), (824,
    Int.ofNat 8), (826, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 8), (451, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 4), (455, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 12), (458, Int.ofNat 6), (513, Int.ofNat
    12)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.ofNat 1), (476, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (415, Int.ofNat 2), (465, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 2), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (148, Int.negSucc 3), (153,
    Int.ofNat 16), (160, Int.ofNat 4), (430, Int.negSucc 79), (442, Int.ofNat 56), (443, Int.ofNat
    16), (463, Int.ofNat 8), (480, Int.negSucc 63), (488, Int.negSucc 47), (510, Int.ofNat 12),
    (516, Int.negSucc 23), (520, Int.negSucc 11), (528, Int.ofNat 48), (535, Int.ofNat 12), (547,
    Int.ofNat 40), (560, Int.negSucc 7), (696, Int.ofNat 20), (709, Int.ofNat 16), (746,
    Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 47), (774,
    Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 32), (824, Int.ofNat 24), (826,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(154, Int.ofNat 8), (161, Int.ofNat 2), (451, Int.ofNat
    3), (505, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (152, Int.negSucc 1), (425,
    Int.ofNat 1), (476, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 6), (139, Int.ofNat 10), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.ofNat 8), (160, Int.ofNat 4), (163, Int.negSucc
    7), (430, Int.negSucc 55), (442, Int.ofNat 32), (443, Int.ofNat 8), (448, Int.ofNat 8), (463,
    Int.ofNat 8), (480, Int.negSucc 39), (488, Int.negSucc 39), (495, Int.ofNat 8), (510,
    Int.ofNat 8), (516, Int.negSucc 11), (520, Int.negSucc 11), (528, Int.ofNat 24), (535,
    Int.ofNat 8), (547, Int.ofNat 32), (560, Int.negSucc 3), (696, Int.ofNat 20), (709, Int.ofNat
    16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 31),
    (774, Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 16), (824, Int.ofNat 16), (826,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 7), (150, Int.negSucc 13), (151,
    Int.ofNat 2), (157, Int.negSucc 7), (162, Int.ofNat 8), (430, Int.negSucc 23), (448, Int.ofNat
    24), (480, Int.ofNat 8), (488, Int.negSucc 7), (495, Int.negSucc 15), (510, Int.ofNat 4),
    (524, Int.negSucc 11), (528, Int.negSucc 7), (535, Int.ofNat 4), (550, Int.ofNat 24), (556,
    Int.negSucc 1), (774, Int.negSucc 15), (795, Int.ofNat 16), (824, Int.ofNat 8), (829,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.ofNat 6), (451, Int.ofNat 3), (505, Int.ofNat
    3)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 1), (425, Int.ofNat 1), (476, Int.ofNat
    1)] },
  { denominator := Int.ofNat 4, terms := [(154, Int.ofNat 4), (451, Int.ofNat 2), (505, Int.ofNat
    1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (148, Int.ofNat 4), (153,
    Int.ofNat 32), (160, Int.negSucc 11), (164, Int.ofNat 4), (430, Int.negSucc 127), (442,
    Int.ofNat 56), (443, Int.ofNat 16), (463, Int.ofNat 56), (480, Int.negSucc 47), (488,
    Int.negSucc 63), (510, Int.negSucc 3), (516, Int.negSucc 15), (520, Int.negSucc 19), (528,
    Int.ofNat 48), (535, Int.ofNat 12), (547, Int.ofNat 40), (556, Int.ofNat 12), (560, Int.ofNat
    16), (696, Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15),
    (760, Int.ofNat 16), (766, Int.negSucc 47), (774, Int.negSucc 15), (781, Int.ofNat 48), (787,
    Int.ofNat 32), (802, Int.ofNat 32), (824, Int.ofNat 40), (826, Int.negSucc 15), (832,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 2, terms := [(154, Int.ofNat 6), (451, Int.ofNat 1), (543,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 3), (184, Int.ofNat 8), (484,
    Int.negSucc 3), (529, Int.negSucc 7), (545, Int.negSucc 7), (593, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.ofNat 2), (466, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 12), (172, Int.ofNat 5), (185,
    Int.ofNat 8), (481, Int.negSucc 63), (489, Int.negSucc 31), (500, Int.ofNat 60), (511,
    Int.ofNat 4), (564, Int.negSucc 11), (578, Int.ofNat 24), (596, Int.ofNat 12), (710, Int.ofNat
    32), (767, Int.negSucc 15), (775, Int.negSucc 15), (782, Int.ofNat 16), (825, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 8), (173, Int.negSucc 5), (186,
    Int.ofNat 12), (492, Int.negSucc 35), (501, Int.ofNat 36), (533, Int.ofNat 12), (548,
    Int.negSucc 23), (561, Int.ofNat 12), (567, Int.negSucc 17), (581, Int.ofNat 36), (788,
    Int.negSucc 47), (827, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(187, Int.ofNat 4), (506, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(188, Int.ofNat 12), (507, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 8), (514, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (184, Int.ofNat 2), (529,
    Int.negSucc 1), (536, Int.ofNat 1), (545, Int.negSucc 1), (593, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (180, Int.negSucc 8), (192,
    Int.ofNat 4), (470, Int.negSucc 17), (502, Int.ofNat 12), (517, Int.negSucc 3), (521,
    Int.negSucc 13), (585, Int.ofNat 6), (590, Int.ofNat 12), (803, Int.ofNat 8), (833,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 6), (181, Int.negSucc 9), (183,
    Int.ofNat 3), (184, Int.ofNat 8), (193, Int.ofNat 2), (484, Int.negSucc 19), (503, Int.ofNat
    8), (529, Int.negSucc 15), (536, Int.negSucc 11), (545, Int.negSucc 11), (557, Int.ofNat 1),
    (573, Int.negSucc 5), (593, Int.ofNat 20), (796, Int.negSucc 7), (830, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 4), (181, Int.negSucc 8), (183,
    Int.ofNat 3), (193, Int.ofNat 2), (484, Int.negSucc 17), (503, Int.ofNat 12), (529,
    Int.negSucc 11), (536, Int.negSucc 11), (545, Int.negSucc 3), (557, Int.ofNat 1), (573,
    Int.negSucc 5), (593, Int.ofNat 16), (796, Int.negSucc 7), (830, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 34), (172, Int.ofNat 11), (177,
    Int.ofNat 8), (185, Int.ofNat 24), (190, Int.negSucc 15), (481, Int.negSucc 175), (489,
    Int.negSucc 95), (496, Int.ofNat 16), (500, Int.ofNat 164), (511, Int.ofNat 12), (564,
    Int.negSucc 35), (578, Int.ofNat 56), (596, Int.ofNat 36), (710, Int.ofNat 96), (767,
    Int.negSucc 47), (775, Int.negSucc 47), (782, Int.ofNat 48), (825, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(181, Int.ofNat 1), (184, Int.ofNat 4), (193,
    Int.negSucc 0), (484, Int.negSucc 0), (529, Int.negSucc 1), (536, Int.ofNat 1), (545,
    Int.negSucc 3), (573, Int.negSucc 0), (593, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(187, Int.ofNat 4), (506, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(194, Int.ofNat 1), (515, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] }
]

end VOA.DeligneAudit.D4Two.Certificate

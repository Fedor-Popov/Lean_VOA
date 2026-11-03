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
def actionData266 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 2), (437, Int.ofNat 4), (498, Int.ofNat
    8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(469, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (149, Int.ofNat 1), (418, Int.ofNat
    2), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (143, Int.ofNat 2), (148,
    Int.negSucc 1), (150, Int.ofNat 2), (430, Int.negSucc 19), (442, Int.ofNat 8), (443, Int.ofNat
    4), (448, Int.ofNat 4), (480, Int.negSucc 15), (488, Int.negSucc 15), (495, Int.ofNat 8),
    (516, Int.negSucc 3), (520, Int.negSucc 3), (528, Int.ofNat 8), (535, Int.ofNat 4), (547,
    Int.ofNat 12), (550, Int.negSucc 3), (696, Int.ofNat 4), (709, Int.ofNat 4), (746, Int.negSucc
    3), (753, Int.negSucc 3), (760, Int.ofNat 4), (766, Int.negSucc 7), (774, Int.negSucc 3),
    (781, Int.ofNat 4), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 3, terms := [(140, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 5), (437, Int.ofNat 10), (498, Int.ofNat
    20)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (418, Int.ofNat 1), (472, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 0), (539, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (143, Int.ofNat 2), (148,
    Int.ofNat 2), (150, Int.negSucc 5), (151, Int.ofNat 4), (430, Int.negSucc 43), (442, Int.ofNat
    8), (443, Int.ofNat 4), (448, Int.ofNat 20), (480, Int.negSucc 15), (488, Int.negSucc 23),
    (516, Int.negSucc 3), (520, Int.negSucc 3), (524, Int.negSucc 7), (528, Int.ofNat 8), (535,
    Int.ofNat 8), (547, Int.ofNat 12), (550, Int.ofNat 12), (696, Int.ofNat 4), (709, Int.ofNat
    4), (746, Int.negSucc 3), (753, Int.negSucc 3), (760, Int.ofNat 4), (766, Int.negSucc 7),
    (774, Int.negSucc 11), (781, Int.ofNat 4), (787, Int.ofNat 4), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (498, Int.ofNat
    6), (532, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 1), (483, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 7), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (163, Int.negSucc 7), (430, Int.negSucc 23), (442, Int.ofNat 8), (448, Int.ofNat 8), (463,
    Int.ofNat 8), (480, Int.negSucc 7), (488, Int.negSucc 15), (495, Int.ofNat 8), (516,
    Int.negSucc 3), (520, Int.negSucc 3), (535, Int.ofNat 8), (547, Int.ofNat 8), (560, Int.ofNat
    4), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760,
    Int.ofNat 8), (766, Int.negSucc 7), (774, Int.negSucc 7), (781, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(142, Int.ofNat 1), (149, Int.ofNat 3), (418, Int.ofNat
    4), (472, Int.ofNat 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (148, Int.ofNat 3), (150,
    Int.negSucc 3), (160, Int.negSucc 5), (162, Int.ofNat 8), (164, Int.ofNat 1), (430,
    Int.negSucc 55), (442, Int.ofNat 16), (443, Int.ofNat 8), (448, Int.ofNat 8), (463, Int.ofNat
    16), (480, Int.negSucc 31), (488, Int.negSucc 39), (495, Int.ofNat 24), (510, Int.negSucc 3),
    (516, Int.negSucc 7), (520, Int.negSucc 11), (524, Int.ofNat 4), (528, Int.ofNat 16), (535,
    Int.ofNat 8), (547, Int.ofNat 24), (550, Int.negSucc 7), (556, Int.ofNat 4), (560, Int.ofNat
    8), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760,
    Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 16), (787,
    Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.ofNat 3), (158, Int.ofNat 2), (437, Int.ofNat
    8), (498, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 0), (159, Int.ofNat 1), (531,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.ofNat 1), (158, Int.ofNat 2), (437, Int.ofNat
    4), (498, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (174, Int.ofNat 2), (470,
    Int.negSucc 1), (517, Int.negSucc 1), (541, Int.negSucc 3), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 2), (473, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 2), (474, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 3), (172, Int.ofNat 1), (177,
    Int.ofNat 2), (481, Int.negSucc 23), (489, Int.negSucc 11), (496, Int.ofNat 4), (500,
    Int.ofNat 20), (564, Int.negSucc 3), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat
    8), (767, Int.negSucc 3), (775, Int.negSucc 3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 2), (173, Int.negSucc 1), (178,
    Int.ofNat 2), (492, Int.negSucc 7), (501, Int.ofNat 8), (533, Int.ofNat 4), (548, Int.negSucc
    7), (551, Int.ofNat 8), (567, Int.negSucc 3), (581, Int.ofNat 8), (788, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 2), (499, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (174, Int.ofNat 1), (470,
    Int.negSucc 0), (517, Int.negSucc 1), (521, Int.ofNat 1), (541, Int.negSucc 1), (590,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (174, Int.ofNat 1), (180,
    Int.negSucc 2), (182, Int.ofNat 1), (192, Int.ofNat 1), (470, Int.negSucc 6), (502, Int.ofNat
    2), (517, Int.negSucc 2), (521, Int.negSucc 3), (525, Int.ofNat 1), (541, Int.negSucc 3),
    (585, Int.ofNat 2), (590, Int.ofNat 6), (803, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 3), (474, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 2), (181, Int.negSucc 6), (183,
    Int.ofNat 3), (484, Int.negSucc 13), (503, Int.ofNat 8), (529, Int.negSucc 7), (536,
    Int.negSucc 9), (573, Int.negSucc 3), (593, Int.ofNat 8), (796, Int.negSucc 3)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.ofNat 11), (173, Int.negSucc 11), (178,
    Int.ofNat 9), (492, Int.negSucc 35), (501, Int.ofNat 30), (533, Int.ofNat 12), (548,
    Int.negSucc 35), (551, Int.ofNat 36), (567, Int.negSucc 17), (581, Int.ofNat 36), (788,
    Int.negSucc 35)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (174, Int.ofNat 1), (182,
    Int.negSucc 0), (470, Int.negSucc 2), (517, Int.negSucc 1), (521, Int.ofNat 1), (541,
    Int.negSucc 3), (585, Int.ofNat 1), (590, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 2), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.negSucc 0), (474, Int.negSucc 0)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.ofNat 11), (173, Int.negSucc 11), (178,
    Int.ofNat 3), (492, Int.negSucc 47), (501, Int.ofNat 30), (548, Int.negSucc 35), (551,
    Int.ofNat 36), (567, Int.negSucc 17), (581, Int.ofNat 48), (788, Int.negSucc 35)] },
  { denominator := Int.ofNat 4, terms := [(170, Int.negSucc 3), (174, Int.ofNat 2), (180,
    Int.negSucc 4), (182, Int.ofNat 2), (192, Int.ofNat 2), (470, Int.negSucc 13), (502, Int.ofNat
    8), (517, Int.negSucc 7), (521, Int.negSucc 7), (525, Int.ofNat 2), (541, Int.negSucc 3),
    (585, Int.ofNat 4), (590, Int.ofNat 12), (803, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (178,
    Int.ofNat 1), (186, Int.negSucc 1), (191, Int.ofNat 2), (492, Int.negSucc 3), (501, Int.ofNat
    4), (533, Int.negSucc 1), (551, Int.ofNat 4), (561, Int.negSucc 1), (567, Int.negSucc 2),
    (581, Int.ofNat 4), (788, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(176, Int.ofNat 5), (474, Int.ofNat 5)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 11), (173, Int.negSucc 11), (178,
    Int.ofNat 9), (186, Int.negSucc 5), (191, Int.ofNat 6), (492, Int.negSucc 35), (501, Int.ofNat
    30), (533, Int.ofNat 6), (548, Int.negSucc 35), (551, Int.ofNat 36), (567, Int.negSucc 20),
    (581, Int.ofNat 36), (788, Int.negSucc 35)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (206, Int.ofNat 2), (518,
    Int.negSucc 5), (522, Int.negSucc 1), (542, Int.negSucc 3), (553, Int.ofNat 4), (565,
    Int.negSucc 5), (628, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.negSucc 1), (207, Int.ofNat 2), (523,
    Int.negSucc 1), (568, Int.ofNat 2), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 1), (201, Int.negSucc 3), (208,
    Int.ofNat 2), (217, Int.ofNat 4), (518, Int.negSucc 7), (522, Int.negSucc 11), (526, Int.ofNat
    2), (542, Int.negSucc 3), (553, Int.ofNat 8), (565, Int.negSucc 15), (618, Int.ofNat 8), (628,
    Int.ofNat 8), (721, Int.ofNat 4), (769, Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 2), (527, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(196, Int.ofNat 2), (203, Int.negSucc 9), (210,
    Int.ofNat 6), (530, Int.negSucc 31), (537, Int.negSucc 27), (554, Int.ofNat 16), (579,
    Int.negSucc 63), (605, Int.negSucc 7), (631, Int.ofNat 16), (732, Int.ofNat 8), (768,
    Int.ofNat 8), (784, Int.negSucc 7), (797, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.ofNat 6), (205, Int.negSucc 2), (211,
    Int.ofNat 2), (549, Int.negSucc 11), (552, Int.ofNat 4), (555, Int.ofNat 4), (597, Int.negSucc
    3), (608, Int.negSucc 3), (621, Int.ofNat 8), (743, Int.ofNat 4), (776, Int.ofNat 4), (783,
    Int.negSucc 3), (789, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(199, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(212, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(213, Int.negSucc 0), (519, Int.negSucc 1), (586,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(202, Int.negSucc 1), (207, Int.ofNat 2), (523,
    Int.negSucc 2), (568, Int.ofNat 1), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(202, Int.negSucc 3), (207, Int.ofNat 3), (523,
    Int.negSucc 3), (568, Int.ofNat 2), (591, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.negSucc 0), (538, Int.negSucc 0), (582,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(202, Int.negSucc 1), (207, Int.ofNat 1), (523,
    Int.negSucc 3), (568, Int.ofNat 1), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 3), (527, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(202, Int.negSucc 2), (207, Int.ofNat 3), (523,
    Int.negSucc 2), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.ofNat 3), (205, Int.negSucc 0), (211,
    Int.ofNat 2), (219, Int.negSucc 7), (221, Int.ofNat 8), (534, Int.negSucc 11), (549,
    Int.negSucc 11), (552, Int.ofNat 4), (555, Int.ofNat 12), (562, Int.negSucc 3), (597,
    Int.negSucc 3), (608, Int.negSucc 7), (621, Int.ofNat 8), (743, Int.ofNat 4), (776, Int.ofNat
    4), (783, Int.negSucc 3), (789, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(231, Int.negSucc 0), (572, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(222, Int.ofNat 3), (229, Int.negSucc 9), (232,
    Int.negSucc 5), (236, Int.ofNat 6), (240, Int.ofNat 8), (563, Int.negSucc 3), (570,
    Int.negSucc 1), (575, Int.negSucc 7), (587, Int.negSucc 1), (606, Int.negSucc 15), (619,
    Int.negSucc 7), (654, Int.ofNat 8), (750, Int.ofNat 4), (770, Int.ofNat 4), (799, Int.negSucc
    3), (806, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(224, Int.ofNat 1), (233, Int.negSucc 3), (237,
    Int.ofNat 4), (569, Int.ofNat 2), (576, Int.negSucc 3), (592, Int.negSucc 7), (609, Int.ofNat
    4), (629, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] }
]

end VOA.DeligneAudit.D4Two.Certificate

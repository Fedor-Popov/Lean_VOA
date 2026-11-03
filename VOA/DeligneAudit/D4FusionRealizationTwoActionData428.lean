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
def actionData428 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (117,
    Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 15), (429, Int.ofNat 28), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.ofNat 8), (482,
    Int.negSucc 5), (490, Int.negSucc 7), (695, Int.negSucc 11), (745, Int.ofNat 8), (752,
    Int.ofNat 8), (759, Int.negSucc 7), (823, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 7), (126, Int.ofNat 6), (130,
    Int.ofNat 4), (132, Int.negSucc 3), (404, Int.ofNat 9), (412, Int.negSucc 11), (454, Int.ofNat
    8), (478, Int.negSucc 3), (485, Int.ofNat 8), (493, Int.negSucc 3), (504, Int.negSucc 2),
    (512, Int.negSucc 5), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 2), (415, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 4), (425, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (143,
    Int.negSucc 1), (153, Int.negSucc 3), (157, Int.ofNat 4), (430, Int.ofNat 16), (442,
    Int.negSucc 11), (480, Int.ofNat 16), (488, Int.ofNat 8), (495, Int.negSucc 3), (510,
    Int.negSucc 1), (516, Int.ofNat 6), (528, Int.negSucc 11), (547, Int.negSucc 7), (550,
    Int.ofNat 4), (560, Int.ofNat 2), (766, Int.ofNat 8), (787, Int.negSucc 7), (824, Int.negSucc
    3), (826, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 4), (418, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(157, Int.ofNat 4), (430, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 4), (437, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 8), (451, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(159, Int.ofNat 4), (458, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 9), (139, Int.negSucc 11), (143,
    Int.negSucc 1), (148, Int.ofNat 6), (150, Int.negSucc 3), (153, Int.negSucc 3), (157,
    Int.ofNat 4), (160, Int.negSucc 3), (163, Int.ofNat 8), (430, Int.ofNat 56), (442, Int.negSucc
    19), (443, Int.negSucc 7), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 32),
    (488, Int.ofNat 48), (495, Int.negSucc 11), (510, Int.negSucc 5), (516, Int.ofNat 6), (520,
    Int.ofNat 12), (528, Int.negSucc 11), (535, Int.negSucc 11), (547, Int.negSucc 31), (550,
    Int.ofNat 4), (560, Int.ofNat 2), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 24), (774,
    Int.ofNat 16), (781, Int.negSucc 15), (787, Int.negSucc 7), (824, Int.negSucc 11), (826,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 9), (139, Int.negSucc 11), (143,
    Int.negSucc 1), (148, Int.ofNat 1), (150, Int.ofNat 6), (151, Int.negSucc 1), (153,
    Int.negSucc 3), (157, Int.ofNat 8), (160, Int.negSucc 3), (162, Int.negSucc 3), (163,
    Int.ofNat 8), (430, Int.ofNat 72), (442, Int.negSucc 19), (443, Int.negSucc 7), (448,
    Int.negSucc 19), (463, Int.negSucc 7), (480, Int.ofNat 28), (488, Int.ofNat 56), (495,
    Int.negSucc 3), (510, Int.negSucc 7), (516, Int.ofNat 6), (520, Int.ofNat 12), (524, Int.ofNat
    6), (528, Int.negSucc 7), (535, Int.negSucc 15), (547, Int.negSucc 31), (550, Int.negSucc 7),
    (556, Int.ofNat 1), (560, Int.ofNat 2), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 24), (774,
    Int.ofNat 24), (781, Int.negSucc 15), (787, Int.negSucc 7), (795, Int.negSucc 7), (824,
    Int.negSucc 15), (826, Int.ofNat 4), (829, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 9), (139, Int.negSucc 11), (148,
    Int.ofNat 1), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat 2), (162, Int.negSucc
    3), (163, Int.ofNat 8), (164, Int.negSucc 0), (430, Int.ofNat 72), (442, Int.negSucc 19),
    (443, Int.negSucc 7), (448, Int.negSucc 7), (463, Int.negSucc 19), (480, Int.ofNat 28), (488,
    Int.ofNat 56), (495, Int.negSucc 15), (510, Int.negSucc 1), (516, Int.ofNat 4), (520,
    Int.ofNat 16), (524, Int.negSucc 1), (528, Int.negSucc 11), (535, Int.negSucc 11), (547,
    Int.negSucc 31), (550, Int.ofNat 4), (556, Int.negSucc 2), (560, Int.negSucc 3), (696,
    Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753, Int.ofNat 16), (760,
    Int.negSucc 15), (766, Int.ofNat 24), (774, Int.ofNat 16), (781, Int.negSucc 23), (787,
    Int.negSucc 7), (802, Int.negSucc 7), (824, Int.negSucc 15), (826, Int.ofNat 4), (832,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 4), (467, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(174, Int.ofNat 2), (470, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(184, Int.ofNat 4), (484, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 11), (172, Int.negSucc 2), (177,
    Int.negSucc 3), (185, Int.negSucc 7), (190, Int.ofNat 8), (481, Int.ofNat 64), (489, Int.ofNat
    40), (496, Int.negSucc 7), (500, Int.negSucc 59), (511, Int.negSucc 3), (564, Int.ofNat 12),
    (578, Int.negSucc 23), (596, Int.negSucc 11), (710, Int.negSucc 31), (767, Int.ofNat 16),
    (775, Int.ofNat 16), (782, Int.negSucc 15), (825, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 3), (173, Int.ofNat 4), (178,
    Int.negSucc 1), (186, Int.negSucc 3), (191, Int.ofNat 4), (492, Int.ofNat 16), (501,
    Int.negSucc 11), (533, Int.negSucc 7), (548, Int.ofNat 16), (551, Int.negSucc 7), (561,
    Int.negSucc 3), (567, Int.ofNat 6), (581, Int.negSucc 11), (788, Int.ofNat 16), (827,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 4), (474, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(191, Int.ofNat 4), (492, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(188, Int.ofNat 8), (507, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (174, Int.ofNat 1), (180, Int.ofNat
    5), (182, Int.negSucc 0), (192, Int.negSucc 1), (470, Int.ofNat 10), (502, Int.negSucc 5),
    (517, Int.ofNat 2), (521, Int.ofNat 8), (525, Int.negSucc 0), (585, Int.negSucc 2), (590,
    Int.negSucc 5), (803, Int.negSucc 3), (833, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 4), (181, Int.ofNat 12), (183,
    Int.negSucc 3), (184, Int.ofNat 4), (193, Int.negSucc 1), (484, Int.ofNat 20), (503,
    Int.negSucc 11), (529, Int.ofNat 8), (536, Int.ofNat 16), (557, Int.negSucc 0), (573,
    Int.ofNat 6), (593, Int.negSucc 11), (796, Int.ofNat 8), (830, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(200, Int.ofNat 4), (519, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 1), (201, Int.ofNat 6), (206,
    Int.ofNat 2), (208, Int.negSucc 1), (217, Int.negSucc 7), (518, Int.ofNat 10), (522, Int.ofNat
    22), (526, Int.negSucc 1), (553, Int.negSucc 11), (565, Int.ofNat 24), (618, Int.negSucc 11),
    (628, Int.negSucc 11), (721, Int.negSucc 7), (769, Int.ofNat 8), (777, Int.ofNat 8), (804,
    Int.negSucc 7), (834, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(207, Int.ofNat 2), (523, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 1), (203, Int.ofNat 8), (210,
    Int.negSucc 3), (215, Int.ofNat 4), (218, Int.negSucc 3), (530, Int.ofNat 20), (537, Int.ofNat
    22), (554, Int.negSucc 11), (558, Int.negSucc 0), (579, Int.ofNat 48), (605, Int.ofNat 6),
    (631, Int.negSucc 11), (732, Int.negSucc 7), (768, Int.negSucc 7), (784, Int.ofNat 8), (797,
    Int.ofNat 8), (831, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(216, Int.ofNat 4), (538, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.negSucc 18), (205, Int.ofNat 9), (211,
    Int.negSucc 3), (219, Int.negSucc 7), (221, Int.ofNat 8), (534, Int.negSucc 7), (549,
    Int.ofNat 40), (552, Int.negSucc 7), (555, Int.negSucc 11), (562, Int.negSucc 3), (597,
    Int.ofNat 12), (608, Int.ofNat 12), (621, Int.negSucc 23), (743, Int.negSucc 15), (776,
    Int.negSucc 15), (783, Int.ofNat 16), (789, Int.ofNat 16), (828, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(222, Int.negSucc 9), (229, Int.ofNat 36), (232,
    Int.ofNat 16), (236, Int.negSucc 15), (240, Int.negSucc 31), (563, Int.ofNat 8), (570,
    Int.ofNat 10), (575, Int.ofNat 24), (606, Int.ofNat 48), (619, Int.ofNat 24), (654,
    Int.negSucc 23), (750, Int.negSucc 15), (770, Int.negSucc 15), (799, Int.ofNat 16), (806,
    Int.ofNat 16), (837, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(230, Int.ofNat 4), (571, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(224, Int.negSucc 12), (233, Int.ofNat 24), (237,
    Int.ofNat 4), (238, Int.negSucc 3), (242, Int.negSucc 15), (569, Int.negSucc 21), (576,
    Int.ofNat 44), (577, Int.negSucc 3), (629, Int.ofNat 24), (648, Int.negSucc 23), (757,
    Int.negSucc 15), (778, Int.negSucc 15), (791, Int.ofNat 16), (805, Int.ofNat 16), (836,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(226, Int.negSucc 12), (235, Int.ofNat 28), (239,
    Int.negSucc 7), (241, Int.ofNat 8), (243, Int.negSucc 7), (583, Int.negSucc 43), (589,
    Int.ofNat 44), (602, Int.negSucc 1), (632, Int.ofNat 24), (639, Int.ofNat 12), (764,
    Int.negSucc 15), (785, Int.negSucc 15), (790, Int.negSucc 15), (798, Int.negSucc 15), (835,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(245, Int.negSucc 18), (256, Int.ofNat 36), (258,
    Int.ofNat 28), (260, Int.negSucc 15), (262, Int.negSucc 31), (604, Int.negSucc 33), (614,
    Int.ofNat 10), (616, Int.ofNat 24), (634, Int.ofNat 24), (649, Int.ofNat 24), (655, Int.ofNat
    24), (772, Int.negSucc 31), (792, Int.negSucc 15), (800, Int.negSucc 15), (807, Int.negSucc
    15), (838, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

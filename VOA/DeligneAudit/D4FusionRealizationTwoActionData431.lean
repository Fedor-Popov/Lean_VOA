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
def actionData431 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (403, Int.ofNat 2), (411, Int.ofNat 4), (426, Int.ofNat 4), (449, Int.negSucc 0), (456,
    Int.negSucc 0), (692, Int.ofNat 4), (723, Int.ofNat 4), (734, Int.ofNat 4), (758, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 9), (429, Int.ofNat 12), (441,
    Int.negSucc 1), (447, Int.negSucc 1), (468, Int.ofNat 4), (482, Int.negSucc 3), (490,
    Int.negSucc 3), (695, Int.negSucc 9), (745, Int.ofNat 6), (752, Int.ofNat 6), (759,
    Int.negSucc 3), (823, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 0), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (495, Int.negSucc 1), (528, Int.ofNat 2), (550, Int.ofNat 2), (709, Int.ofNat
    2), (729, Int.negSucc 1), (741, Int.negSucc 1), (760, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (437, Int.negSucc 1), (498,
    Int.negSucc 3), (532, Int.ofNat 2), (740, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 3), (148, Int.negSucc 0), (430,
    Int.negSucc 59), (442, Int.ofNat 16), (443, Int.ofNat 32), (480, Int.negSucc 51), (488,
    Int.negSucc 43), (516, Int.negSucc 7), (520, Int.negSucc 15), (528, Int.ofNat 16), (535,
    Int.ofNat 16), (547, Int.ofNat 36), (696, Int.ofNat 40), (709, Int.ofNat 36), (741,
    Int.negSucc 3), (746, Int.negSucc 23), (753, Int.negSucc 23), (760, Int.ofNat 24), (766,
    Int.negSucc 35), (774, Int.negSucc 23), (781, Int.ofNat 24), (787, Int.ofNat 12), (824,
    Int.ofNat 24), (826, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 1), (539, Int.ofNat 2), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (148, Int.ofNat 1), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 159), (442, Int.ofNat 32), (443,
    Int.ofNat 64), (448, Int.ofNat 32), (480, Int.negSucc 103), (488, Int.negSucc 95), (495,
    Int.negSucc 31), (516, Int.negSucc 15), (520, Int.negSucc 31), (524, Int.negSucc 15), (528,
    Int.ofNat 32), (535, Int.ofNat 36), (547, Int.ofNat 72), (550, Int.ofNat 32), (696, Int.ofNat
    80), (709, Int.ofNat 80), (729, Int.negSucc 7), (741, Int.negSucc 7), (746, Int.negSucc 47),
    (753, Int.negSucc 47), (760, Int.ofNat 48), (766, Int.negSucc 71), (774, Int.negSucc 71),
    (781, Int.ofNat 48), (787, Int.ofNat 24), (795, Int.ofNat 24), (824, Int.ofNat 64), (826,
    Int.negSucc 15), (829, Int.negSucc 15)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (98, Int.negSucc 1), (102,
    Int.ofNat 2), (384, Int.negSucc 1), (395, Int.negSucc 1), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 1), (693, Int.ofNat 2), (712, Int.negSucc 1), (737, Int.ofNat
    2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 4), (429, Int.ofNat 6), (441,
    Int.negSucc 0), (462, Int.negSucc 0), (468, Int.ofNat 2), (482, Int.negSucc 1), (490,
    Int.negSucc 1), (695, Int.negSucc 4), (745, Int.ofNat 3), (752, Int.ofNat 2), (759,
    Int.negSucc 2), (823, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560, Int.ofNat 1), (709,
    Int.ofNat 2), (717, Int.ofNat 2), (741, Int.negSucc 1), (753, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 1), (458, Int.negSucc 0), (513,
    Int.negSucc 1), (531, Int.negSucc 1), (739, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (148, Int.ofNat 1), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 159), (442, Int.ofNat 32), (443,
    Int.ofNat 64), (463, Int.ofNat 32), (480, Int.negSucc 103), (488, Int.negSucc 95), (510,
    Int.negSucc 15), (516, Int.negSucc 15), (520, Int.negSucc 35), (528, Int.ofNat 32), (535,
    Int.ofNat 32), (547, Int.ofNat 72), (556, Int.ofNat 8), (560, Int.ofNat 16), (696, Int.ofNat
    80), (709, Int.ofNat 80), (717, Int.ofNat 8), (741, Int.negSucc 7), (746, Int.negSucc 47),
    (753, Int.negSucc 47), (760, Int.ofNat 48), (766, Int.negSucc 71), (774, Int.negSucc 47),
    (781, Int.ofNat 72), (787, Int.ofNat 24), (802, Int.ofNat 24), (824, Int.ofNat 64), (826,
    Int.negSucc 15), (832, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.negSucc 0), (451, Int.negSucc 0), (505,
    Int.negSucc 0), (543, Int.negSucc 1), (728, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 3), (82, Int.ofNat 1), (85, Int.negSucc
    5), (95, Int.negSucc 1), (101, Int.ofNat 4), (352, Int.negSucc 27), (379, Int.ofNat 4), (389,
    Int.negSucc 15), (413, Int.ofNat 6), (423, Int.negSucc 1), (428, Int.ofNat 4), (446, Int.ofNat
    12), (694, Int.ofNat 16), (715, Int.negSucc 3), (726, Int.ofNat 16), (744, Int.negSucc 15),
    (821, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.negSucc 35), (429, Int.ofNat 48), (441, Int.negSucc 1), (447, Int.negSucc 3), (462,
    Int.negSucc 1), (468, Int.ofNat 16), (482, Int.negSucc 17), (490, Int.negSucc 15), (695,
    Int.negSucc 43), (745, Int.ofNat 22), (752, Int.ofNat 24), (759, Int.negSucc 21), (823,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 1), (150, Int.negSucc 1), (151,
    Int.ofNat 2), (162, Int.negSucc 3), (430, Int.negSucc 47), (448, Int.ofNat 32), (480,
    Int.negSucc 3), (488, Int.negSucc 7), (495, Int.negSucc 39), (510, Int.negSucc 1), (524,
    Int.negSucc 17), (528, Int.ofNat 4), (535, Int.ofNat 4), (550, Int.ofNat 36), (556, Int.ofNat
    1), (709, Int.ofNat 16), (717, Int.ofNat 4), (729, Int.negSucc 15), (741, Int.negSucc 3),
    (746, Int.negSucc 3), (760, Int.ofNat 4), (774, Int.negSucc 23), (795, Int.ofNat 24), (824,
    Int.ofNat 16), (829, Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 7), (139, Int.ofNat 10), (148,
    Int.negSucc 6), (150, Int.ofNat 8), (153, Int.negSucc 3), (157, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.negSucc 3), (163, Int.negSucc 7), (430, Int.negSucc 87), (442, Int.ofNat 40),
    (443, Int.ofNat 16), (448, Int.ofNat 8), (463, Int.ofNat 8), (480, Int.negSucc 63), (488,
    Int.negSucc 39), (516, Int.negSucc 17), (520, Int.negSucc 11), (524, Int.negSucc 1), (528,
    Int.ofNat 36), (535, Int.ofNat 12), (547, Int.ofNat 32), (550, Int.ofNat 4), (556, Int.ofNat
    1), (560, Int.ofNat 2), (696, Int.ofNat 24), (709, Int.ofNat 36), (741, Int.negSucc 7), (746,
    Int.negSucc 19), (753, Int.negSucc 19), (760, Int.ofNat 20), (766, Int.negSucc 47), (774,
    Int.negSucc 23), (781, Int.ofNat 24), (787, Int.ofNat 24), (824, Int.ofNat 40), (826,
    Int.negSucc 19), (829, Int.negSucc 3), (832, Int.negSucc 7), (840, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (470, Int.negSucc 1), (517,
    Int.negSucc 1), (541, Int.negSucc 1), (590, Int.ofNat 2), (720, Int.ofNat 2), (755,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (484, Int.negSucc 1), (529,
    Int.negSucc 3), (545, Int.negSucc 1), (593, Int.ofNat 2), (731, Int.ofNat 2), (762,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 13), (172, Int.ofNat 6), (481,
    Int.negSucc 51), (489, Int.negSucc 19), (500, Int.ofNat 44), (564, Int.negSucc 7), (578,
    Int.ofNat 16), (596, Int.ofNat 8), (710, Int.ofNat 26), (767, Int.negSucc 11), (775,
    Int.negSucc 11), (782, Int.ofNat 12), (825, Int.ofNat 4)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.ofNat 4), (173, Int.negSucc 2), (492,
    Int.negSucc 29), (501, Int.ofNat 24), (548, Int.negSucc 11), (567, Int.negSucc 11), (581,
    Int.ofNat 24), (742, Int.ofNat 12), (788, Int.negSucc 35), (827, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(178, Int.negSucc 0), (492, Int.negSucc 1), (533,
    Int.negSucc 1), (551, Int.negSucc 3), (581, Int.ofNat 2), (742, Int.ofNat 4), (761,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 3), (180, Int.negSucc 8), (192,
    Int.ofNat 4), (470, Int.negSucc 25), (502, Int.ofNat 16), (517, Int.negSucc 7), (521,
    Int.negSucc 15), (541, Int.negSucc 3), (585, Int.ofNat 8), (590, Int.ofNat 16), (720,
    Int.ofNat 4), (803, Int.ofNat 12), (833, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 3), (181, Int.negSucc 8), (183,
    Int.ofNat 4), (484, Int.negSucc 25), (503, Int.ofNat 16), (529, Int.negSucc 15), (536,
    Int.negSucc 15), (545, Int.negSucc 3), (573, Int.negSucc 7), (593, Int.ofNat 16), (731,
    Int.ofNat 4), (796, Int.negSucc 11), (830, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(182, Int.negSucc 0), (470, Int.negSucc 1), (525,
    Int.negSucc 0), (541, Int.negSucc 1), (585, Int.ofNat 1), (720, Int.ofNat 2), (748,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(186, Int.negSucc 1), (492, Int.negSucc 1), (533,
    Int.negSucc 1), (561, Int.negSucc 1), (567, Int.negSucc 0), (742, Int.ofNat 4), (754,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 7), (181, Int.negSucc 15), (183,
    Int.ofNat 8), (193, Int.negSucc 1), (484, Int.negSucc 59), (503, Int.ofNat 32), (529,
    Int.negSucc 39), (536, Int.negSucc 31), (545, Int.negSucc 15), (557, Int.negSucc 0), (573,
    Int.negSucc 17), (593, Int.ofNat 36), (731, Int.ofNat 16), (747, Int.ofNat 4), (762,
    Int.negSucc 3), (796, Int.negSucc 23), (830, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(201, Int.negSucc 1), (217, Int.ofNat 4), (518,
    Int.negSucc 8), (522, Int.negSucc 11), (542, Int.negSucc 1), (553, Int.ofNat 10), (565,
    Int.negSucc 15), (618, Int.ofNat 8), (628, Int.ofNat 8), (721, Int.ofNat 7), (769, Int.negSucc
    5), (777, Int.negSucc 5), (804, Int.ofNat 6), (834, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.negSucc 0), (523, Int.negSucc 1), (591,
    Int.negSucc 3), (756, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(203, Int.negSucc 1), (210, Int.ofNat 2), (530,
    Int.negSucc 17), (537, Int.negSucc 11), (546, Int.negSucc 1), (554, Int.ofNat 10), (579,
    Int.negSucc 31), (605, Int.negSucc 3), (631, Int.ofNat 8), (732, Int.ofNat 7), (768, Int.ofNat
    6), (784, Int.negSucc 5), (797, Int.negSucc 5), (831, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.negSucc 0), (538, Int.negSucc 1), (594,
    Int.negSucc 3), (763, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

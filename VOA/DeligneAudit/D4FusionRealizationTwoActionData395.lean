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
def actionData395 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (115, Int.negSucc 2), (117,
    Int.ofNat 4), (391, Int.ofNat 28), (429, Int.negSucc 31), (441, Int.ofNat 2), (447, Int.ofNat
    8), (462, Int.ofNat 2), (468, Int.negSucc 11), (482, Int.ofNat 12), (490, Int.ofNat 12), (695,
    Int.ofNat 24), (745, Int.negSucc 15), (752, Int.negSucc 15), (759, Int.ofNat 16), (823,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 1), (141, Int.ofNat 2), (415,
    Int.negSucc 1), (465, Int.negSucc 1), (540, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 2), (418, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 2), (430, Int.negSucc 11), (442, Int.ofNat 12), (480, Int.negSucc 11), (488,
    Int.negSucc 3), (495, Int.ofNat 4), (516, Int.negSucc 5), (528, Int.ofNat 12), (547, Int.ofNat
    4), (550, Int.negSucc 3), (766, Int.negSucc 7), (787, Int.ofNat 8), (824, Int.ofNat 4), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 2), (434, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 2), (437, Int.ofNat 4), (498, Int.ofNat
    8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(469, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (149, Int.ofNat 1), (418, Int.ofNat
    2), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (143, Int.ofNat 4), (148,
    Int.negSucc 3), (150, Int.ofNat 4), (430, Int.negSucc 55), (442, Int.ofNat 24), (443,
    Int.ofNat 16), (448, Int.ofNat 8), (480, Int.negSucc 47), (488, Int.negSucc 39), (495,
    Int.ofNat 16), (516, Int.negSucc 11), (520, Int.negSucc 11), (528, Int.ofNat 24), (535,
    Int.ofNat 12), (547, Int.ofNat 32), (550, Int.negSucc 7), (696, Int.ofNat 20), (709, Int.ofNat
    16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 31),
    (774, Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 16), (824, Int.ofNat 16), (826,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 3, terms := [(140, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 5), (437, Int.ofNat 10), (498, Int.ofNat
    20)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (418, Int.ofNat 1), (472, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 0), (539, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (143, Int.ofNat 4), (148,
    Int.ofNat 4), (150, Int.negSucc 11), (151, Int.ofNat 8), (430, Int.negSucc 119), (442,
    Int.ofNat 24), (443, Int.ofNat 16), (448, Int.ofNat 56), (480, Int.negSucc 47), (488,
    Int.negSucc 55), (495, Int.negSucc 15), (516, Int.negSucc 11), (520, Int.negSucc 11), (524,
    Int.negSucc 23), (528, Int.ofNat 24), (535, Int.ofNat 20), (547, Int.ofNat 32), (550,
    Int.ofNat 40), (696, Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753,
    Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 31), (774, Int.negSucc 47), (781,
    Int.ofNat 16), (787, Int.ofNat 16), (795, Int.ofNat 32), (824, Int.ofNat 32), (826,
    Int.negSucc 7), (829, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (498, Int.ofNat
    6), (532, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 1), (483, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 8), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (163, Int.negSucc 7), (430, Int.negSucc 31), (442, Int.ofNat 8), (443, Int.ofNat 8), (448,
    Int.ofNat 8), (463, Int.ofNat 8), (480, Int.negSucc 15), (488, Int.negSucc 23), (495,
    Int.ofNat 8), (516, Int.negSucc 3), (520, Int.negSucc 7), (535, Int.ofNat 12), (547, Int.ofNat
    16), (560, Int.ofNat 4), (696, Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15),
    (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 15), (774, Int.negSucc 15),
    (781, Int.ofNat 16), (824, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(142, Int.ofNat 1), (149, Int.ofNat 3), (418, Int.ofNat
    4), (472, Int.ofNat 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (148, Int.ofNat 3), (150,
    Int.negSucc 3), (160, Int.negSucc 5), (162, Int.ofNat 8), (164, Int.ofNat 1), (430,
    Int.negSucc 79), (442, Int.ofNat 24), (443, Int.ofNat 16), (448, Int.ofNat 8), (463, Int.ofNat
    24), (480, Int.negSucc 47), (488, Int.negSucc 47), (495, Int.ofNat 24), (510, Int.negSucc 7),
    (516, Int.negSucc 11), (520, Int.negSucc 15), (524, Int.ofNat 4), (528, Int.ofNat 24), (535,
    Int.ofNat 12), (547, Int.ofNat 32), (550, Int.negSucc 7), (556, Int.ofNat 6), (560, Int.ofNat
    12), (696, Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15),
    (760, Int.ofNat 16), (766, Int.negSucc 31), (774, Int.negSucc 15), (781, Int.ofNat 32), (787,
    Int.ofNat 16), (802, Int.ofNat 16), (824, Int.ofNat 24), (826, Int.negSucc 7), (832,
    Int.negSucc 7)] },
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
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 14), (172, Int.ofNat 5), (177,
    Int.ofNat 4), (481, Int.negSucc 71), (489, Int.negSucc 31), (496, Int.ofNat 8), (500,
    Int.ofNat 60), (564, Int.negSucc 11), (578, Int.ofNat 24), (596, Int.ofNat 12), (710,
    Int.ofNat 32), (767, Int.negSucc 15), (775, Int.negSucc 15), (782, Int.ofNat 16), (825,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.ofNat 7), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (492, Int.negSucc 35), (501, Int.ofNat 36), (533, Int.ofNat 12), (548,
    Int.negSucc 23), (551, Int.ofNat 24), (567, Int.negSucc 17), (581, Int.ofNat 36), (788,
    Int.negSucc 47), (827, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 2), (499, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (174, Int.ofNat 1), (470,
    Int.negSucc 0), (517, Int.negSucc 1), (521, Int.ofNat 1), (541, Int.negSucc 1), (590,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(170, Int.negSucc 4), (174, Int.ofNat 2), (180,
    Int.negSucc 7), (182, Int.ofNat 2), (192, Int.ofNat 3), (470, Int.negSucc 19), (502, Int.ofNat
    8), (517, Int.negSucc 7), (521, Int.negSucc 11), (525, Int.ofNat 2), (541, Int.negSucc 7),
    (585, Int.ofNat 6), (590, Int.ofNat 16), (803, Int.ofNat 8), (833, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 3), (474, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 3), (181, Int.negSucc 8), (183,
    Int.ofNat 4), (484, Int.negSucc 19), (503, Int.ofNat 12), (529, Int.negSucc 11), (536,
    Int.negSucc 13), (573, Int.negSucc 5), (593, Int.ofNat 12), (796, Int.negSucc 7), (830,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 25), (173, Int.negSucc 23), (178,
    Int.ofNat 18), (492, Int.negSucc 107), (501, Int.ofNat 96), (533, Int.ofNat 24), (548,
    Int.negSucc 71), (551, Int.ofNat 72), (567, Int.negSucc 53), (581, Int.ofNat 108), (788,
    Int.negSucc 143), (827, Int.ofNat 72)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (174, Int.ofNat 1), (182,
    Int.negSucc 0), (470, Int.negSucc 2), (517, Int.negSucc 1), (521, Int.ofNat 1), (541,
    Int.negSucc 3), (585, Int.ofNat 1), (590, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 2), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.negSucc 0), (474, Int.negSucc 0)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 25), (173, Int.negSucc 23), (178,
    Int.ofNat 6), (492, Int.negSucc 131), (501, Int.ofNat 96), (548, Int.negSucc 71), (551,
    Int.ofNat 72), (567, Int.negSucc 53), (581, Int.ofNat 132), (788, Int.negSucc 143), (827,
    Int.ofNat 72)] },
  { denominator := Int.ofNat 4, terms := [(170, Int.negSucc 4), (174, Int.ofNat 2), (180,
    Int.negSucc 6), (182, Int.ofNat 2), (192, Int.ofNat 3), (470, Int.negSucc 19), (502, Int.ofNat
    12), (517, Int.negSucc 9), (521, Int.negSucc 11), (525, Int.ofNat 2), (541, Int.negSucc 3),
    (585, Int.ofNat 6), (590, Int.ofNat 16), (803, Int.ofNat 8), (833, Int.negSucc 3)] },
  { denominator := Int.ofNat 24, terms := [(168, Int.ofNat 7), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (186, Int.negSucc 11), (191, Int.ofNat 12), (492, Int.negSucc 35), (501,
    Int.ofNat 36), (533, Int.negSucc 11), (551, Int.ofNat 24), (561, Int.negSucc 11), (567,
    Int.negSucc 23), (581, Int.ofNat 36), (788, Int.negSucc 47), (827, Int.ofNat 24)] },
  { denominator := Int.ofNat 4, terms := [(176, Int.ofNat 5), (474, Int.ofNat 5)] },
  { denominator := Int.ofNat 24, terms := [(168, Int.ofNat 25), (173, Int.negSucc 23), (178,
    Int.ofNat 18), (186, Int.negSucc 11), (191, Int.ofNat 12), (492, Int.negSucc 107), (501,
    Int.ofNat 96), (533, Int.ofNat 12), (548, Int.negSucc 71), (551, Int.ofNat 72), (567,
    Int.negSucc 59), (581, Int.ofNat 108), (788, Int.negSucc 143), (827, Int.ofNat 72)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (206, Int.ofNat 2), (518,
    Int.negSucc 5), (522, Int.negSucc 1), (542, Int.negSucc 3), (553, Int.ofNat 4), (565,
    Int.negSucc 5), (628, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.negSucc 1), (207, Int.ofNat 2), (523,
    Int.negSucc 1), (568, Int.ofNat 2), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 1), (201, Int.negSucc 4), (208,
    Int.ofNat 2), (217, Int.ofNat 6), (518, Int.negSucc 11), (522, Int.negSucc 17), (526,
    Int.ofNat 2), (542, Int.negSucc 3), (553, Int.ofNat 12), (565, Int.negSucc 23), (618,
    Int.ofNat 12), (628, Int.ofNat 12), (721, Int.ofNat 8), (769, Int.negSucc 7), (777,
    Int.negSucc 7), (804, Int.ofNat 8), (834, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 2), (527, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(196, Int.ofNat 2), (203, Int.negSucc 11), (210,
    Int.ofNat 8), (530, Int.negSucc 47), (537, Int.negSucc 39), (554, Int.ofNat 24), (579,
    Int.negSucc 95), (605, Int.negSucc 11), (631, Int.ofNat 24), (732, Int.ofNat 16), (768,
    Int.ofNat 16), (784, Int.negSucc 15), (797, Int.negSucc 15), (831, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

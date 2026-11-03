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
def actionData252 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 2), (425, Int.ofNat 4), (476, Int.ofNat
    4), (544, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 0), (139, Int.ofNat 2), (430,
    Int.ofNat 12), (442, Int.negSucc 7), (480, Int.ofNat 8), (488, Int.ofNat 4), (516, Int.ofNat
    4), (528, Int.negSucc 7), (547, Int.negSucc 3), (766, Int.ofNat 4), (787, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(139, Int.ofNat 2), (148, Int.ofNat 1), (430, Int.ofNat
    36), (442, Int.negSucc 15), (443, Int.negSucc 3), (480, Int.ofNat 24), (488, Int.ofNat 20),
    (516, Int.ofNat 8), (520, Int.ofNat 4), (528, Int.negSucc 15), (535, Int.negSucc 3), (547,
    Int.negSucc 15), (696, Int.negSucc 3), (709, Int.negSucc 3), (746, Int.ofNat 4), (753,
    Int.ofNat 4), (760, Int.negSucc 3), (766, Int.ofNat 12), (774, Int.ofNat 4), (781, Int.negSucc
    3), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 10)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 2), (472, Int.ofNat
    1), (539, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 2), (148, Int.negSucc 0), (150,
    Int.ofNat 6), (151, Int.negSucc 1), (430, Int.ofNat 72), (442, Int.negSucc 15), (443,
    Int.negSucc 7), (448, Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 40), (495,
    Int.ofNat 8), (516, Int.ofNat 8), (520, Int.ofNat 8), (524, Int.ofNat 8), (528, Int.negSucc
    15), (535, Int.negSucc 11), (547, Int.negSucc 23), (550, Int.negSucc 15), (696, Int.negSucc
    7), (709, Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766,
    Int.ofNat 16), (774, Int.ofNat 16), (781, Int.negSucc 7), (787, Int.negSucc 7), (795,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 3, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (532,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.ofNat 2), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 2), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 11), (483, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(483, Int.negSucc 0)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 2), (148, Int.negSucc 0), (160,
    Int.ofNat 6), (164, Int.negSucc 0), (430, Int.ofNat 72), (442, Int.negSucc 15), (443,
    Int.negSucc 7), (463, Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 40), (510,
    Int.ofNat 4), (516, Int.ofNat 8), (520, Int.ofNat 12), (528, Int.negSucc 15), (535,
    Int.negSucc 7), (547, Int.negSucc 23), (556, Int.negSucc 3), (560, Int.negSucc 7), (696,
    Int.negSucc 7), (709, Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat 8), (760,
    Int.negSucc 7), (766, Int.ofNat 16), (774, Int.ofNat 8), (781, Int.negSucc 15), (787,
    Int.negSucc 7), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 6, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(161, Int.ofNat 2), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 2), (458, Int.ofNat 1), (531, Int.ofNat
    2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 8), (139, Int.negSucc 13), (148,
    Int.ofNat 9), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 8), (430, Int.ofNat 40), (442, Int.negSucc
    7), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 8), (495,
    Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 4), (520, Int.ofNat 4), (524, Int.ofNat 4),
    (528, Int.negSucc 7), (535, Int.negSucc 3), (547, Int.negSucc 7), (550, Int.negSucc 7), (556,
    Int.negSucc 1), (560, Int.negSucc 3), (696, Int.negSucc 7), (709, Int.negSucc 7), (746,
    Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat
    8), (781, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 11), (469, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 3), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (470, Int.ofNat 4), (517, Int.ofNat
    2), (541, Int.ofNat 4), (590, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (484, Int.ofNat 4), (529, Int.ofNat
    4), (545, Int.ofNat 4), (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 10), (172, Int.negSucc 3), (481,
    Int.ofNat 48), (489, Int.ofNat 24), (500, Int.negSucc 39), (564, Int.ofNat 8), (578,
    Int.negSucc 15), (596, Int.negSucc 7), (710, Int.negSucc 15), (767, Int.ofNat 8), (775,
    Int.ofNat 8), (782, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 1), (173, Int.ofNat 2), (492,
    Int.ofNat 12), (501, Int.negSucc 7), (533, Int.negSucc 3), (548, Int.ofNat 8), (567, Int.ofNat
    4), (581, Int.negSucc 7), (788, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (180, Int.ofNat 3), (192,
    Int.negSucc 0), (470, Int.ofNat 9), (502, Int.negSucc 1), (517, Int.ofNat 3), (521, Int.ofNat
    4), (541, Int.ofNat 4), (585, Int.negSucc 1), (590, Int.negSucc 5), (803, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (181, Int.ofNat 3), (183,
    Int.negSucc 0), (484, Int.ofNat 9), (503, Int.negSucc 1), (529, Int.ofNat 6), (536, Int.ofNat
    4), (545, Int.ofNat 4), (573, Int.ofNat 2), (593, Int.negSucc 5), (796, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(168, Int.negSucc 16), (173, Int.ofNat 18), (492,
    Int.ofNat 90), (501, Int.negSucc 53), (533, Int.negSucc 23), (548, Int.ofNat 60), (567,
    Int.ofNat 30), (581, Int.negSucc 59), (788, Int.ofNat 60)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (182, Int.ofNat 1), (470, Int.ofNat
    4), (517, Int.ofNat 2), (521, Int.negSucc 0), (525, Int.ofNat 1), (541, Int.ofNat 4), (585,
    Int.negSucc 0), (590, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(182, Int.ofNat 1), (470, Int.ofNat 2), (541, Int.ofNat
    2), (585, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 4), (181, Int.ofNat 8), (183,
    Int.negSucc 2), (484, Int.ofNat 23), (503, Int.negSucc 9), (529, Int.ofNat 14), (536,
    Int.ofNat 14), (545, Int.ofNat 4), (573, Int.ofNat 6), (593, Int.negSucc 13), (796, Int.ofNat
    6)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.negSucc 10), (173, Int.ofNat 12), (178,
    Int.ofNat 3), (492, Int.ofNat 60), (501, Int.negSucc 29), (533, Int.negSucc 5), (548,
    Int.ofNat 36), (567, Int.ofNat 18), (581, Int.negSucc 41), (788, Int.ofNat 36)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(181, Int.negSucc 1), (193, Int.ofNat 2), (484,
    Int.ofNat 8), (529, Int.ofNat 8), (536, Int.negSucc 1), (545, Int.ofNat 8), (557, Int.ofNat
    1), (573, Int.ofNat 2), (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 4), (180, Int.ofNat 8), (192,
    Int.negSucc 2), (470, Int.ofNat 23), (502, Int.negSucc 9), (517, Int.ofNat 7), (521, Int.ofNat
    14), (541, Int.ofNat 4), (585, Int.negSucc 5), (590, Int.negSucc 13), (803, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 1), (181, Int.ofNat 2), (183,
    Int.negSucc 0), (193, Int.ofNat 1), (484, Int.ofNat 11), (503, Int.negSucc 1), (529, Int.ofNat
    6), (536, Int.ofNat 4), (545, Int.ofNat 6), (573, Int.ofNat 3), (593, Int.negSucc 5), (796,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 10), (173, Int.ofNat 12), (186,
    Int.ofNat 6), (492, Int.ofNat 60), (501, Int.negSucc 29), (533, Int.negSucc 5), (548,
    Int.ofNat 36), (567, Int.ofNat 21), (581, Int.negSucc 35), (788, Int.ofNat 36)] },
  { denominator := Int.ofNat 8, terms := [(188, Int.ofNat 4), (507, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(168, Int.negSucc 0), (173, Int.ofNat 1), (178,
    Int.ofNat 1), (186, Int.ofNat 2), (492, Int.ofNat 10), (501, Int.negSucc 3), (533, Int.ofNat
    4), (551, Int.ofNat 4), (561, Int.ofNat 2), (567, Int.ofNat 3), (581, Int.negSucc 5), (788,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(200, Int.ofNat 2), (519, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (201, Int.ofNat 4), (217,
    Int.negSucc 3), (518, Int.ofNat 8), (522, Int.ofNat 12), (542, Int.ofNat 4), (553, Int.negSucc
    7), (565, Int.ofNat 16), (618, Int.negSucc 7), (628, Int.negSucc 7), (721, Int.negSucc 3),
    (769, Int.ofNat 4), (777, Int.ofNat 4), (804, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.ofNat 2), (523, Int.ofNat 4), (568,
    Int.negSucc 1), (591, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 0), (203, Int.ofNat 4), (210,
    Int.negSucc 1), (530, Int.ofNat 16), (537, Int.ofNat 12), (546, Int.ofNat 4), (554,
    Int.negSucc 7), (579, Int.ofNat 32), (605, Int.ofNat 4), (631, Int.negSucc 7), (732,
    Int.negSucc 3), (768, Int.negSucc 3), (784, Int.ofNat 4), (797, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.ofNat 2), (538, Int.ofNat 4), (582,
    Int.negSucc 3), (594, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.negSucc 9), (205, Int.ofNat 4), (549,
    Int.ofNat 24), (555, Int.negSucc 7), (597, Int.ofNat 8), (608, Int.ofNat 8), (621, Int.negSucc
    15), (743, Int.negSucc 7), (776, Int.negSucc 7), (783, Int.ofNat 8), (789, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(199, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.ofNat 2), (213, Int.ofNat 1), (519, Int.ofNat
    4), (574, Int.ofNat 2), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(212, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.ofNat 2), (213, Int.ofNat 2), (519, Int.ofNat
    5), (574, Int.ofNat 2), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(202, Int.ofNat 4), (523, Int.ofNat 7), (568,
    Int.negSucc 1), (591, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(214, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(204, Int.ofNat 4), (538, Int.ofNat 7), (582,
    Int.negSucc 3), (594, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(200, Int.ofNat 1), (213, Int.ofNat 1), (519, Int.ofNat
    3), (574, Int.ofNat 1), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(202, Int.ofNat 2), (207, Int.ofNat 1), (523, Int.ofNat
    5), (568, Int.negSucc 0), (591, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(207, Int.ofNat 1), (523, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(204, Int.ofNat 6), (538, Int.ofNat 9), (594, Int.ofNat
    12)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.ofNat 1), (213, Int.ofNat 1), (519, Int.ofNat
    3), (574, Int.ofNat 2), (586, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(204, Int.ofNat 2), (216, Int.ofNat 2), (538, Int.ofNat
    5), (582, Int.negSucc 1), (594, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(202, Int.ofNat 6), (523, Int.ofNat 9), (591, Int.ofNat
    12)] },
  { denominator := Int.ofNat 2, terms := [(204, Int.ofNat 2), (216, Int.ofNat 1), (538, Int.ofNat
    4), (582, Int.negSucc 1), (594, Int.ofNat 6)] }
]

end VOA.DeligneAudit.D4Two.Certificate

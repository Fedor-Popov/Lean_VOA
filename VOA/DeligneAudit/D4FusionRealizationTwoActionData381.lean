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
def actionData381 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.negSucc 27), (429, Int.ofNat 36), (441, Int.negSucc 1), (447, Int.negSucc 7), (462,
    Int.negSucc 1), (468, Int.ofNat 12), (482, Int.negSucc 13), (490, Int.negSucc 11), (695,
    Int.negSucc 23), (745, Int.ofNat 16), (752, Int.ofNat 16), (759, Int.negSucc 15), (823,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 4), (115, Int.ofNat 5), (133,
    Int.ofNat 4), (391, Int.negSucc 39), (429, Int.ofNat 72), (441, Int.negSucc 7), (468,
    Int.ofNat 24), (482, Int.negSucc 23), (490, Int.negSucc 27), (695, Int.negSucc 47), (745,
    Int.ofNat 32), (752, Int.ofNat 32), (759, Int.negSucc 31), (823, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (115, Int.negSucc 1), (128,
    Int.ofNat 6), (391, Int.negSucc 11), (429, Int.ofNat 28), (462, Int.negSucc 3), (468,
    Int.ofNat 12), (482, Int.negSucc 5), (490, Int.negSucc 5), (695, Int.negSucc 11), (745,
    Int.ofNat 8), (752, Int.ofNat 8), (759, Int.negSucc 7), (823, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (415, Int.ofNat 4), (465, Int.ofNat
    2), (540, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 2), (425, Int.ofNat 4), (476, Int.ofNat
    4), (544, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 0), (139, Int.ofNat 2), (430,
    Int.ofNat 16), (442, Int.negSucc 11), (480, Int.ofNat 12), (488, Int.ofNat 4), (516, Int.ofNat
    6), (528, Int.negSucc 11), (547, Int.negSucc 3), (766, Int.ofNat 8), (787, Int.negSucc 7),
    (824, Int.negSucc 3), (826, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.ofNat 4), (148, Int.ofNat
    2), (430, Int.ofNat 96), (442, Int.negSucc 47), (443, Int.negSucc 15), (480, Int.ofNat 72),
    (488, Int.ofNat 48), (516, Int.ofNat 24), (520, Int.ofNat 12), (528, Int.negSucc 47), (535,
    Int.negSucc 11), (547, Int.negSucc 39), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 48), (774,
    Int.ofNat 16), (781, Int.negSucc 15), (787, Int.negSucc 31), (824, Int.negSucc 23), (826,
    Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 10)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 2), (472, Int.ofNat
    1), (539, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 3), (148, Int.negSucc 0), (150,
    Int.ofNat 6), (151, Int.negSucc 1), (430, Int.ofNat 96), (442, Int.negSucc 23), (443,
    Int.negSucc 15), (448, Int.negSucc 23), (480, Int.ofNat 48), (488, Int.ofNat 48), (495,
    Int.ofNat 16), (516, Int.ofNat 12), (520, Int.ofNat 12), (524, Int.ofNat 12), (528,
    Int.negSucc 23), (535, Int.negSucc 15), (547, Int.negSucc 31), (550, Int.negSucc 23), (696,
    Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753, Int.ofNat 16), (760,
    Int.negSucc 15), (766, Int.ofNat 32), (774, Int.ofNat 32), (781, Int.negSucc 15), (787,
    Int.negSucc 15), (795, Int.negSucc 15), (824, Int.negSucc 23), (826, Int.ofNat 8), (829,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 3, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (532,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.ofNat 2), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 2), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 11), (483, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(483, Int.negSucc 0)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 3), (148, Int.negSucc 0), (160,
    Int.ofNat 6), (164, Int.negSucc 0), (430, Int.ofNat 96), (442, Int.negSucc 23), (443,
    Int.negSucc 15), (463, Int.negSucc 23), (480, Int.ofNat 48), (488, Int.ofNat 48), (510,
    Int.ofNat 8), (516, Int.ofNat 12), (520, Int.ofNat 16), (528, Int.negSucc 23), (535,
    Int.negSucc 11), (547, Int.negSucc 31), (556, Int.negSucc 5), (560, Int.negSucc 11), (696,
    Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753, Int.ofNat 16), (760,
    Int.negSucc 15), (766, Int.ofNat 32), (774, Int.ofNat 16), (781, Int.negSucc 31), (787,
    Int.negSucc 15), (802, Int.negSucc 15), (824, Int.negSucc 23), (826, Int.ofNat 8), (832,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 6, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(161, Int.ofNat 2), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 2), (458, Int.ofNat 1), (531, Int.ofNat
    2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 9), (139, Int.negSucc 13), (148,
    Int.ofNat 9), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 8), (430, Int.ofNat 48), (442, Int.negSucc
    7), (443, Int.negSucc 7), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 24),
    (488, Int.ofNat 16), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 4), (520,
    Int.ofNat 8), (524, Int.ofNat 4), (528, Int.negSucc 7), (535, Int.negSucc 7), (547,
    Int.negSucc 15), (550, Int.negSucc 7), (556, Int.negSucc 1), (560, Int.negSucc 3), (696,
    Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753, Int.ofNat 16), (760,
    Int.negSucc 15), (766, Int.ofNat 16), (774, Int.ofNat 16), (781, Int.negSucc 15), (824,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 11), (469, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 3), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (470, Int.ofNat 4), (517, Int.ofNat
    2), (541, Int.ofNat 4), (590, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (484, Int.ofNat 4), (529, Int.ofNat
    4), (545, Int.ofNat 4), (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 17), (172, Int.negSucc 6), (481,
    Int.ofNat 72), (489, Int.ofNat 32), (500, Int.negSucc 59), (564, Int.ofNat 12), (578,
    Int.negSucc 23), (596, Int.negSucc 11), (710, Int.negSucc 31), (767, Int.ofNat 16), (775,
    Int.ofNat 16), (782, Int.negSucc 15), (825, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.negSucc 6), (173, Int.ofNat 6), (492,
    Int.ofNat 48), (501, Int.negSucc 35), (533, Int.negSucc 11), (548, Int.ofNat 24), (567,
    Int.ofNat 18), (581, Int.negSucc 35), (788, Int.ofNat 48), (827, Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 5), (180, Int.ofNat 8), (192,
    Int.negSucc 2), (470, Int.ofNat 24), (502, Int.negSucc 7), (517, Int.ofNat 8), (521, Int.ofNat
    12), (541, Int.ofNat 8), (585, Int.negSucc 5), (590, Int.negSucc 15), (803, Int.negSucc 7),
    (833, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 5), (181, Int.ofNat 8), (183,
    Int.negSucc 2), (484, Int.ofNat 24), (503, Int.negSucc 7), (529, Int.ofNat 16), (536,
    Int.ofNat 12), (545, Int.ofNat 8), (573, Int.ofNat 6), (593, Int.negSucc 15), (796, Int.ofNat
    8), (830, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(168, Int.negSucc 12), (173, Int.ofNat 12), (492,
    Int.ofNat 80), (501, Int.negSucc 55), (533, Int.negSucc 15), (548, Int.ofNat 40), (567,
    Int.ofNat 30), (581, Int.negSucc 59), (788, Int.ofNat 80), (827, Int.negSucc 39)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (182, Int.ofNat 1), (470, Int.ofNat
    4), (517, Int.ofNat 2), (521, Int.negSucc 0), (525, Int.ofNat 1), (541, Int.ofNat 4), (585,
    Int.negSucc 0), (590, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(182, Int.ofNat 1), (470, Int.ofNat 2), (541, Int.ofNat
    2), (585, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 11), (181, Int.ofNat 22), (183,
    Int.negSucc 8), (484, Int.ofNat 64), (503, Int.negSucc 31), (529, Int.ofNat 40), (536,
    Int.ofNat 40), (545, Int.ofNat 8), (573, Int.ofNat 18), (593, Int.negSucc 39), (796, Int.ofNat
    24), (830, Int.negSucc 11)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 24), (173, Int.ofNat 24), (178,
    Int.ofNat 6), (492, Int.ofNat 156), (501, Int.negSucc 95), (533, Int.negSucc 11), (548,
    Int.ofNat 72), (567, Int.ofNat 54), (581, Int.negSucc 119), (788, Int.ofNat 144), (827,
    Int.negSucc 71)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(181, Int.negSucc 1), (193, Int.ofNat 2), (484,
    Int.ofNat 8), (529, Int.ofNat 8), (536, Int.negSucc 1), (545, Int.ofNat 8), (557, Int.ofNat
    1), (573, Int.ofNat 2), (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(170, Int.ofNat 11), (180, Int.ofNat 22), (192,
    Int.negSucc 8), (470, Int.ofNat 64), (502, Int.negSucc 31), (517, Int.ofNat 20), (521,
    Int.ofNat 40), (541, Int.ofNat 8), (585, Int.negSucc 17), (590, Int.negSucc 39), (803,
    Int.negSucc 23), (833, Int.ofNat 12)] },
  { denominator := Int.ofNat 4, terms := [(171, Int.ofNat 3), (181, Int.ofNat 6), (183,
    Int.negSucc 2), (193, Int.ofNat 2), (484, Int.ofNat 28), (503, Int.negSucc 7), (529, Int.ofNat
    16), (536, Int.ofNat 12), (545, Int.ofNat 12), (573, Int.ofNat 8), (593, Int.negSucc 15),
    (796, Int.ofNat 8), (830, Int.negSucc 3)] },
  { denominator := Int.ofNat 24, terms := [(168, Int.negSucc 24), (173, Int.ofNat 24), (186,
    Int.ofNat 12), (492, Int.ofNat 156), (501, Int.negSucc 95), (533, Int.negSucc 11), (548,
    Int.ofNat 72), (567, Int.ofNat 60), (581, Int.negSucc 107), (788, Int.ofNat 144), (827,
    Int.negSucc 71)] },
  { denominator := Int.ofNat 8, terms := [(188, Int.ofNat 4), (507, Int.ofNat 1)] },
  { denominator := Int.ofNat 24, terms := [(168, Int.negSucc 6), (173, Int.ofNat 6), (178,
    Int.ofNat 6), (186, Int.ofNat 12), (492, Int.ofNat 72), (501, Int.negSucc 35), (533, Int.ofNat
    24), (551, Int.ofNat 24), (561, Int.ofNat 12), (567, Int.ofNat 24), (581, Int.negSucc 47),
    (788, Int.ofNat 48), (827, Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [(200, Int.ofNat 2), (519, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (201, Int.ofNat 5), (217,
    Int.negSucc 5), (518, Int.ofNat 12), (522, Int.ofNat 18), (542, Int.ofNat 4), (553,
    Int.negSucc 11), (565, Int.ofNat 24), (618, Int.negSucc 11), (628, Int.negSucc 11), (721,
    Int.negSucc 7), (769, Int.ofNat 8), (777, Int.ofNat 8), (804, Int.negSucc 7), (834, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.ofNat 2), (523, Int.ofNat 4), (568,
    Int.negSucc 1), (591, Int.ofNat 8)] }
]

end VOA.DeligneAudit.D4Two.Certificate

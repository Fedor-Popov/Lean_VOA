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
def actionData225 : List ActionCase := [
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (148,
    Int.negSucc 2), (160, Int.ofNat 6), (164, Int.negSucc 0), (430, Int.ofNat 48), (442,
    Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 16), (510,
    Int.ofNat 8), (516, Int.ofNat 8), (520, Int.ofNat 4), (528, Int.negSucc 15), (547, Int.negSucc
    7), (556, Int.negSucc 3), (560, Int.negSucc 7), (766, Int.ofNat 8), (781, Int.negSucc 7),
    (787, Int.negSucc 7), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(161, Int.ofNat 2), (451, Int.ofNat 3), (505, Int.ofNat
    2), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.negSucc 0), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 1), (458, Int.ofNat 1), (531, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 2), (150, Int.negSucc 3), (153,
    Int.ofNat 4), (157, Int.negSucc 3), (162, Int.ofNat 4), (430, Int.ofNat 16), (480, Int.ofNat
    8), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 2), (524, Int.ofNat 2), (528,
    Int.negSucc 3), (550, Int.negSucc 3), (556, Int.negSucc 0), (560, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 1), (437, Int.ofNat 4), (498, Int.ofNat
    4), (532, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 1), (458, Int.ofNat 1), (513, Int.ofNat
    1), (531, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 15), (139, Int.negSucc 7), (148,
    Int.ofNat 2), (160, Int.ofNat 8), (164, Int.negSucc 1), (430, Int.ofNat 224), (442,
    Int.negSucc 23), (443, Int.negSucc 47), (463, Int.negSucc 23), (480, Int.ofNat 128), (488,
    Int.ofNat 160), (510, Int.ofNat 12), (516, Int.ofNat 16), (520, Int.ofNat 52), (528,
    Int.negSucc 31), (535, Int.negSucc 47), (547, Int.negSucc 103), (556, Int.negSucc 7), (560,
    Int.negSucc 15), (696, Int.negSucc 47), (709, Int.negSucc 47), (746, Int.ofNat 48), (753,
    Int.ofNat 48), (760, Int.negSucc 47), (766, Int.ofNat 64), (774, Int.ofNat 48), (781,
    Int.negSucc 63), (787, Int.negSucc 15), (802, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 1), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 4), (148, Int.negSucc 14), (150,
    Int.ofNat 28), (151, Int.negSucc 11), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 224), (442, Int.negSucc 7), (443, Int.negSucc 15), (448, Int.negSucc 63), (463,
    Int.negSucc 7), (480, Int.ofNat 56), (488, Int.ofNat 96), (495, Int.ofNat 80), (510, Int.ofNat
    8), (516, Int.ofNat 8), (520, Int.ofNat 20), (524, Int.ofNat 48), (528, Int.negSucc 15), (535,
    Int.negSucc 31), (547, Int.negSucc 39), (550, Int.negSucc 95), (556, Int.negSucc 3), (560,
    Int.negSucc 7), (696, Int.negSucc 15), (709, Int.negSucc 15), (746, Int.ofNat 16), (753,
    Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 24), (774, Int.ofNat 64), (781,
    Int.negSucc 23), (787, Int.negSucc 7), (795, Int.negSucc 47), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 9), (139, Int.negSucc 9), (148,
    Int.ofNat 11), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 4), (430, Int.ofNat 128), (442,
    Int.negSucc 31), (443, Int.negSucc 15), (448, Int.negSucc 7), (463, Int.negSucc 7), (480,
    Int.ofNat 80), (488, Int.ofNat 64), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat
    20), (520, Int.ofNat 20), (524, Int.ofNat 4), (528, Int.negSucc 39), (535, Int.negSucc 19),
    (547, Int.negSucc 47), (550, Int.negSucc 7), (556, Int.negSucc 1), (560, Int.negSucc 3), (696,
    Int.negSucc 23), (709, Int.negSucc 23), (746, Int.ofNat 24), (753, Int.ofNat 24), (760,
    Int.negSucc 23), (766, Int.ofNat 40), (774, Int.ofNat 24), (781, Int.negSucc 23), (787,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 3), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (160, Int.ofNat 12), (164, Int.negSucc 3), (430, Int.ofNat 96), (443,
    Int.negSucc 7), (463, Int.negSucc 55), (480, Int.ofNat 16), (488, Int.ofNat 32), (510,
    Int.ofNat 20), (520, Int.ofNat 12), (535, Int.negSucc 7), (547, Int.negSucc 15), (556,
    Int.negSucc 15), (560, Int.negSucc 31), (696, Int.negSucc 7), (709, Int.negSucc 7), (746,
    Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat
    8), (781, Int.negSucc 39), (802, Int.negSucc 31)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.ofNat 5), (172, Int.negSucc 2), (481,
    Int.ofNat 40), (489, Int.ofNat 16), (500, Int.negSucc 27), (564, Int.ofNat 8), (578,
    Int.negSucc 15), (596, Int.negSucc 3), (710, Int.negSucc 15), (767, Int.ofNat 8), (775,
    Int.ofNat 8), (782, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 1), (492, Int.ofNat 24), (501,
    Int.negSucc 23), (567, Int.ofNat 12), (581, Int.negSucc 23), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 4), (180, Int.ofNat 5), (192,
    Int.negSucc 1), (470, Int.ofNat 18), (502, Int.negSucc 3), (517, Int.ofNat 6), (521, Int.ofNat
    8), (541, Int.ofNat 8), (585, Int.negSucc 3), (590, Int.negSucc 11), (803, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 4), (181, Int.ofNat 5), (183,
    Int.negSucc 1), (484, Int.ofNat 18), (503, Int.negSucc 3), (529, Int.ofNat 12), (536,
    Int.ofNat 8), (545, Int.ofNat 8), (573, Int.ofNat 4), (593, Int.negSucc 11), (796, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 19), (172, Int.negSucc 8), (481,
    Int.ofNat 88), (489, Int.ofNat 40), (500, Int.negSucc 67), (564, Int.ofNat 16), (578,
    Int.negSucc 31), (596, Int.negSucc 11), (710, Int.negSucc 31), (767, Int.ofNat 16), (775,
    Int.ofNat 16), (782, Int.negSucc 15)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.negSucc 9), (173, Int.ofNat 6), (492,
    Int.ofNat 78), (501, Int.negSucc 59), (533, Int.ofNat 6), (548, Int.ofNat 12), (567, Int.ofNat
    36), (581, Int.negSucc 71), (788, Int.ofNat 72)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (182, Int.ofNat 1), (470, Int.ofNat
    5), (517, Int.ofNat 2), (525, Int.ofNat 1), (541, Int.ofNat 4), (585, Int.negSucc 0), (590,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 41), (172, Int.negSucc 16), (177,
    Int.negSucc 3), (481, Int.ofNat 176), (489, Int.ofNat 80), (496, Int.ofNat 8), (500,
    Int.negSucc 139), (564, Int.ofNat 32), (578, Int.negSucc 55), (596, Int.negSucc 27), (710,
    Int.negSucc 63), (767, Int.ofNat 32), (775, Int.ofNat 32), (782, Int.negSucc 31)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 0), (173, Int.ofNat 1), (178,
    Int.ofNat 1), (492, Int.ofNat 8), (501, Int.negSucc 1), (533, Int.ofNat 2), (548, Int.ofNat
    4), (567, Int.ofNat 2), (581, Int.negSucc 5), (788, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 4), (180, Int.ofNat 10), (192,
    Int.negSucc 3), (470, Int.ofNat 26), (502, Int.negSucc 7), (517, Int.ofNat 8), (521, Int.ofNat
    14), (541, Int.ofNat 8), (585, Int.negSucc 7), (590, Int.negSucc 15), (803, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 4), (181, Int.ofNat 10), (183,
    Int.negSucc 3), (484, Int.ofNat 26), (503, Int.negSucc 7), (529, Int.ofNat 16), (536,
    Int.ofNat 14), (545, Int.ofNat 8), (573, Int.ofNat 8), (593, Int.negSucc 15), (796, Int.ofNat
    8)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 2), (180, Int.ofNat 5), (182, Int.ofNat
    2), (192, Int.negSucc 1), (470, Int.ofNat 18), (502, Int.negSucc 3), (517, Int.ofNat 4), (521,
    Int.ofNat 8), (541, Int.ofNat 8), (585, Int.negSucc 5), (590, Int.negSucc 7), (803,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 24), (181, Int.ofNat 53), (183,
    Int.negSucc 21), (484, Int.ofNat 146), (503, Int.negSucc 51), (529, Int.ofNat 92), (536,
    Int.ofNat 80), (545, Int.ofNat 40), (573, Int.ofNat 44), (593, Int.negSucc 91), (796,
    Int.ofNat 44)] },
  { denominator := Int.ofNat 4, terms := [(181, Int.negSucc 1), (193, Int.ofNat 2), (484,
    Int.ofNat 10), (529, Int.ofNat 8), (545, Int.ofNat 8), (557, Int.ofNat 1), (573, Int.ofNat 2),
    (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 41), (172, Int.negSucc 16), (185,
    Int.negSucc 7), (481, Int.ofNat 176), (489, Int.ofNat 80), (500, Int.negSucc 139), (511,
    Int.ofNat 4), (564, Int.ofNat 28), (578, Int.negSucc 63), (596, Int.negSucc 27), (710,
    Int.negSucc 63), (767, Int.ofNat 32), (775, Int.ofNat 32), (782, Int.negSucc 31)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData295 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (126, Int.ofNat 4), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.negSucc 3), (412, Int.ofNat 4), (454,
    Int.negSucc 1), (478, Int.negSucc 11), (493, Int.negSucc 3), (504, Int.ofNat 1), (512,
    Int.ofNat 2), (706, Int.ofNat 12), (735, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (134,
    Int.ofNat 1), (404, Int.negSucc 5), (412, Int.ofNat 12), (454, Int.negSucc 5), (504, Int.ofNat
    3), (512, Int.ofNat 6), (706, Int.ofNat 4), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (430, Int.negSucc 23), (442,
    Int.ofNat 24), (480, Int.negSucc 23), (516, Int.negSucc 11), (528, Int.ofNat 24), (709,
    Int.ofNat 8), (741, Int.negSucc 7), (766, Int.negSucc 15), (787, Int.ofNat 16), (824,
    Int.ofNat 8), (826, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 2), (362, Int.ofNat 1), (419, Int.ofNat
    2), (702, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 1), (380, Int.ofNat 12), (390, Int.negSucc 7), (421, Int.ofNat 16), (464,
    Int.ofNat 6), (475, Int.negSucc 7), (487, Int.negSucc 3), (708, Int.ofNat 4), (765,
    Int.negSucc 7), (822, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 2), (367, Int.ofNat 1), (431, Int.ofNat
    2), (699, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 2), (118, Int.ofNat 1), (385,
    Int.ofNat 12), (396, Int.negSucc 7), (433, Int.ofNat 16), (471, Int.ofNat 6), (486,
    Int.negSucc 3), (497, Int.negSucc 7), (707, Int.ofNat 4), (773, Int.negSucc 7), (820,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.ofNat 6), (740, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 1), (465, Int.negSucc 1), (540,
    Int.ofNat 4), (719, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 1), (476, Int.negSucc 3), (544,
    Int.ofNat 4), (730, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 0), (430, Int.negSucc 27), (442,
    Int.ofNat 12), (443, Int.ofNat 12), (480, Int.negSucc 23), (488, Int.negSucc 15), (516,
    Int.negSucc 5), (520, Int.negSucc 5), (528, Int.ofNat 12), (535, Int.ofNat 6), (547, Int.ofNat
    12), (696, Int.ofNat 14), (709, Int.ofNat 16), (741, Int.negSucc 3), (746, Int.negSucc 7),
    (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 8), (824, Int.ofNat 8), (826, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.negSucc 0), (472, Int.negSucc 0), (539,
    Int.ofNat 2), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 1), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 79), (442, Int.ofNat 24), (443,
    Int.ofNat 24), (448, Int.ofNat 24), (480, Int.negSucc 47), (488, Int.negSucc 31), (495,
    Int.negSucc 23), (516, Int.negSucc 11), (520, Int.negSucc 11), (524, Int.negSucc 11), (528,
    Int.ofNat 24), (535, Int.ofNat 12), (547, Int.ofNat 24), (550, Int.ofNat 24), (696, Int.ofNat
    28), (709, Int.ofNat 40), (729, Int.negSucc 7), (741, Int.negSucc 7), (746, Int.negSucc 15),
    (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 31), (774, Int.negSucc 31),
    (781, Int.ofNat 16), (787, Int.ofNat 16), (795, Int.ofNat 16), (824, Int.ofNat 24), (826,
    Int.negSucc 7), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 3), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.negSucc 0), (347, Int.negSucc 0), (420,
    Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (120,
    Int.negSucc 3), (380, Int.ofNat 12), (390, Int.negSucc 7), (421, Int.ofNat 16), (464,
    Int.ofNat 4), (475, Int.negSucc 11), (487, Int.negSucc 3), (708, Int.ofNat 4), (765,
    Int.negSucc 7), (822, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 1), (367, Int.negSucc 0), (452,
    Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (130, Int.ofNat 1), (404,
    Int.ofNat 6), (412, Int.negSucc 7), (454, Int.ofNat 8), (485, Int.ofNat 4), (504, Int.negSucc
    2), (512, Int.negSucc 3), (706, Int.negSucc 3), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.ofNat 1), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(531, Int.negSucc 2), (739, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 1), (148, Int.ofNat 1), (160,
    Int.negSucc 1), (164, Int.ofNat 1), (430, Int.negSucc 79), (442, Int.ofNat 24), (443,
    Int.ofNat 24), (463, Int.ofNat 24), (480, Int.negSucc 47), (488, Int.negSucc 31), (510,
    Int.negSucc 11), (516, Int.negSucc 11), (520, Int.negSucc 11), (528, Int.ofNat 24), (535,
    Int.ofNat 12), (547, Int.ofNat 24), (556, Int.ofNat 6), (560, Int.ofNat 12), (696, Int.ofNat
    28), (709, Int.ofNat 40), (717, Int.ofNat 8), (741, Int.negSucc 7), (746, Int.negSucc 15),
    (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 31), (774, Int.negSucc 15),
    (781, Int.ofNat 32), (787, Int.ofNat 16), (802, Int.ofNat 16), (824, Int.ofNat 24), (826,
    Int.negSucc 7), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(451, Int.negSucc 0), (505, Int.negSucc 0), (543,
    Int.negSucc 3), (728, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 3), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 2), (91, Int.negSucc 1), (347,
    Int.negSucc 5), (420, Int.ofNat 6), (432, Int.ofNat 6), (705, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (131,
    Int.negSucc 1), (385, Int.ofNat 28), (396, Int.negSucc 19), (433, Int.ofNat 32), (471,
    Int.ofNat 11), (486, Int.negSucc 7), (497, Int.negSucc 21), (707, Int.ofNat 8), (773,
    Int.negSucc 15), (820, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 5), (92, Int.negSucc 1), (362,
    Int.negSucc 2), (419, Int.negSucc 5), (453, Int.ofNat 3), (702, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 7), (130, Int.ofNat 4), (132,
    Int.negSucc 3), (404, Int.ofNat 28), (412, Int.negSucc 39), (454, Int.ofNat 32), (485,
    Int.ofNat 16), (504, Int.negSucc 10), (512, Int.negSucc 21), (706, Int.negSucc 15), (780,
    Int.negSucc 31), (817, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (148,
    Int.negSucc 8), (150, Int.ofNat 12), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (162, Int.negSucc 7), (430, Int.negSucc 95), (442, Int.ofNat 56), (443, Int.ofNat 16),
    (448, Int.ofNat 8), (463, Int.ofNat 8), (480, Int.negSucc 71), (488, Int.negSucc 15), (495,
    Int.negSucc 7), (510, Int.negSucc 3), (516, Int.negSucc 27), (520, Int.negSucc 7), (524,
    Int.negSucc 3), (528, Int.ofNat 56), (535, Int.ofNat 8), (547, Int.ofNat 16), (550, Int.ofNat
    8), (556, Int.ofNat 2), (560, Int.ofNat 4), (696, Int.ofNat 4), (709, Int.ofNat 40), (741,
    Int.negSucc 15), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766,
    Int.negSucc 47), (774, Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 32), (824,
    Int.ofNat 32), (826, Int.negSucc 23), (829, Int.negSucc 7), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 3), (172, Int.ofNat 2), (481,
    Int.negSucc 15), (489, Int.negSucc 5), (500, Int.ofNat 14), (564, Int.negSucc 2), (578,
    Int.ofNat 6), (596, Int.ofNat 2), (710, Int.ofNat 9), (767, Int.negSucc 3), (775, Int.negSucc
    3), (782, Int.ofNat 4), (825, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 3), (492, Int.negSucc 35), (501,
    Int.ofNat 36), (533, Int.negSucc 11), (567, Int.negSucc 17), (581, Int.ofNat 36), (742,
    Int.ofNat 24), (788, Int.negSucc 47), (827, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.ofNat 4), (130,
    Int.negSucc 0), (404, Int.ofNat 2), (412, Int.negSucc 3), (454, Int.negSucc 1), (478,
    Int.ofNat 4), (485, Int.negSucc 3), (493, Int.ofNat 4), (706, Int.negSucc 3), (780,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 3), (150, Int.ofNat 6), (151, Int.negSucc 1), (430,
    Int.ofNat 48), (442, Int.negSucc 15), (443, Int.negSucc 7), (448, Int.negSucc 15), (480,
    Int.ofNat 32), (488, Int.ofNat 8), (495, Int.ofNat 24), (516, Int.ofNat 12), (524, Int.ofNat
    12), (528, Int.negSucc 15), (535, Int.negSucc 3), (547, Int.negSucc 7), (550, Int.negSucc 15),
    (696, Int.negSucc 7), (709, Int.negSucc 15), (766, Int.ofNat 16), (774, Int.ofNat 16), (781,
    Int.negSucc 7), (787, Int.negSucc 15), (795, Int.negSucc 15), (824, Int.negSucc 15), (826,
    Int.ofNat 8), (829, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 4), (172, Int.ofNat 2), (177,
    Int.ofNat 2), (481, Int.negSucc 23), (489, Int.negSucc 11), (496, Int.ofNat 4), (500,
    Int.ofNat 24), (564, Int.negSucc 5), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat
    14), (767, Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 4), (825, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 2), (180, Int.negSucc 5), (192,
    Int.ofNat 3), (470, Int.negSucc 17), (502, Int.ofNat 12), (517, Int.negSucc 5), (521,
    Int.negSucc 9), (541, Int.negSucc 3), (585, Int.ofNat 6), (590, Int.ofNat 12), (720, Int.ofNat
    4), (803, Int.ofNat 8), (833, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 2), (181, Int.negSucc 5), (183,
    Int.ofNat 3), (484, Int.negSucc 17), (503, Int.ofNat 12), (529, Int.negSucc 11), (536,
    Int.negSucc 9), (545, Int.negSucc 3), (573, Int.negSucc 5), (593, Int.ofNat 12), (731,
    Int.ofNat 4), (796, Int.negSucc 7), (830, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 32), (172, Int.ofNat 15), (481,
    Int.negSucc 111), (489, Int.negSucc 43), (500, Int.ofNat 96), (564, Int.negSucc 17), (578,
    Int.ofNat 36), (596, Int.ofNat 16), (710, Int.ofNat 54), (767, Int.negSucc 23), (775,
    Int.negSucc 23), (782, Int.ofNat 24), (825, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 1), (473, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData169 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 2), (367, Int.ofNat 1), (431, Int.ofNat
    2), (699, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 2), (118, Int.ofNat 1), (385,
    Int.ofNat 8), (396, Int.negSucc 3), (433, Int.ofNat 12), (471, Int.ofNat 4), (486, Int.negSucc
    3), (497, Int.negSucc 3), (707, Int.ofNat 4), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.ofNat 6), (740, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 1), (465, Int.negSucc 1), (540,
    Int.ofNat 4), (719, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 1), (476, Int.negSucc 3), (544,
    Int.ofNat 4), (730, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (430, Int.negSucc 39), (442,
    Int.ofNat 16), (443, Int.ofNat 16), (480, Int.negSucc 31), (488, Int.negSucc 23), (516,
    Int.negSucc 7), (520, Int.negSucc 7), (528, Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat
    16), (696, Int.ofNat 16), (709, Int.ofNat 24), (741, Int.negSucc 7), (746, Int.negSucc 7),
    (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.negSucc 0), (472, Int.negSucc 0), (539,
    Int.ofNat 2), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 55), (442, Int.ofNat 16), (443,
    Int.ofNat 16), (448, Int.ofNat 16), (480, Int.negSucc 31), (488, Int.negSucc 23), (495,
    Int.negSucc 15), (516, Int.negSucc 7), (520, Int.negSucc 7), (524, Int.negSucc 7), (528,
    Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat 16), (550, Int.ofNat 16), (696, Int.ofNat
    16), (709, Int.ofNat 32), (729, Int.negSucc 7), (741, Int.negSucc 7), (746, Int.negSucc 7),
    (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 15), (781,
    Int.ofNat 8), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 3), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.negSucc 0), (347, Int.negSucc 0), (420,
    Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (120,
    Int.negSucc 3), (380, Int.ofNat 8), (390, Int.negSucc 3), (421, Int.ofNat 12), (464, Int.ofNat
    2), (475, Int.negSucc 7), (487, Int.negSucc 3), (708, Int.ofNat 4), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 1), (367, Int.negSucc 0), (452,
    Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (130, Int.ofNat 1), (404,
    Int.ofNat 4), (412, Int.negSucc 3), (454, Int.ofNat 6), (485, Int.ofNat 4), (504, Int.negSucc
    1), (512, Int.negSucc 1), (706, Int.negSucc 3), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.ofNat 1), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(531, Int.negSucc 2), (739, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (160,
    Int.negSucc 1), (164, Int.ofNat 1), (430, Int.negSucc 55), (442, Int.ofNat 16), (443,
    Int.ofNat 16), (463, Int.ofNat 16), (480, Int.negSucc 31), (488, Int.negSucc 23), (510,
    Int.negSucc 7), (516, Int.negSucc 7), (520, Int.negSucc 7), (528, Int.ofNat 16), (535,
    Int.ofNat 8), (547, Int.ofNat 16), (556, Int.ofNat 4), (560, Int.ofNat 8), (696, Int.ofNat
    16), (709, Int.ofNat 32), (717, Int.ofNat 8), (741, Int.negSucc 7), (746, Int.negSucc 7),
    (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781,
    Int.ofNat 16), (787, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(451, Int.negSucc 0), (505, Int.negSucc 0), (543,
    Int.negSucc 3), (728, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 3), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 2), (91, Int.negSucc 1), (347,
    Int.negSucc 5), (420, Int.ofNat 6), (432, Int.ofNat 6), (705, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (131,
    Int.negSucc 1), (385, Int.ofNat 20), (396, Int.negSucc 11), (433, Int.ofNat 24), (471,
    Int.ofNat 7), (486, Int.negSucc 7), (497, Int.negSucc 13), (707, Int.ofNat 8), (773,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 5), (92, Int.negSucc 1), (362,
    Int.negSucc 2), (419, Int.negSucc 5), (453, Int.ofNat 3), (702, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 7), (130, Int.ofNat 4), (132,
    Int.negSucc 3), (404, Int.ofNat 20), (412, Int.negSucc 23), (454, Int.ofNat 24), (485,
    Int.ofNat 16), (504, Int.negSucc 6), (512, Int.negSucc 13), (706, Int.negSucc 15), (780,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 6), (148,
    Int.negSucc 8), (150, Int.ofNat 12), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (162, Int.negSucc 7), (430, Int.negSucc 71), (442, Int.ofNat 40), (443, Int.ofNat 8),
    (448, Int.ofNat 8), (463, Int.ofNat 8), (480, Int.negSucc 47), (488, Int.negSucc 7), (495,
    Int.negSucc 7), (510, Int.negSucc 3), (516, Int.negSucc 19), (520, Int.negSucc 3), (524,
    Int.negSucc 3), (528, Int.ofNat 40), (535, Int.ofNat 4), (547, Int.ofNat 8), (550, Int.ofNat
    8), (556, Int.ofNat 2), (560, Int.ofNat 4), (709, Int.ofNat 32), (741, Int.negSucc 15), (766,
    Int.negSucc 23), (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat 16)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 8), (172, Int.ofNat 5), (481,
    Int.negSucc 39), (489, Int.negSucc 15), (500, Int.ofNat 36), (564, Int.negSucc 7), (578,
    Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 20), (767, Int.negSucc 7), (775,
    Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 1), (492, Int.negSucc 11), (501,
    Int.ofNat 12), (533, Int.negSucc 5), (567, Int.negSucc 5), (581, Int.ofNat 12), (742,
    Int.ofNat 12), (788, Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.ofNat 4), (130,
    Int.negSucc 0), (404, Int.ofNat 2), (412, Int.negSucc 3), (454, Int.negSucc 1), (478,
    Int.ofNat 4), (485, Int.negSucc 3), (493, Int.ofNat 4), (706, Int.negSucc 3), (780,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 3), (150, Int.ofNat 6), (151, Int.negSucc 1), (430,
    Int.ofNat 32), (442, Int.negSucc 7), (443, Int.negSucc 7), (448, Int.negSucc 7), (480,
    Int.ofNat 24), (488, Int.ofNat 8), (495, Int.ofNat 16), (516, Int.ofNat 8), (524, Int.ofNat
    8), (528, Int.negSucc 7), (535, Int.negSucc 3), (547, Int.negSucc 7), (550, Int.negSucc 7),
    (696, Int.negSucc 7), (709, Int.negSucc 15), (766, Int.ofNat 8), (774, Int.ofNat 8), (781,
    Int.negSucc 7), (787, Int.negSucc 7), (795, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (177,
    Int.ofNat 4), (481, Int.negSucc 23), (489, Int.negSucc 15), (496, Int.ofNat 8), (500,
    Int.ofNat 28), (564, Int.negSucc 7), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat
    12), (767, Int.negSucc 7), (775, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (180, Int.negSucc 3), (192,
    Int.ofNat 2), (470, Int.negSucc 11), (502, Int.ofNat 8), (517, Int.negSucc 3), (521,
    Int.negSucc 5), (541, Int.negSucc 3), (585, Int.ofNat 4), (590, Int.ofNat 8), (720, Int.ofNat
    4), (803, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 1), (181, Int.negSucc 3), (183,
    Int.ofNat 2), (484, Int.negSucc 11), (503, Int.ofNat 8), (529, Int.negSucc 7), (536,
    Int.negSucc 5), (545, Int.negSucc 3), (573, Int.negSucc 3), (593, Int.ofNat 8), (731,
    Int.ofNat 4), (796, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 44), (172, Int.ofNat 21), (481,
    Int.negSucc 151), (489, Int.negSucc 63), (500, Int.ofNat 132), (564, Int.negSucc 23), (578,
    Int.ofNat 48), (596, Int.ofNat 20), (710, Int.ofNat 60), (767, Int.negSucc 23), (775,
    Int.negSucc 23), (782, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 1), (473, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 56), (172, Int.ofNat 25), (177,
    Int.ofNat 4), (481, Int.negSucc 199), (489, Int.negSucc 79), (500, Int.ofNat 172), (564,
    Int.negSucc 31), (578, Int.ofNat 56), (596, Int.ofNat 28), (710, Int.ofNat 80), (767,
    Int.negSucc 31), (775, Int.negSucc 31), (782, Int.ofNat 32)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (125,
    Int.negSucc 3), (385, Int.negSucc 3), (396, Int.ofNat 4), (433, Int.ofNat 4), (479, Int.ofNat
    4), (486, Int.negSucc 3), (508, Int.ofNat 2), (707, Int.negSucc 3), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (148,
    Int.negSucc 3), (153, Int.negSucc 7), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 32), (442, Int.negSucc 7), (443, Int.negSucc 7), (463, Int.negSucc 7), (480,
    Int.ofNat 24), (488, Int.ofNat 8), (510, Int.ofNat 8), (516, Int.ofNat 4), (520, Int.ofNat 4),
    (528, Int.negSucc 15), (547, Int.negSucc 7), (556, Int.negSucc 3), (560, Int.negSucc 3), (696,
    Int.negSucc 7), (709, Int.negSucc 15), (766, Int.ofNat 8), (774, Int.ofNat 8), (781,
    Int.negSucc 7), (787, Int.negSucc 7), (802, Int.negSucc 7)] }
]

end VOA.DeligneAudit.D4Two.Certificate

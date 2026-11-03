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
def actionData311 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(105, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(367, Int.negSucc 0), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (380, Int.negSucc 7), (390,
    Int.ofNat 4), (421, Int.negSucc 7), (464, Int.negSucc 3), (475, Int.ofNat 8), (765, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(385, Int.negSucc 3), (479, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 11), (390, Int.ofNat 4), (421,
    Int.negSucc 11), (464, Int.negSucc 3), (475, Int.ofNat 8), (487, Int.ofNat 4), (765, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.ofNat 8), (429, Int.negSucc 23), (468,
    Int.negSucc 7), (482, Int.ofNat 8), (490, Int.ofNat 8), (695, Int.ofNat 8), (745, Int.negSucc
    7), (752, Int.negSucc 7), (759, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(375, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 7), (390, Int.ofNat 2), (421,
    Int.negSucc 5), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 2), (494, Int.ofNat
    2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(385, Int.negSucc 7), (396, Int.ofNat 2), (433,
    Int.negSucc 5), (471, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 7), (396, Int.ofNat 4), (433, Int.negSucc 7), (471,
    Int.negSucc 3), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 0), (478, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(407, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 7), (390, Int.ofNat 2), (421,
    Int.negSucc 5), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 2), (509, Int.ofNat
    1), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(399, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 3), (412, Int.ofNat 2), (454,
    Int.negSucc 2), (478, Int.negSucc 1), (485, Int.negSucc 1), (504, Int.ofNat 1), (512,
    Int.ofNat 2), (780, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 9), (396, Int.ofNat 2), (433,
    Int.negSucc 5), (471, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (508, Int.ofNat 1), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(404, Int.negSucc 4), (412, Int.ofNat 2), (454,
    Int.negSucc 2), (478, Int.negSucc 1), (485, Int.negSucc 1), (493, Int.negSucc 1), (504,
    Int.ofNat 1), (512, Int.ofNat 2), (780, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 1), (110, Int.negSucc 0), (120,
    Int.negSucc 1), (124, Int.ofNat 2), (380, Int.negSucc 9), (390, Int.ofNat 4), (421,
    Int.negSucc 5), (464, Int.negSucc 2), (475, Int.ofNat 6), (494, Int.ofNat 2), (509, Int.ofNat
    1), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 3), (125,
    Int.ofNat 4), (131, Int.negSucc 3), (385, Int.negSucc 19), (396, Int.ofNat 4), (433,
    Int.negSucc 3), (471, Int.negSucc 1), (479, Int.ofNat 12), (497, Int.ofNat 4), (508, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (126, Int.ofNat 4), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.negSucc 9), (412, Int.ofNat 4), (454,
    Int.negSucc 1), (478, Int.negSucc 11), (493, Int.negSucc 3), (504, Int.ofNat 1), (512,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (134,
    Int.ofNat 1), (404, Int.negSucc 3), (412, Int.ofNat 4), (454, Int.negSucc 3), (504, Int.ofNat
    2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1), (422, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (430, Int.negSucc 15), (442,
    Int.ofNat 8), (480, Int.negSucc 15), (516, Int.negSucc 7), (528, Int.ofNat 16), (766,
    Int.negSucc 7), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(437, Int.negSucc 5), (532, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 3), (465, Int.negSucc 1), (540,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 3), (476, Int.negSucc 3), (544,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (430, Int.negSucc 39), (442,
    Int.ofNat 8), (443, Int.ofNat 8), (480, Int.negSucc 31), (488, Int.negSucc 23), (516,
    Int.negSucc 7), (520, Int.negSucc 7), (528, Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat
    16), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760,
    Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat
    8)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.negSucc 1), (472, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 55), (442, Int.ofNat 8), (443, Int.ofNat
    8), (448, Int.ofNat 8), (480, Int.negSucc 31), (488, Int.negSucc 23), (495, Int.negSucc 15),
    (516, Int.negSucc 7), (520, Int.negSucc 7), (524, Int.negSucc 7), (528, Int.ofNat 16), (535,
    Int.ofNat 8), (547, Int.ofNat 16), (550, Int.ofNat 16), (696, Int.ofNat 8), (709, Int.ofNat
    8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15),
    (774, Int.negSucc 15), (781, Int.ofNat 8), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 3), (434, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 1), (434, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(155, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(458, Int.negSucc 2), (531, Int.negSucc 5)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.ofNat 1), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (160,
    Int.negSucc 1), (164, Int.ofNat 1), (430, Int.negSucc 55), (442, Int.ofNat 8), (443, Int.ofNat
    8), (463, Int.ofNat 8), (480, Int.negSucc 31), (488, Int.negSucc 23), (510, Int.negSucc 7),
    (516, Int.negSucc 7), (520, Int.negSucc 7), (528, Int.ofNat 16), (535, Int.ofNat 8), (547,
    Int.ofNat 16), (556, Int.ofNat 4), (560, Int.ofNat 8), (696, Int.ofNat 8), (709, Int.ofNat 8),
    (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774,
    Int.negSucc 7), (781, Int.ofNat 16), (787, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(451, Int.negSucc 1), (505, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 3), (455, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.negSucc 0)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 6), (148,
    Int.negSucc 8), (150, Int.ofNat 12), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (162, Int.negSucc 7), (430, Int.negSucc 71), (442, Int.ofNat 24), (448, Int.ofNat 8),
    (463, Int.ofNat 8), (480, Int.negSucc 47), (488, Int.negSucc 7), (495, Int.negSucc 7), (510,
    Int.negSucc 3), (516, Int.negSucc 19), (520, Int.negSucc 3), (524, Int.negSucc 3), (528,
    Int.ofNat 40), (535, Int.ofNat 4), (547, Int.ofNat 8), (550, Int.ofNat 8), (556, Int.ofNat 2),
    (560, Int.ofNat 4), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753,
    Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 23), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(481, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 8), (172, Int.ofNat 5), (481,
    Int.negSucc 55), (489, Int.negSucc 15), (500, Int.ofNat 28), (564, Int.negSucc 7), (578,
    Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 16), (767, Int.negSucc 7), (775,
    Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 1), (492, Int.negSucc 11), (501,
    Int.ofNat 6), (533, Int.negSucc 5), (567, Int.negSucc 5), (581, Int.ofNat 12), (788,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 1), (473, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (177,
    Int.ofNat 4), (481, Int.negSucc 23), (489, Int.negSucc 7), (500, Int.ofNat 20), (564,
    Int.negSucc 7), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 16), (767, Int.negSucc
    7), (775, Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (180, Int.negSucc 3), (192,
    Int.ofNat 2), (470, Int.negSucc 11), (502, Int.ofNat 4), (517, Int.negSucc 3), (521,
    Int.negSucc 5), (541, Int.negSucc 3), (585, Int.ofNat 4), (590, Int.ofNat 8), (803, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 1), (181, Int.negSucc 3), (183,
    Int.ofNat 2), (484, Int.negSucc 11), (503, Int.ofNat 4), (529, Int.negSucc 7), (536,
    Int.negSucc 5), (545, Int.negSucc 3), (573, Int.negSucc 3), (593, Int.ofNat 8), (796,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 44), (172, Int.ofNat 21), (481,
    Int.negSucc 135), (489, Int.negSucc 63), (500, Int.ofNat 108), (564, Int.negSucc 23), (578,
    Int.ofNat 48), (596, Int.ofNat 20), (710, Int.ofNat 48), (767, Int.negSucc 23), (775,
    Int.negSucc 23), (782, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 56), (172, Int.ofNat 25), (177,
    Int.ofNat 4), (481, Int.negSucc 175), (489, Int.negSucc 79), (496, Int.negSucc 7), (500,
    Int.ofNat 140), (564, Int.negSucc 31), (578, Int.ofNat 56), (596, Int.ofNat 28), (710,
    Int.ofNat 64), (767, Int.negSucc 31), (775, Int.negSucc 31), (782, Int.ofNat 32)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (177,
    Int.ofNat 1), (481, Int.negSucc 9), (489, Int.negSucc 3), (496, Int.negSucc 5), (500,
    Int.ofNat 8), (564, Int.negSucc 1), (578, Int.ofNat 2), (596, Int.ofNat 2), (710, Int.ofNat
    4), (767, Int.negSucc 1), (775, Int.negSucc 1), (782, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (185,
    Int.ofNat 8), (481, Int.negSucc 23), (489, Int.negSucc 7), (500, Int.ofNat 20), (564,
    Int.negSucc 3), (578, Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 16), (767,
    Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(187, Int.ofNat 4), (506, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 3), (172, Int.negSucc 2), (177,
    Int.ofNat 4), (185, Int.ofNat 8), (481, Int.negSucc 7), (489, Int.negSucc 7), (496, Int.ofNat
    8), (500, Int.ofNat 12), (511, Int.ofNat 4), (564, Int.negSucc 3), (578, Int.ofNat 8), (596,
    Int.ofNat 4), (710, Int.ofNat 16), (767, Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat
    8)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 1), (514, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 56), (172, Int.ofNat 25), (185,
    Int.ofNat 8), (481, Int.negSucc 175), (489, Int.negSucc 79), (500, Int.ofNat 140), (511,
    Int.negSucc 3), (564, Int.negSucc 27), (578, Int.ofNat 64), (596, Int.ofNat 28), (710,
    Int.ofNat 64), (767, Int.negSucc 31), (775, Int.negSucc 31), (782, Int.ofNat 32)] },
  { denominator := Int.ofNat 1, terms := [(187, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

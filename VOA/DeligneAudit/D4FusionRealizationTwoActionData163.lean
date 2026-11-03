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
def actionData163 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (131,
    Int.ofNat 4), (385, Int.ofNat 4), (396, Int.negSucc 3), (471, Int.ofNat 2), (479, Int.negSucc
    3), (508, Int.negSucc 1), (707, Int.ofNat 8), (738, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 2), (130, Int.negSucc 2), (132,
    Int.ofNat 4), (404, Int.ofNat 2), (412, Int.negSucc 3), (478, Int.ofNat 4), (493, Int.ofNat
    4), (504, Int.negSucc 0), (706, Int.negSucc 7), (735, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(401, Int.ofNat 2), (409, Int.negSucc 3), (733,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (411, Int.negSucc 3), (426,
    Int.negSucc 3), (734, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (134,
    Int.negSucc 0), (404, Int.ofNat 4), (412, Int.negSucc 7), (454, Int.ofNat 2), (504,
    Int.negSucc 1), (512, Int.negSucc 1), (735, Int.negSucc 3), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(77, Int.negSucc 3), (342, Int.negSucc 7), (381,
    Int.negSucc 3), (401, Int.negSucc 1), (405, Int.negSucc 0), (409, Int.ofNat 4), (685,
    Int.negSucc 3), (698, Int.negSucc 3), (733, Int.negSucc 3), (736, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(406, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(430, Int.ofNat 4), (442, Int.negSucc 3), (480,
    Int.ofNat 4), (516, Int.ofNat 2), (528, Int.negSucc 3), (709, Int.negSucc 1), (741, Int.ofNat
    2), (766, Int.ofNat 2), (787, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(431, Int.negSucc 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (396, Int.ofNat 4), (433, Int.negSucc 11), (471, Int.negSucc 3), (486,
    Int.ofNat 4), (497, Int.ofNat 4), (707, Int.negSucc 3), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.negSucc 0), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(112, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.negSucc 1), (740, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (430, Int.ofNat 16), (443,
    Int.negSucc 15), (480, Int.ofNat 8), (488, Int.ofNat 16), (520, Int.ofNat 8), (535,
    Int.negSucc 7), (547, Int.negSucc 7), (696, Int.negSucc 15), (709, Int.negSucc 15), (746,
    Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat
    8), (781, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 1), (472, Int.ofNat 1), (539,
    Int.negSucc 1), (718, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372, Int.ofNat
    2), (411, Int.ofNat 2), (426, Int.ofNat 2), (445, Int.negSucc 1), (692, Int.ofNat 2), (734,
    Int.ofNat 2), (758, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(115, Int.ofNat 1), (117, Int.negSucc 1), (391,
    Int.ofNat 8), (429, Int.negSucc 7), (447, Int.negSucc 3), (468, Int.negSucc 3), (482,
    Int.ofNat 6), (490, Int.ofNat 2), (695, Int.ofNat 12), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (148, Int.negSucc 0), (150,
    Int.ofNat 2), (151, Int.negSucc 1), (430, Int.ofNat 32), (443, Int.negSucc 15), (448,
    Int.negSucc 15), (480, Int.ofNat 8), (488, Int.ofNat 16), (495, Int.ofNat 8), (520, Int.ofNat
    8), (524, Int.ofNat 8), (535, Int.negSucc 7), (547, Int.negSucc 7), (550, Int.negSucc 7),
    (696, Int.negSucc 15), (709, Int.negSucc 15), (741, Int.negSucc 7), (746, Int.ofNat 8), (753,
    Int.ofNat 8), (766, Int.ofNat 8), (774, Int.ofNat 16), (781, Int.negSucc 7), (795, Int.negSucc
    7)] },
  { denominator := Int.ofNat 1, terms := [(437, Int.negSucc 0), (498, Int.negSucc 1), (532,
    Int.negSucc 0), (740, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(498, Int.negSucc 1), (740, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(452, Int.negSucc 0), (699, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (404,
    Int.negSucc 3), (412, Int.ofNat 4), (454, Int.negSucc 5), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 2), (706, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.negSucc 0), (455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(123, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(531, Int.ofNat 1), (739, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (357,
    Int.negSucc 3), (395, Int.negSucc 3), (427, Int.ofNat 4), (460, Int.negSucc 3), (693,
    Int.ofNat 4), (737, Int.ofNat 4), (751, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(115, Int.ofNat 1), (128, Int.negSucc 1), (391,
    Int.ofNat 8), (429, Int.negSucc 7), (462, Int.negSucc 3), (468, Int.negSucc 5), (482,
    Int.ofNat 4), (490, Int.ofNat 2), (695, Int.ofNat 12), (745, Int.negSucc 3), (752, Int.negSucc
    7), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (148, Int.negSucc 0), (160,
    Int.ofNat 2), (164, Int.negSucc 0), (430, Int.ofNat 32), (443, Int.negSucc 15), (463,
    Int.negSucc 15), (480, Int.ofNat 8), (488, Int.ofNat 16), (510, Int.ofNat 4), (520, Int.ofNat
    8), (535, Int.negSucc 7), (547, Int.negSucc 7), (556, Int.negSucc 3), (560, Int.negSucc 3),
    (696, Int.negSucc 15), (709, Int.negSucc 15), (741, Int.negSucc 7), (746, Int.ofNat 8), (760,
    Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat 8), (781, Int.negSucc 15), (802,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(451, Int.ofNat 1), (505, Int.ofNat 1), (543, Int.ofNat
    4), (728, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(458, Int.negSucc 0), (513, Int.negSucc 1), (531,
    Int.ofNat 2), (739, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(81, Int.ofNat 1), (86, Int.ofNat 2), (98, Int.negSucc
    7), (357, Int.negSucc 3), (384, Int.negSucc 7), (395, Int.negSucc 3), (416, Int.negSucc 3),
    (440, Int.negSucc 3), (460, Int.ofNat 4), (693, Int.negSucc 3), (737, Int.negSucc 3)] },
  { denominator := Int.ofNat 12, terms := [(112, Int.negSucc 0), (436, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(437, Int.negSucc 0), (498, Int.negSucc 1), (532,
    Int.negSucc 0), (740, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 1), (97, Int.ofNat 1), (99, Int.negSucc
    3), (372, Int.negSucc 1), (403, Int.negSucc 1), (411, Int.negSucc 1), (439, Int.ofNat 2),
    (445, Int.negSucc 1), (449, Int.ofNat 1), (692, Int.ofNat 2), (734, Int.ofNat 2)] },
  { denominator := Int.ofNat 6, terms := [(123, Int.negSucc 0), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 4, terms := [(458, Int.negSucc 0), (513, Int.negSucc 1), (531,
    Int.ofNat 2), (739, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 3), (100, Int.negSucc 4), (367,
    Int.negSucc 5), (431, Int.negSucc 5), (452, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 0), (407, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 2), (139, Int.negSucc 1), (143,
    Int.negSucc 3), (148, Int.ofNat 9), (150, Int.negSucc 11), (160, Int.negSucc 3), (162,
    Int.ofNat 8), (430, Int.ofNat 40), (442, Int.negSucc 15), (443, Int.negSucc 7), (448,
    Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 8), (516, Int.ofNat
    8), (520, Int.ofNat 4), (524, Int.ofNat 4), (528, Int.negSucc 15), (535, Int.negSucc 3), (547,
    Int.negSucc 7), (556, Int.negSucc 1), (709, Int.negSucc 15), (766, Int.ofNat 16), (774,
    Int.ofNat 8), (781, Int.negSucc 7), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.negSucc 0), (158, Int.ofNat 2), (437,
    Int.negSucc 1), (498, Int.negSucc 3), (532, Int.negSucc 3), (740, Int.ofNat 12)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.negSucc 1), (159, Int.ofNat 2), (458,
    Int.negSucc 0), (513, Int.negSucc 1), (531, Int.ofNat 4), (739, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(513, Int.negSucc 1), (739, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 11), (172, Int.negSucc 4), (481,
    Int.ofNat 40), (489, Int.ofNat 16), (500, Int.negSucc 35), (564, Int.ofNat 8), (578,
    Int.negSucc 15), (596, Int.negSucc 3), (710, Int.negSucc 19), (767, Int.ofNat 8), (775,
    Int.ofNat 8), (782, Int.negSucc 7)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.negSucc 0), (492, Int.ofNat 24), (501,
    Int.negSucc 23), (533, Int.ofNat 12), (567, Int.ofNat 12), (581, Int.negSucc 23), (742,
    Int.negSucc 23), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (412,
    Int.ofNat 4), (454, Int.ofNat 2), (485, Int.ofNat 4), (493, Int.negSucc 3), (735, Int.ofNat
    4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (148,
    Int.ofNat 4), (150, Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 15), (443, Int.ofNat
    8), (448, Int.ofNat 8), (495, Int.negSucc 15), (524, Int.negSucc 7), (535, Int.ofNat 4), (550,
    Int.ofNat 8), (696, Int.ofNat 8), (709, Int.ofNat 8), (741, Int.ofNat 8), (774, Int.negSucc
    7), (781, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 5), (172, Int.negSucc 0), (177,
    Int.negSucc 3), (481, Int.ofNat 32), (489, Int.ofNat 16), (496, Int.negSucc 7), (500,
    Int.negSucc 27), (564, Int.ofNat 8), (578, Int.negSucc 7), (596, Int.negSucc 3), (710,
    Int.negSucc 11), (767, Int.ofNat 8), (775, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(145, Int.negSucc 0), (532, Int.ofNat 2), (740,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.negSucc 0), (499, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (180, Int.ofNat 4), (192,
    Int.negSucc 1), (470, Int.ofNat 10), (502, Int.negSucc 7), (517, Int.ofNat 2), (521, Int.ofNat
    6), (585, Int.negSucc 3), (590, Int.negSucc 3), (755, Int.negSucc 3), (803, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (181, Int.ofNat 4), (183,
    Int.negSucc 1), (484, Int.ofNat 10), (503, Int.negSucc 7), (529, Int.ofNat 4), (536, Int.ofNat
    6), (573, Int.ofNat 4), (593, Int.negSucc 3), (762, Int.negSucc 3), (796, Int.ofNat 4)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.negSucc 0), (492, Int.ofNat 12), (501,
    Int.negSucc 23), (533, Int.ofNat 24), (548, Int.negSucc 23), (567, Int.ofNat 12), (581,
    Int.negSucc 23), (742, Int.negSucc 23), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 0), (492, Int.ofNat 12), (501,
    Int.negSucc 23), (533, Int.ofNat 24), (548, Int.negSucc 23), (551, Int.negSucc 23), (567,
    Int.ofNat 12), (581, Int.negSucc 23), (761, Int.negSucc 23), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.negSucc 0), (499, Int.negSucc 11)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (396,
    Int.negSucc 3), (433, Int.negSucc 3), (486, Int.ofNat 4), (508, Int.negSucc 1), (738,
    Int.ofNat 4), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (148,
    Int.ofNat 4), (160, Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 15), (443, Int.ofNat
    8), (463, Int.ofNat 8), (510, Int.negSucc 7), (520, Int.negSucc 3), (556, Int.ofNat 4), (560,
    Int.ofNat 4), (696, Int.ofNat 8), (709, Int.ofNat 8), (741, Int.ofNat 8), (774, Int.negSucc
    7), (781, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 5), (172, Int.negSucc 0), (185,
    Int.negSucc 7), (481, Int.ofNat 32), (489, Int.ofNat 16), (500, Int.negSucc 27), (511,
    Int.negSucc 3), (564, Int.ofNat 4), (578, Int.negSucc 15), (596, Int.negSucc 3), (710,
    Int.negSucc 11), (767, Int.ofNat 8), (782, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 0), (531, Int.negSucc 0), (739,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(189, Int.negSucc 0), (514, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 0), (492, Int.ofNat 12), (501,
    Int.negSucc 23), (533, Int.ofNat 24), (548, Int.negSucc 23), (561, Int.negSucc 11), (567,
    Int.ofNat 12), (581, Int.negSucc 23), (754, Int.ofNat 24), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(189, Int.negSucc 0), (514, Int.negSucc 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

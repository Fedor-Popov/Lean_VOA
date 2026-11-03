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
def actionData301 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (385, Int.negSucc 1), (433,
    Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2), (707, Int.negSucc 1), (738, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 12), (429,
    Int.negSucc 19), (468, Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 8), (695, Int.ofNat
    16), (745, Int.negSucc 7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (391, Int.ofNat 6), (429,
    Int.negSucc 11), (468, Int.negSucc 2), (482, Int.ofNat 4), (490, Int.ofNat 4), (695, Int.ofNat
    8), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4), (823, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 17), (396,
    Int.ofNat 12), (433, Int.negSucc 17), (471, Int.negSucc 5), (479, Int.ofNat 2), (486,
    Int.ofNat 4), (497, Int.ofNat 14), (707, Int.negSucc 5), (738, Int.ofNat 2), (773, Int.ofNat
    8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (72, Int.ofNat
    2), (346, Int.negSucc 1), (373, Int.negSucc 0), (377, Int.ofNat 2), (394, Int.ofNat 2), (691,
    Int.ofNat 2), (704, Int.ofNat 2), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(352, Int.negSucc 7), (379, Int.ofNat 8), (389,
    Int.negSucc 1), (413, Int.ofNat 3), (423, Int.negSucc 2), (428, Int.negSucc 1), (461,
    Int.ofNat 2), (694, Int.ofNat 4), (715, Int.negSucc 1), (744, Int.negSucc 3), (821, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1), (708, Int.negSucc 1), (716,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (366, Int.negSucc 1), (393, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.ofNat 1), (685,
    Int.negSucc 3), (698, Int.negSucc 3), (733, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(372, Int.negSucc 15), (403, Int.ofNat 8), (411,
    Int.negSucc 3), (426, Int.ofNat 4), (439, Int.negSucc 3), (449, Int.negSucc 2), (456,
    Int.negSucc 2), (692, Int.negSucc 7), (734, Int.negSucc 3), (758, Int.negSucc 7), (816,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (404, Int.negSucc 0), (454,
    Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1), (706, Int.ofNat 2), (735,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(128, Int.negSucc 0), (391, Int.ofNat 6), (429,
    Int.negSucc 11), (468, Int.negSucc 3), (482, Int.ofNat 3), (490, Int.ofNat 4), (695, Int.ofNat
    8), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4), (823, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.negSucc 0), (404, Int.negSucc 8), (412,
    Int.ofNat 12), (454, Int.negSucc 8), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 7), (706, Int.ofNat 6), (735, Int.negSucc 1), (780, Int.ofNat
    8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (59, Int.negSucc 0), (68,
    Int.negSucc 0), (72, Int.ofNat 1), (323, Int.negSucc 5), (346, Int.negSucc 0), (373, Int.ofNat
    1), (377, Int.negSucc 0), (383, Int.ofNat 1), (388, Int.ofNat 4), (394, Int.ofNat 3), (691,
    Int.ofNat 4), (704, Int.ofNat 6), (711, Int.negSucc 2), (714, Int.negSucc 1), (818,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357,
    Int.negSucc 27), (384, Int.ofNat 32), (395, Int.negSucc 3), (416, Int.ofNat 12), (427,
    Int.negSucc 7), (435, Int.negSucc 11), (440, Int.ofNat 2), (460, Int.ofNat 2), (693, Int.ofNat
    16), (712, Int.negSucc 1), (737, Int.ofNat 2), (751, Int.negSucc 15), (819, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(131, Int.negSucc 1), (385, Int.negSucc 19), (396,
    Int.ofNat 12), (433, Int.negSucc 19), (471, Int.negSucc 6), (479, Int.ofNat 2), (486,
    Int.ofNat 4), (497, Int.ofNat 14), (508, Int.ofNat 1), (707, Int.negSucc 7), (713, Int.negSucc
    1), (738, Int.ofNat 2), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 3), (66, Int.negSucc 1), (69,
    Int.negSucc 1), (73, Int.ofNat 2), (335, Int.negSucc 11), (361, Int.negSucc 0), (376,
    Int.ofNat 2), (387, Int.negSucc 7), (397, Int.negSucc 0), (402, Int.ofNat 1), (410, Int.ofNat
    6), (688, Int.negSucc 7), (701, Int.negSucc 11), (722, Int.negSucc 5), (725, Int.negSucc 3),
    (815, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372,
    Int.negSucc 13), (403, Int.ofNat 8), (411, Int.negSucc 1), (426, Int.ofNat 4), (439,
    Int.negSucc 0), (445, Int.negSucc 0), (449, Int.negSucc 2), (456, Int.negSucc 2), (692,
    Int.negSucc 7), (723, Int.negSucc 0), (734, Int.negSucc 0), (758, Int.negSucc 7), (816,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.negSucc 3), (404, Int.negSucc 19), (412,
    Int.ofNat 24), (454, Int.negSucc 19), (478, Int.negSucc 3), (485, Int.negSucc 7), (493,
    Int.negSucc 3), (504, Int.ofNat 7), (512, Int.ofNat 14), (706, Int.ofNat 16), (724,
    Int.negSucc 3), (735, Int.negSucc 3), (780, Int.ofNat 16), (817, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 7), (391, Int.ofNat 12), (429, Int.negSucc
    23), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 3), (482,
    Int.ofNat 4), (490, Int.ofNat 8), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc
    7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 1), (465,
    Int.negSucc 1), (540, Int.ofNat 2), (719, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 1), (476,
    Int.negSucc 3), (544, Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 15), (442, Int.ofNat 12), (480, Int.negSucc 15), (488, Int.negSucc 3), (516,
    Int.negSucc 5), (528, Int.ofNat 12), (547, Int.ofNat 4), (709, Int.ofNat 4), (741, Int.negSucc
    3), (766, Int.negSucc 7), (787, Int.ofNat 8), (824, Int.ofNat 4), (826, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (403, Int.ofNat 2), (411, Int.ofNat 4), (426, Int.ofNat 4), (449, Int.negSucc 0), (456,
    Int.negSucc 0), (692, Int.ofNat 4), (723, Int.ofNat 4), (734, Int.ofNat 4), (758, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 7), (429, Int.ofNat 10), (441,
    Int.negSucc 1), (447, Int.negSucc 1), (468, Int.ofNat 3), (482, Int.negSucc 2), (490,
    Int.negSucc 2), (695, Int.negSucc 5), (745, Int.ofNat 4), (752, Int.ofNat 4), (759,
    Int.negSucc 1), (823, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 0), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (495, Int.negSucc 1), (528, Int.ofNat 2), (550, Int.ofNat 2), (709, Int.ofNat
    2), (729, Int.negSucc 1), (741, Int.negSucc 1), (760, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 0), (437, Int.negSucc 1), (498,
    Int.negSucc 3), (532, Int.ofNat 2), (740, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (148, Int.negSucc 0), (430,
    Int.negSucc 47), (442, Int.ofNat 12), (443, Int.ofNat 24), (480, Int.negSucc 39), (488,
    Int.negSucc 35), (516, Int.negSucc 5), (520, Int.negSucc 11), (528, Int.ofNat 12), (535,
    Int.ofNat 12), (547, Int.ofNat 28), (696, Int.ofNat 28), (709, Int.ofNat 28), (741,
    Int.negSucc 3), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766,
    Int.negSucc 23), (774, Int.negSucc 15), (781, Int.ofNat 16), (787, Int.ofNat 8), (824,
    Int.ofNat 12), (826, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 1), (539, Int.ofNat 2), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (148, Int.ofNat 1), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 127), (442, Int.ofNat 24), (443,
    Int.ofNat 48), (448, Int.ofNat 24), (480, Int.negSucc 79), (488, Int.negSucc 79), (495,
    Int.negSucc 23), (516, Int.negSucc 11), (520, Int.negSucc 23), (524, Int.negSucc 11), (528,
    Int.ofNat 24), (535, Int.ofNat 28), (547, Int.ofNat 56), (550, Int.ofNat 24), (696, Int.ofNat
    56), (709, Int.ofNat 64), (729, Int.negSucc 7), (741, Int.negSucc 7), (746, Int.negSucc 31),
    (753, Int.negSucc 31), (760, Int.ofNat 32), (766, Int.negSucc 47), (774, Int.negSucc 47),
    (781, Int.ofNat 32), (787, Int.ofNat 16), (795, Int.ofNat 16), (824, Int.ofNat 32), (826,
    Int.negSucc 7), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (98, Int.negSucc 1), (102,
    Int.ofNat 2), (384, Int.negSucc 1), (395, Int.negSucc 1), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 1), (693, Int.ofNat 2), (712, Int.negSucc 1), (737, Int.ofNat
    2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(391, Int.negSucc 7), (429, Int.ofNat 10), (441,
    Int.negSucc 1), (462, Int.negSucc 1), (468, Int.ofNat 3), (482, Int.negSucc 2), (490,
    Int.negSucc 2), (695, Int.negSucc 5), (745, Int.ofNat 4), (752, Int.ofNat 2), (759,
    Int.negSucc 3), (823, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (430, Int.negSucc 1), (480,
    Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560, Int.ofNat 1), (709,
    Int.ofNat 2), (717, Int.ofNat 2), (741, Int.negSucc 1), (753, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 1), (458, Int.negSucc 0), (513,
    Int.negSucc 1), (531, Int.negSucc 1), (739, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (148, Int.ofNat 1), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 127), (442, Int.ofNat 24), (443,
    Int.ofNat 48), (463, Int.ofNat 24), (480, Int.negSucc 79), (488, Int.negSucc 79), (510,
    Int.negSucc 11), (516, Int.negSucc 11), (520, Int.negSucc 27), (528, Int.ofNat 24), (535,
    Int.ofNat 24), (547, Int.ofNat 56), (556, Int.ofNat 6), (560, Int.ofNat 12), (696, Int.ofNat
    56), (709, Int.ofNat 64), (717, Int.ofNat 8), (741, Int.negSucc 7), (746, Int.negSucc 31),
    (753, Int.negSucc 31), (760, Int.ofNat 32), (766, Int.negSucc 47), (774, Int.negSucc 31),
    (781, Int.ofNat 48), (787, Int.ofNat 16), (802, Int.ofNat 16), (824, Int.ofNat 32), (826,
    Int.negSucc 7), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.negSucc 0), (451, Int.negSucc 0), (505,
    Int.negSucc 0), (543, Int.negSucc 1), (728, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 3), (82, Int.ofNat 1), (85, Int.negSucc
    5), (95, Int.negSucc 1), (101, Int.ofNat 4), (352, Int.negSucc 23), (389, Int.negSucc 15),
    (413, Int.ofNat 4), (428, Int.ofNat 4), (446, Int.ofNat 12), (694, Int.ofNat 12), (715,
    Int.negSucc 3), (726, Int.ofNat 16), (744, Int.negSucc 11), (821, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.negSucc 27), (429, Int.ofNat 40), (441, Int.negSucc 1), (447, Int.negSucc 3), (462,
    Int.negSucc 1), (468, Int.ofNat 12), (482, Int.negSucc 13), (490, Int.negSucc 11), (695,
    Int.negSucc 27), (745, Int.ofNat 14), (752, Int.ofNat 16), (759, Int.negSucc 13), (823,
    Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

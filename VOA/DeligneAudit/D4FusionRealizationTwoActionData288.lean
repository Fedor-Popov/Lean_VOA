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
def actionData288 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(393, Int.negSucc 1), (685, Int.negSucc 1), (698,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (357, Int.ofNat
    8), (384, Int.negSucc 11), (395, Int.negSucc 3), (416, Int.negSucc 5), (427, Int.ofNat 4),
    (435, Int.ofNat 4), (693, Int.negSucc 7), (751, Int.ofNat 8), (819, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(385, Int.ofNat 6), (396, Int.negSucc 5), (433,
    Int.ofNat 6), (471, Int.ofNat 3), (486, Int.negSucc 1), (497, Int.negSucc 3), (707, Int.ofNat
    2), (773, Int.negSucc 3), (820, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(436, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(381, Int.ofNat 2), (393, Int.negSucc 1), (736,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (395, Int.negSucc 1), (427,
    Int.ofNat 2), (737, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (119,
    Int.negSucc 1), (385, Int.ofNat 12), (396, Int.negSucc 11), (433, Int.ofNat 8), (471,
    Int.ofNat 6), (497, Int.negSucc 7), (738, Int.ofNat 4), (773, Int.negSucc 7), (820, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(401, Int.negSucc 0), (685, Int.ofNat 2), (698,
    Int.ofNat 2), (733, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(372, Int.ofNat 12), (403, Int.negSucc 5), (426,
    Int.negSucc 3), (439, Int.ofNat 4), (449, Int.ofNat 3), (456, Int.ofNat 2), (692, Int.ofNat
    8), (734, Int.ofNat 4), (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(478, Int.ofNat 1), (706, Int.negSucc 0), (735,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(94, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(409, Int.negSucc 1), (685, Int.ofNat 2), (698,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (97, Int.negSucc 1), (372, Int.ofNat
    8), (403, Int.negSucc 5), (411, Int.negSucc 3), (426, Int.negSucc 3), (449, Int.ofNat 3),
    (456, Int.ofNat 2), (692, Int.ofNat 8), (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(404, Int.ofNat 6), (412, Int.negSucc 11), (454,
    Int.ofNat 6), (485, Int.ofNat 4), (504, Int.negSucc 2), (512, Int.negSucc 3), (706,
    Int.negSucc 3), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(457, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(62, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(59, Int.ofNat 1), (68, Int.negSucc 1), (323,
    Int.negSucc 5), (346, Int.ofNat 2), (373, Int.ofNat 2), (388, Int.negSucc 1), (459,
    Int.negSucc 1), (691, Int.negSucc 1), (711, Int.negSucc 1), (714, Int.negSucc 3), (818,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(81, Int.ofNat 1), (98, Int.negSucc 3), (357, Int.ofNat
    8), (384, Int.negSucc 15), (395, Int.negSucc 3), (416, Int.negSucc 7), (427, Int.ofNat 4),
    (435, Int.ofNat 4), (693, Int.negSucc 11), (712, Int.ofNat 4), (751, Int.ofNat 8), (819,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.ofNat 6), (396, Int.negSucc 5), (433,
    Int.ofNat 6), (471, Int.ofNat 3), (486, Int.negSucc 1), (497, Int.negSucc 3), (508,
    Int.negSucc 0), (707, Int.ofNat 4), (713, Int.ofNat 2), (773, Int.negSucc 3), (820, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(76, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.ofNat 1), (69, Int.negSucc 1), (335,
    Int.negSucc 5), (361, Int.ofNat 1), (387, Int.ofNat 2), (397, Int.negSucc 0), (444, Int.ofNat
    2), (688, Int.ofNat 2), (722, Int.negSucc 1), (725, Int.negSucc 3), (815, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 1), (99, Int.negSucc 1), (372, Int.ofNat
    4), (403, Int.negSucc 3), (411, Int.negSucc 1), (426, Int.negSucc 1), (449, Int.ofNat 2),
    (456, Int.ofNat 1), (692, Int.ofNat 6), (723, Int.ofNat 2), (758, Int.ofNat 4), (816,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(404, Int.ofNat 6), (412, Int.negSucc 11), (454,
    Int.ofNat 6), (485, Int.ofNat 4), (493, Int.ofNat 4), (504, Int.negSucc 2), (512, Int.negSucc
    3), (706, Int.negSucc 7), (724, Int.ofNat 4), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 2), (70, Int.negSucc 7), (342, Int.ofNat
    4), (366, Int.negSucc 9), (393, Int.negSucc 3), (405, Int.ofNat 3), (409, Int.ofNat 4), (438,
    Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 8), (733, Int.ofNat 8), (736, Int.ofNat
    8), (814, Int.negSucc 3)] },
  { denominator := Int.ofNat 12, terms := [(94, Int.negSucc 1), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 4, terms := [(407, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 3), (342, Int.negSucc 5), (366,
    Int.ofNat 1), (381, Int.ofNat 2), (393, Int.negSucc 1), (401, Int.ofNat 1), (405, Int.negSucc
    0), (685, Int.negSucc 1), (698, Int.negSucc 3), (733, Int.negSucc 3), (736, Int.negSucc 3),
    (814, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(406, Int.ofNat 1)] },
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
    Int.negSucc 0), (404, Int.ofNat 6), (412, Int.negSucc 11), (454, Int.ofNat 4), (504,
    Int.negSucc 2), (512, Int.negSucc 3), (735, Int.negSucc 3), (780, Int.negSucc 7), (817,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 1), (342, Int.negSucc 5), (366,
    Int.ofNat 1), (381, Int.negSucc 1), (401, Int.negSucc 0), (405, Int.negSucc 0), (409,
    Int.ofNat 2), (685, Int.negSucc 1), (698, Int.negSucc 3), (733, Int.negSucc 3), (736,
    Int.negSucc 3), (814, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(406, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(430, Int.ofNat 6), (442, Int.negSucc 5), (480,
    Int.ofNat 6), (516, Int.ofNat 3), (528, Int.negSucc 5), (709, Int.negSucc 1), (741, Int.ofNat
    2), (766, Int.ofNat 4), (787, Int.negSucc 3), (824, Int.negSucc 1), (826, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(431, Int.negSucc 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 11), (396, Int.ofNat 8), (433, Int.negSucc 15), (471, Int.negSucc 5), (486,
    Int.ofNat 4), (497, Int.ofNat 8), (707, Int.negSucc 3), (773, Int.ofNat 8), (820, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.negSucc 0), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(112, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.negSucc 1), (740, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (430, Int.ofNat 12), (443,
    Int.negSucc 11), (480, Int.ofNat 8), (488, Int.ofNat 12), (520, Int.ofNat 6), (535,
    Int.negSucc 5), (547, Int.negSucc 7), (696, Int.negSucc 13), (709, Int.negSucc 11), (746,
    Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 8), (774, Int.ofNat
    8), (781, Int.negSucc 7), (824, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 1), (472, Int.ofNat 1), (539,
    Int.negSucc 1), (718, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372, Int.ofNat
    2), (411, Int.ofNat 2), (426, Int.ofNat 2), (445, Int.negSucc 1), (692, Int.ofNat 2), (734,
    Int.ofNat 2), (758, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(115, Int.ofNat 1), (117, Int.negSucc 1), (391,
    Int.ofNat 12), (429, Int.negSucc 11), (447, Int.negSucc 3), (468, Int.negSucc 5), (482,
    Int.ofNat 8), (490, Int.ofNat 4), (695, Int.ofNat 20), (745, Int.negSucc 7), (752, Int.negSucc
    7), (759, Int.ofNat 12), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 2), (148, Int.negSucc 0), (150,
    Int.ofNat 2), (151, Int.negSucc 1), (430, Int.ofNat 48), (443, Int.negSucc 23), (448,
    Int.negSucc 23), (480, Int.ofNat 16), (488, Int.ofNat 24), (495, Int.ofNat 16), (520,
    Int.ofNat 12), (524, Int.ofNat 12), (535, Int.negSucc 11), (547, Int.negSucc 15), (550,
    Int.negSucc 15), (696, Int.negSucc 27), (709, Int.negSucc 23), (741, Int.negSucc 7), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 7), (766, Int.ofNat 16), (774, Int.ofNat
    32), (781, Int.negSucc 15), (795, Int.negSucc 15), (824, Int.negSucc 15), (829, Int.ofNat 8)]
    },
  { denominator := Int.ofNat 1, terms := [(437, Int.negSucc 0), (498, Int.negSucc 1), (532,
    Int.negSucc 0), (740, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(498, Int.negSucc 1), (740, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(452, Int.negSucc 0), (699, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (404,
    Int.negSucc 5), (412, Int.ofNat 8), (454, Int.negSucc 7), (485, Int.negSucc 3), (504,
    Int.ofNat 3), (512, Int.ofNat 4), (706, Int.ofNat 4), (780, Int.ofNat 8), (817, Int.ofNat 4)]
    },
  { denominator := Int.ofNat 2, terms := [(155, Int.negSucc 0), (455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(123, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(531, Int.ofNat 1), (739, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (357,
    Int.negSucc 3), (395, Int.negSucc 3), (427, Int.ofNat 4), (460, Int.negSucc 3), (693,
    Int.ofNat 4), (737, Int.ofNat 4), (751, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(115, Int.ofNat 1), (128, Int.negSucc 1), (391,
    Int.ofNat 12), (429, Int.negSucc 11), (462, Int.negSucc 3), (468, Int.negSucc 7), (482,
    Int.ofNat 6), (490, Int.ofNat 4), (695, Int.ofNat 20), (745, Int.negSucc 7), (752, Int.negSucc
    11), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 2), (148, Int.negSucc 0), (160,
    Int.ofNat 2), (164, Int.negSucc 0), (430, Int.ofNat 48), (443, Int.negSucc 23), (463,
    Int.negSucc 23), (480, Int.ofNat 16), (488, Int.ofNat 24), (510, Int.ofNat 8), (520, Int.ofNat
    12), (535, Int.negSucc 11), (547, Int.negSucc 15), (556, Int.negSucc 5), (560, Int.negSucc 7),
    (696, Int.negSucc 27), (709, Int.negSucc 23), (741, Int.negSucc 7), (746, Int.ofNat 16), (753,
    Int.ofNat 8), (760, Int.negSucc 15), (766, Int.ofNat 16), (774, Int.ofNat 16), (781,
    Int.negSucc 31), (802, Int.negSucc 15), (824, Int.negSucc 15), (832, Int.ofNat 8)] },
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
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 3), (139, Int.negSucc 1), (143,
    Int.negSucc 3), (148, Int.ofNat 9), (150, Int.negSucc 11), (160, Int.negSucc 3), (162,
    Int.ofNat 8), (430, Int.ofNat 56), (442, Int.negSucc 23), (443, Int.negSucc 15), (448,
    Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 40), (488, Int.ofNat 16), (516,
    Int.ofNat 12), (520, Int.ofNat 8), (524, Int.ofNat 4), (528, Int.negSucc 23), (535,
    Int.negSucc 7), (547, Int.negSucc 15), (556, Int.negSucc 1), (696, Int.negSucc 3), (709,
    Int.negSucc 23), (746, Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat
    32), (774, Int.ofNat 16), (781, Int.negSucc 15), (787, Int.negSucc 15), (824, Int.negSucc 23),
    (826, Int.ofNat 16), (829, Int.ofNat 8), (832, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.negSucc 0), (158, Int.ofNat 2), (437,
    Int.negSucc 1), (498, Int.negSucc 3), (532, Int.negSucc 3), (740, Int.ofNat 12)] }
]

end VOA.DeligneAudit.D4Two.Certificate

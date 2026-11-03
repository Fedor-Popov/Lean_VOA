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
def actionData430 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    7), (342, Int.ofNat 16), (366, Int.negSucc 9), (393, Int.ofNat 4), (405, Int.ofNat 5), (409,
    Int.negSucc 3), (438, Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 12), (733, Int.ofNat
    12), (736, Int.ofNat 12), (814, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 3), (35, Int.ofNat 4), (340, Int.ofNat
    4), (353, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(334, Int.negSucc 3), (349, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.negSucc 0), (361, Int.negSucc 1), (376,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.negSucc 0), (400, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (35, Int.ofNat 2), (332, Int.ofNat
    2), (348, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(341, Int.negSucc 1), (354, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 0), (366, Int.negSucc 0), (381,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 0), (379, Int.negSucc 1), (428,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (327, Int.ofNat 1), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 0), (408,
    Int.ofNat 2), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(323, Int.negSucc 9), (346, Int.ofNat 8), (373,
    Int.ofNat 4), (377, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat
    2), (691, Int.ofNat 2), (704, Int.ofNat 8), (711, Int.negSucc 5), (714, Int.negSucc 5), (818,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (347, Int.negSucc 1), (420,
    Int.ofNat 2), (432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (49, Int.negSucc 1), (369,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(356, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (384, Int.negSucc 3), (435,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (352, Int.ofNat 16), (379,
    Int.negSucc 19), (413, Int.negSucc 7), (423, Int.ofNat 8), (428, Int.ofNat 4), (694,
    Int.negSucc 11), (744, Int.ofNat 12), (821, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.negSucc 0), (374, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (51, Int.negSucc 1), (334, Int.ofNat
    2), (349, Int.ofNat 2), (370, Int.negSucc 3), (687, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.negSucc 0), (352, Int.ofNat 8), (379,
    Int.negSucc 11), (413, Int.negSucc 3), (423, Int.ofNat 5), (428, Int.ofNat 2), (694,
    Int.negSucc 5), (744, Int.ofNat 6), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (357, Int.ofNat 8), (384,
    Int.negSucc 11), (416, Int.negSucc 3), (427, Int.ofNat 2), (435, Int.ofNat 5), (693,
    Int.negSucc 5), (751, Int.ofNat 6), (819, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (44, Int.negSucc 1), (48, Int.ofNat
    2), (327, Int.negSucc 0), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (392,
    Int.ofNat 2), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(335, Int.negSucc 9), (361, Int.ofNat 4), (376,
    Int.ofNat 2), (387, Int.negSucc 1), (397, Int.negSucc 1), (402, Int.negSucc 0), (410,
    Int.ofNat 2), (688, Int.negSucc 1), (701, Int.negSucc 7), (722, Int.negSucc 5), (725,
    Int.negSucc 5), (815, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (362, Int.negSucc 0), (419,
    Int.negSucc 1), (453, Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0), (49, Int.ofNat 1), (354,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(371, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (403, Int.negSucc 1), (456,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.negSucc 1), (406, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.negSucc 1), (50, Int.ofNat 2), (322,
    Int.negSucc 1), (350, Int.ofNat 2), (355, Int.ofNat 4), (690, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(95, Int.negSucc 0), (352, Int.ofNat 8), (379,
    Int.negSucc 11), (413, Int.negSucc 4), (423, Int.ofNat 4), (428, Int.ofNat 2), (694,
    Int.negSucc 5), (744, Int.ofNat 6), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.negSucc 1), (398, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (372, Int.ofNat 16), (403,
    Int.negSucc 11), (426, Int.negSucc 3), (449, Int.ofNat 4), (456, Int.ofNat 5), (692, Int.ofNat
    12), (758, Int.ofNat 12), (816, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.negSucc 0), (50, Int.ofNat 1), (322,
    Int.negSucc 1), (350, Int.ofNat 2), (355, Int.ofNat 2), (690, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(60, Int.ofNat 1), (356, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(98, Int.negSucc 1), (357, Int.ofNat 8), (384,
    Int.negSucc 13), (416, Int.negSucc 4), (427, Int.ofNat 2), (435, Int.ofNat 5), (693,
    Int.negSucc 5), (751, Int.ofNat 6), (819, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.negSucc 0), (51, Int.ofNat 1), (334,
    Int.negSucc 1), (349, Int.negSucc 1), (370, Int.ofNat 2), (687, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(67, Int.ofNat 1), (371, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(99, Int.negSucc 3), (372, Int.ofNat 16), (403,
    Int.negSucc 13), (426, Int.negSucc 3), (449, Int.ofNat 5), (456, Int.ofNat 5), (692, Int.ofNat
    12), (758, Int.ofNat 12), (816, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 5), (44, Int.negSucc 5), (48, Int.ofNat
    6), (316, Int.negSucc 9), (327, Int.negSucc 0), (343, Int.negSucc 5), (359, Int.ofNat 3),
    (365, Int.ofNat 3), (386, Int.ofNat 6), (392, Int.ofNat 2), (408, Int.negSucc 1), (682,
    Int.ofNat 10), (697, Int.negSucc 9), (700, Int.negSucc 5), (703, Int.negSucc 5), (813,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (342, Int.negSucc 59), (366, Int.ofNat 20), (381, Int.ofNat 8), (393, Int.negSucc 11),
    (401, Int.negSucc 3), (405, Int.negSucc 10), (409, Int.ofNat 12), (438, Int.ofNat 4), (685,
    Int.negSucc 11), (698, Int.negSucc 43), (733, Int.negSucc 35), (736, Int.negSucc 35), (814,
    Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(100, Int.negSucc 1), (367, Int.negSucc 2), (431,
    Int.negSucc 3), (452, Int.ofNat 2), (699, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 7), (352, Int.ofNat 16), (379, Int.negSucc 19), (389,
    Int.ofNat 4), (413, Int.negSucc 5), (423, Int.ofNat 6), (428, Int.ofNat 8), (446, Int.negSucc
    3), (461, Int.negSucc 3), (694, Int.negSucc 7), (744, Int.ofNat 12), (821, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    3), (357, Int.ofNat 8), (384, Int.negSucc 11), (395, Int.ofNat 2), (416, Int.negSucc 2), (427,
    Int.ofNat 2), (435, Int.ofNat 5), (440, Int.negSucc 1), (460, Int.negSucc 1), (693,
    Int.negSucc 3), (751, Int.ofNat 6), (819, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    7), (372, Int.ofNat 16), (403, Int.negSucc 11), (411, Int.ofNat 4), (426, Int.negSucc 3),
    (439, Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 3), (456, Int.ofNat 5), (692,
    Int.ofNat 8), (758, Int.ofNat 12), (816, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 19), (390, Int.ofNat 16), (421, Int.negSucc 19), (464, Int.negSucc 7), (475,
    Int.ofNat 16), (487, Int.ofNat 4), (708, Int.negSucc 3), (765, Int.ofNat 12), (822,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (361, Int.ofNat 2), (376, Int.ofNat 4), (397, Int.negSucc 0), (410, Int.negSucc 3), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 9), (379, Int.ofNat 10), (389,
    Int.negSucc 1), (413, Int.ofNat 4), (423, Int.negSucc 3), (428, Int.negSucc 1), (446,
    Int.ofNat 2), (694, Int.ofNat 6), (726, Int.ofNat 2), (744, Int.negSucc 5), (821, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2), (708, Int.negSucc 1), (727, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (366, Int.ofNat 2), (381, Int.ofNat 4), (405, Int.negSucc 0), (409, Int.negSucc 3), (685,
    Int.ofNat 4), (698, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 9), (384, Int.ofNat 10), (395,
    Int.negSucc 1), (416, Int.ofNat 4), (427, Int.negSucc 1), (435, Int.negSucc 3), (440,
    Int.ofNat 2), (693, Int.ofNat 6), (737, Int.ofNat 2), (751, Int.negSucc 5), (819, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (385, Int.negSucc 1), (433,
    Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2), (707, Int.negSucc 1), (738, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 16), (429,
    Int.negSucc 23), (468, Int.negSucc 7), (482, Int.ofNat 8), (490, Int.ofNat 10), (695,
    Int.ofNat 24), (745, Int.negSucc 11), (752, Int.negSucc 11), (759, Int.ofNat 12), (823,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (391, Int.ofNat 8), (429,
    Int.negSucc 13), (468, Int.negSucc 3), (482, Int.ofNat 5), (490, Int.ofNat 5), (695, Int.ofNat
    12), (745, Int.negSucc 5), (752, Int.negSucc 5), (759, Int.ofNat 6), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 21), (396,
    Int.ofNat 16), (433, Int.negSucc 21), (471, Int.negSucc 7), (479, Int.ofNat 2), (486,
    Int.ofNat 4), (497, Int.ofNat 18), (707, Int.negSucc 5), (738, Int.ofNat 2), (773, Int.ofNat
    12), (820, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (72, Int.ofNat
    2), (346, Int.negSucc 1), (373, Int.negSucc 0), (377, Int.ofNat 2), (394, Int.ofNat 2), (691,
    Int.ofNat 2), (704, Int.ofNat 2), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 4), (379, Int.ofNat 5), (389,
    Int.negSucc 0), (413, Int.ofNat 2), (423, Int.negSucc 1), (428, Int.negSucc 0), (461,
    Int.ofNat 1), (694, Int.ofNat 3), (715, Int.negSucc 0), (744, Int.negSucc 2), (821, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1), (708, Int.negSucc 1), (716,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (366, Int.negSucc 1), (393, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.ofNat 1), (685,
    Int.negSucc 3), (698, Int.negSucc 3), (733, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(372, Int.negSucc 9), (403, Int.ofNat 5), (411,
    Int.negSucc 1), (426, Int.ofNat 2), (439, Int.negSucc 1), (449, Int.negSucc 1), (456,
    Int.negSucc 1), (692, Int.negSucc 5), (734, Int.negSucc 1), (758, Int.negSucc 5), (816,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (404, Int.negSucc 0), (454,
    Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1), (706, Int.ofNat 2), (735,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(128, Int.negSucc 0), (391, Int.ofNat 8), (429,
    Int.negSucc 13), (468, Int.negSucc 4), (482, Int.ofNat 4), (490, Int.ofNat 5), (695, Int.ofNat
    12), (745, Int.negSucc 5), (752, Int.negSucc 5), (759, Int.ofNat 6), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.negSucc 0), (404, Int.negSucc 10), (412,
    Int.ofNat 16), (454, Int.negSucc 10), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 4), (512, Int.ofNat 9), (706, Int.ofNat 6), (735, Int.negSucc 1), (780, Int.ofNat
    12), (817, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 1), (59, Int.negSucc 1), (68,
    Int.negSucc 1), (72, Int.ofNat 2), (323, Int.negSucc 13), (373, Int.ofNat 3), (377,
    Int.negSucc 1), (383, Int.ofNat 2), (388, Int.ofNat 8), (394, Int.ofNat 6), (691, Int.ofNat
    8), (704, Int.ofNat 14), (711, Int.negSucc 7), (714, Int.negSucc 5), (818, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357,
    Int.negSucc 35), (384, Int.ofNat 40), (395, Int.negSucc 3), (416, Int.ofNat 16), (427,
    Int.negSucc 7), (435, Int.negSucc 15), (440, Int.ofNat 2), (460, Int.ofNat 2), (693, Int.ofNat
    24), (712, Int.negSucc 1), (737, Int.ofNat 2), (751, Int.negSucc 23), (819, Int.ofNat 16)] },
  { denominator := Int.ofNat 2, terms := [(131, Int.negSucc 1), (385, Int.negSucc 23), (396,
    Int.ofNat 16), (433, Int.negSucc 23), (471, Int.negSucc 8), (479, Int.ofNat 2), (486,
    Int.ofNat 4), (497, Int.ofNat 18), (508, Int.ofNat 1), (707, Int.negSucc 7), (713, Int.negSucc
    1), (738, Int.ofNat 2), (773, Int.ofNat 12), (820, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 7), (66, Int.negSucc 3), (69,
    Int.negSucc 3), (73, Int.ofNat 4), (335, Int.negSucc 27), (376, Int.ofNat 4), (387,
    Int.negSucc 15), (397, Int.negSucc 2), (402, Int.ofNat 2), (410, Int.ofNat 12), (688,
    Int.negSucc 15), (701, Int.negSucc 27), (722, Int.negSucc 15), (725, Int.negSucc 11), (815,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372,
    Int.negSucc 17), (403, Int.ofNat 10), (411, Int.negSucc 1), (426, Int.ofNat 4), (439,
    Int.negSucc 0), (445, Int.negSucc 0), (449, Int.negSucc 3), (456, Int.negSucc 3), (692,
    Int.negSucc 11), (723, Int.negSucc 0), (734, Int.negSucc 0), (758, Int.negSucc 11), (816,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.negSucc 3), (404, Int.negSucc 23), (412,
    Int.ofNat 32), (454, Int.negSucc 23), (478, Int.negSucc 3), (485, Int.negSucc 7), (493,
    Int.negSucc 3), (504, Int.ofNat 9), (512, Int.ofNat 18), (706, Int.ofNat 16), (724,
    Int.negSucc 3), (735, Int.negSucc 3), (780, Int.ofNat 24), (817, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 7), (391, Int.ofNat 16), (429, Int.negSucc
    27), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 6), (490, Int.ofNat 10), (695, Int.ofNat 20), (745, Int.negSucc 11), (752,
    Int.negSucc 11), (759, Int.ofNat 12), (823, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 1), (465,
    Int.negSucc 1), (540, Int.ofNat 2), (719, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 1), (476,
    Int.negSucc 3), (544, Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 19), (442, Int.ofNat 16), (480, Int.negSucc 19), (488, Int.negSucc 3), (516,
    Int.negSucc 7), (528, Int.ofNat 16), (547, Int.ofNat 4), (709, Int.ofNat 4), (741, Int.negSucc
    3), (766, Int.negSucc 11), (787, Int.ofNat 12), (824, Int.ofNat 8), (826, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData174 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0), (49, Int.ofNat 1), (341,
    Int.negSucc 1), (354, Int.negSucc 1), (369, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (366, Int.negSucc 1), (405,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (30, Int.ofNat 2), (308, Int.ofNat
    2), (319, Int.negSucc 1), (332, Int.ofNat 2), (340, Int.ofNat 2), (353, Int.ofNat 2), (686,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(334, Int.negSucc 1), (349, Int.negSucc 1), (370,
    Int.ofNat 2), (687, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (335, Int.ofNat 4), (361,
    Int.negSucc 2), (376, Int.negSucc 1), (397, Int.ofNat 1), (402, Int.ofNat 1), (701, Int.ofNat
    2), (722, Int.ofNat 2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(23, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(22, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.negSucc 0), (50, Int.ofNat 2), (322,
    Int.negSucc 3), (350, Int.ofNat 4), (355, Int.ofNat 4), (690, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(68, Int.negSucc 1), (323, Int.ofNat 4), (346,
    Int.negSucc 7), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(32, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(25, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.negSucc 0), (51, Int.ofNat 2), (334,
    Int.negSucc 3), (349, Int.negSucc 3), (370, Int.ofNat 4), (687, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(69, Int.negSucc 3), (335, Int.ofNat 8), (361,
    Int.negSucc 7), (376, Int.negSucc 3), (397, Int.ofNat 3), (402, Int.ofNat 2), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (29, Int.ofNat 1), (30, Int.ofNat
    1), (308, Int.ofNat 1), (315, Int.negSucc 0), (319, Int.negSucc 1), (332, Int.ofNat 2), (340,
    Int.ofNat 2), (348, Int.ofNat 1), (353, Int.ofNat 1), (368, Int.negSucc 0), (683, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(45, Int.negSucc 0), (49, Int.ofNat 1), (341,
    Int.negSucc 3), (354, Int.negSucc 3), (369, Int.ofNat 4), (684, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(70, Int.negSucc 3), (342, Int.ofNat 8), (366,
    Int.negSucc 7), (381, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.ofNat 3), (698, Int.ofNat
    4), (733, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 0), (31, Int.ofNat 1), (319,
    Int.negSucc 0), (348, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(341, Int.negSucc 0), (369, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 1), (366, Int.negSucc 0), (401,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    3), (323, Int.ofNat 4), (346, Int.negSucc 3), (373, Int.negSucc 0), (383, Int.ofNat 2), (388,
    Int.negSucc 1), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    7), (335, Int.ofNat 8), (361, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 1), (402,
    Int.ofNat 2), (410, Int.negSucc 3), (444, Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    7), (342, Int.ofNat 8), (366, Int.negSucc 5), (393, Int.ofNat 4), (405, Int.ofNat 3), (409,
    Int.negSucc 3), (438, Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 4), (733, Int.ofNat
    4), (736, Int.ofNat 4)] },
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
  { denominator := Int.ofNat 1, terms := [(323, Int.negSucc 5), (346, Int.ofNat 4), (373,
    Int.ofNat 2), (377, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat
    2), (691, Int.ofNat 2), (704, Int.ofNat 4), (711, Int.negSucc 1), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (347, Int.negSucc 1), (420,
    Int.ofNat 2), (432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (49, Int.negSucc 1), (369,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(356, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (384, Int.negSucc 3), (435,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (352, Int.ofNat 8), (379,
    Int.negSucc 11), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 4), (694,
    Int.negSucc 3), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.negSucc 0), (374, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (51, Int.negSucc 1), (334, Int.ofNat
    2), (349, Int.ofNat 2), (370, Int.negSucc 3), (687, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.negSucc 0), (352, Int.ofNat 4), (379,
    Int.negSucc 7), (413, Int.negSucc 1), (423, Int.ofNat 3), (428, Int.ofNat 2), (694,
    Int.negSucc 1), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (357, Int.ofNat 4), (384,
    Int.negSucc 7), (416, Int.negSucc 1), (427, Int.ofNat 2), (435, Int.ofNat 3), (693,
    Int.negSucc 1), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (44, Int.negSucc 1), (48, Int.ofNat
    2), (327, Int.negSucc 0), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (392,
    Int.ofNat 2), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(335, Int.negSucc 5), (361, Int.ofNat 2), (376,
    Int.ofNat 2), (387, Int.negSucc 1), (397, Int.negSucc 0), (402, Int.negSucc 0), (410,
    Int.ofNat 2), (688, Int.negSucc 1), (701, Int.negSucc 3), (722, Int.negSucc 1), (725,
    Int.negSucc 1)] },
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
  { denominator := Int.ofNat 1, terms := [(95, Int.negSucc 0), (352, Int.ofNat 4), (379,
    Int.negSucc 7), (413, Int.negSucc 2), (423, Int.ofNat 2), (428, Int.ofNat 2), (694,
    Int.negSucc 1), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.negSucc 1), (398, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (372, Int.ofNat 8), (403,
    Int.negSucc 7), (426, Int.negSucc 3), (449, Int.ofNat 2), (456, Int.ofNat 3), (692, Int.ofNat
    4), (758, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.negSucc 0), (50, Int.ofNat 1), (322,
    Int.negSucc 1), (350, Int.ofNat 2), (355, Int.ofNat 2), (690, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(60, Int.ofNat 1), (356, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(98, Int.negSucc 1), (357, Int.ofNat 4), (384,
    Int.negSucc 9), (416, Int.negSucc 2), (427, Int.ofNat 2), (435, Int.ofNat 3), (693,
    Int.negSucc 1), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.negSucc 0), (51, Int.ofNat 1), (334,
    Int.negSucc 1), (349, Int.negSucc 1), (370, Int.ofNat 2), (687, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(67, Int.ofNat 1), (371, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(99, Int.negSucc 3), (372, Int.ofNat 8), (403,
    Int.negSucc 9), (426, Int.negSucc 3), (449, Int.ofNat 3), (456, Int.ofNat 3), (692, Int.ofNat
    4), (758, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 5), (44, Int.negSucc 5), (48, Int.ofNat
    6), (316, Int.negSucc 5), (327, Int.negSucc 2), (343, Int.negSucc 5), (359, Int.ofNat 3),
    (365, Int.ofNat 3), (386, Int.ofNat 6), (392, Int.ofNat 2), (408, Int.negSucc 1), (682,
    Int.ofNat 2), (697, Int.negSucc 5), (700, Int.negSucc 1), (703, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (342, Int.negSucc 35), (366, Int.ofNat 8), (381, Int.ofNat 8), (393, Int.negSucc 11),
    (401, Int.negSucc 3), (405, Int.negSucc 4), (409, Int.ofNat 12), (438, Int.ofNat 4), (685,
    Int.negSucc 11), (698, Int.negSucc 19), (733, Int.negSucc 11), (736, Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(100, Int.negSucc 1), (367, Int.negSucc 2), (431,
    Int.negSucc 3), (452, Int.ofNat 2), (699, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 7), (352, Int.ofNat 8), (379, Int.negSucc 11), (389,
    Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 8), (446, Int.negSucc
    3), (461, Int.negSucc 3), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    3), (357, Int.ofNat 4), (384, Int.negSucc 7), (395, Int.ofNat 2), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 3), (440, Int.negSucc 1), (460, Int.negSucc 1), (751, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    7), (372, Int.ofNat 8), (403, Int.negSucc 7), (411, Int.ofNat 4), (426, Int.negSucc 3), (439,
    Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 1), (456, Int.ofNat 3), (758, Int.ofNat 4)]
    },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 11), (390, Int.ofNat 8), (421, Int.negSucc 11), (464, Int.negSucc 3), (475,
    Int.ofNat 8), (487, Int.ofNat 4), (708, Int.negSucc 3), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (361, Int.ofNat 2), (376, Int.ofNat 4), (397, Int.negSucc 0), (410, Int.negSucc 3), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 5), (379, Int.ofNat 6), (389,
    Int.negSucc 1), (413, Int.ofNat 2), (423, Int.negSucc 1), (428, Int.negSucc 1), (446,
    Int.ofNat 2), (694, Int.ofNat 2), (726, Int.ofNat 2), (744, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2), (708, Int.negSucc 1), (727, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (366, Int.ofNat 2), (381, Int.ofNat 4), (405, Int.negSucc 0), (409, Int.negSucc 3), (685,
    Int.ofNat 4), (698, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 5), (384, Int.ofNat 6), (395,
    Int.negSucc 1), (416, Int.ofNat 2), (427, Int.negSucc 1), (435, Int.negSucc 1), (440,
    Int.ofNat 2), (693, Int.ofNat 2), (737, Int.ofNat 2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (385, Int.negSucc 1), (433,
    Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2), (707, Int.negSucc 1), (738, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 8), (429,
    Int.negSucc 15), (468, Int.negSucc 3), (482, Int.ofNat 4), (490, Int.ofNat 6), (695, Int.ofNat
    8), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 9), (468, Int.negSucc 1), (482, Int.ofNat 3), (490, Int.ofNat 3), (695, Int.ofNat
    4), (745, Int.negSucc 1), (752, Int.negSucc 1), (759, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 13), (396,
    Int.ofNat 8), (433, Int.negSucc 13), (471, Int.negSucc 3), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 10), (707, Int.negSucc 5), (738, Int.ofNat 2), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (72, Int.ofNat
    2), (346, Int.negSucc 1), (373, Int.negSucc 0), (377, Int.ofNat 2), (394, Int.ofNat 2), (691,
    Int.ofNat 2), (704, Int.ofNat 2), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 2), (379, Int.ofNat 3), (389,
    Int.negSucc 0), (413, Int.ofNat 1), (423, Int.negSucc 0), (428, Int.negSucc 0), (461,
    Int.ofNat 1), (694, Int.ofNat 1), (715, Int.negSucc 0), (744, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1), (708, Int.negSucc 1), (716,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (366, Int.negSucc 1), (393, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.ofNat 1), (685,
    Int.negSucc 3), (698, Int.negSucc 3), (733, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(372, Int.negSucc 5), (403, Int.ofNat 3), (411,
    Int.negSucc 1), (426, Int.ofNat 2), (439, Int.negSucc 1), (449, Int.negSucc 0), (456,
    Int.negSucc 0), (692, Int.negSucc 1), (734, Int.negSucc 1), (758, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (404, Int.negSucc 0), (454,
    Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1), (706, Int.ofNat 2), (735,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(128, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 9), (468, Int.negSucc 2), (482, Int.ofNat 2), (490, Int.ofNat 3), (695, Int.ofNat
    4), (745, Int.negSucc 1), (752, Int.negSucc 1), (759, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.negSucc 0), (404, Int.negSucc 6), (412,
    Int.ofNat 8), (454, Int.negSucc 6), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 5), (706, Int.ofNat 6), (735, Int.negSucc 1), (780, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 1), (59, Int.negSucc 1), (68,
    Int.negSucc 1), (72, Int.ofNat 2), (323, Int.negSucc 9), (346, Int.negSucc 3), (373, Int.ofNat
    1), (377, Int.negSucc 1), (383, Int.ofNat 2), (388, Int.ofNat 8), (394, Int.ofNat 6), (691,
    Int.ofNat 8), (704, Int.ofNat 10), (711, Int.negSucc 3), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357,
    Int.negSucc 19), (384, Int.ofNat 24), (395, Int.negSucc 3), (416, Int.ofNat 8), (427,
    Int.negSucc 7), (435, Int.negSucc 7), (440, Int.ofNat 2), (460, Int.ofNat 2), (693, Int.ofNat
    8), (712, Int.negSucc 1), (737, Int.ofNat 2), (751, Int.negSucc 7)] }
]

end VOA.DeligneAudit.D4Two.Certificate

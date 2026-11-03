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
def actionData300 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(44, Int.negSucc 1), (316, Int.ofNat 6), (327,
    Int.negSucc 3), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (682,
    Int.negSucc 7), (697, Int.ofNat 4), (700, Int.ofNat 4), (703, Int.ofNat 4), (813, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(16, Int.ofNat 2), (307, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(312, Int.negSucc 0), (329, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(314, Int.negSucc 0), (330, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 0), (31, Int.ofNat 1), (315,
    Int.negSucc 0), (319, Int.negSucc 0), (332, Int.ofNat 1), (340, Int.ofNat 1), (348, Int.ofNat
    1), (368, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.negSucc 1), (327, Int.negSucc 0), (359,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.negSucc 0), (17, Int.ofNat 1), (317, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.negSucc 1), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    3), (316, Int.ofNat 6), (327, Int.negSucc 1), (343, Int.ofNat 2), (359, Int.negSucc 0), (386,
    Int.negSucc 1), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697,
    Int.ofNat 4), (700, Int.ofNat 4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (49, Int.negSucc 1), (354, Int.ofNat
    2), (369, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.ofNat 1), (50, Int.negSucc 3), (350,
    Int.negSucc 1), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.ofNat 1), (51, Int.negSucc 3), (349, Int.ofNat
    2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.negSucc 1), (21, Int.ofNat 4), (336, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(331, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.negSucc 0), (358, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(53, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(313, Int.negSucc 1), (317, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(314, Int.negSucc 1), (318, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (35, Int.ofNat 2), (315,
    Int.negSucc 1), (319, Int.negSucc 1), (332, Int.ofNat 2), (340, Int.ofNat 2), (348, Int.ofNat
    2), (353, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 0), (327, Int.negSucc 0), (343,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.negSucc 0), (21, Int.ofNat 2), (329, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(338, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.negSucc 0), (363, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.negSucc 0), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (29, Int.negSucc 1), (332,
    Int.negSucc 1), (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(322, Int.negSucc 1), (355, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (346, Int.negSucc 1), (383,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (30, Int.negSucc 1), (308,
    Int.negSucc 1), (319, Int.ofNat 2), (332, Int.negSucc 1), (340, Int.negSucc 1), (368,
    Int.ofNat 2), (689, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(322, Int.negSucc 1), (350, Int.ofNat 2), (355,
    Int.ofNat 2), (690, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (323, Int.ofNat 6), (346,
    Int.negSucc 7), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (704,
    Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (31, Int.negSucc 1), (340,
    Int.negSucc 1), (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(322, Int.negSucc 1), (350, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.negSucc 0), (346, Int.negSucc 1), (377,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.negSucc 0), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 0), (29, Int.ofNat 1), (319,
    Int.negSucc 0), (353, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(334, Int.negSucc 0), (370, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (361, Int.negSucc 0), (402,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(338, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0), (49, Int.ofNat 1), (341,
    Int.negSucc 1), (354, Int.negSucc 1), (369, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (366, Int.negSucc 1), (405,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (30, Int.ofNat 2), (308, Int.ofNat
    2), (319, Int.negSucc 1), (332, Int.ofNat 2), (340, Int.ofNat 2), (353, Int.ofNat 2), (686,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(334, Int.negSucc 1), (349, Int.negSucc 1), (370,
    Int.ofNat 2), (687, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.negSucc 1), (335, Int.ofNat 12), (361,
    Int.negSucc 7), (376, Int.negSucc 3), (397, Int.ofNat 3), (402, Int.ofNat 2), (701, Int.ofNat
    8), (722, Int.ofNat 8), (725, Int.ofNat 8), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(23, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(22, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.negSucc 0), (50, Int.ofNat 2), (322,
    Int.negSucc 3), (350, Int.ofNat 4), (355, Int.ofNat 4), (690, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(68, Int.negSucc 0), (323, Int.ofNat 3), (346,
    Int.negSucc 4), (373, Int.negSucc 1), (377, Int.ofNat 1), (383, Int.ofNat 1), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2), (818, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(32, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(25, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.negSucc 0), (51, Int.ofNat 2), (334,
    Int.negSucc 3), (349, Int.negSucc 3), (370, Int.ofNat 4), (687, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(69, Int.negSucc 1), (335, Int.ofNat 6), (361,
    Int.negSucc 4), (376, Int.negSucc 1), (397, Int.ofNat 2), (402, Int.ofNat 1), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4), (815, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (29, Int.ofNat 1), (30, Int.ofNat
    1), (308, Int.ofNat 1), (315, Int.negSucc 0), (319, Int.negSucc 1), (332, Int.ofNat 2), (340,
    Int.ofNat 2), (348, Int.ofNat 1), (353, Int.ofNat 1), (368, Int.negSucc 0), (683, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(45, Int.negSucc 0), (49, Int.ofNat 1), (341,
    Int.negSucc 3), (354, Int.negSucc 3), (369, Int.ofNat 4), (684, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.negSucc 1), (342, Int.ofNat 6), (366,
    Int.negSucc 4), (381, Int.negSucc 1), (401, Int.ofNat 1), (405, Int.ofNat 2), (698, Int.ofNat
    4), (733, Int.ofNat 4), (736, Int.ofNat 4), (814, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 0), (31, Int.ofNat 1), (319,
    Int.negSucc 0), (348, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(341, Int.negSucc 0), (369, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 1), (366, Int.negSucc 0), (401,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    3), (323, Int.ofNat 6), (346, Int.negSucc 5), (373, Int.negSucc 1), (383, Int.ofNat 2), (388,
    Int.negSucc 1), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704,
    Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (69, Int.ofNat 2), (73, Int.negSucc
    3), (335, Int.ofNat 6), (361, Int.negSucc 2), (387, Int.ofNat 2), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (410, Int.negSucc 1), (444, Int.negSucc 1), (688, Int.ofNat 2), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4), (815, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 1), (70, Int.ofNat 1), (74, Int.negSucc
    1), (342, Int.ofNat 3), (366, Int.negSucc 1), (393, Int.ofNat 1), (405, Int.ofNat 1), (409,
    Int.negSucc 0), (438, Int.negSucc 0), (685, Int.ofNat 1), (698, Int.ofNat 2), (733, Int.ofNat
    2), (736, Int.ofNat 2), (814, Int.negSucc 0)] },
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
  { denominator := Int.ofNat 1, terms := [(323, Int.negSucc 7), (346, Int.ofNat 6), (373,
    Int.ofNat 3), (377, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat
    2), (691, Int.ofNat 2), (704, Int.ofNat 6), (711, Int.negSucc 3), (714, Int.negSucc 3), (818,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (347, Int.negSucc 1), (420,
    Int.ofNat 2), (432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (49, Int.negSucc 1), (369,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(356, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (384, Int.negSucc 3), (435,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (352, Int.ofNat 12), (379,
    Int.negSucc 15), (413, Int.negSucc 5), (423, Int.ofNat 6), (428, Int.ofNat 4), (694,
    Int.negSucc 7), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.negSucc 0), (374, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (51, Int.negSucc 1), (334, Int.ofNat
    2), (349, Int.ofNat 2), (370, Int.negSucc 3), (687, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.negSucc 0), (352, Int.ofNat 6), (379,
    Int.negSucc 9), (413, Int.negSucc 2), (423, Int.ofNat 4), (428, Int.ofNat 2), (694,
    Int.negSucc 3), (744, Int.ofNat 4), (821, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (357, Int.ofNat 6), (384,
    Int.negSucc 9), (416, Int.negSucc 2), (427, Int.ofNat 2), (435, Int.ofNat 4), (693,
    Int.negSucc 3), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (44, Int.negSucc 1), (48, Int.ofNat
    2), (327, Int.negSucc 0), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (392,
    Int.ofNat 2), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(335, Int.negSucc 15), (361, Int.ofNat 6), (376,
    Int.ofNat 4), (387, Int.negSucc 3), (397, Int.negSucc 2), (402, Int.negSucc 1), (410,
    Int.ofNat 4), (688, Int.negSucc 3), (701, Int.negSucc 11), (722, Int.negSucc 7), (725,
    Int.negSucc 7), (815, Int.ofNat 4)] },
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
  { denominator := Int.ofNat 1, terms := [(95, Int.negSucc 0), (352, Int.ofNat 6), (379,
    Int.negSucc 9), (413, Int.negSucc 3), (423, Int.ofNat 3), (428, Int.ofNat 2), (694,
    Int.negSucc 3), (744, Int.ofNat 4), (821, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.negSucc 1), (398, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (372, Int.ofNat 12), (403,
    Int.negSucc 9), (426, Int.negSucc 3), (449, Int.ofNat 3), (456, Int.ofNat 4), (692, Int.ofNat
    8), (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.negSucc 0), (50, Int.ofNat 1), (322,
    Int.negSucc 1), (350, Int.ofNat 2), (355, Int.ofNat 2), (690, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(60, Int.ofNat 1), (356, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(98, Int.negSucc 0), (357, Int.ofNat 3), (384,
    Int.negSucc 5), (416, Int.negSucc 1), (427, Int.ofNat 1), (435, Int.ofNat 2), (693,
    Int.negSucc 1), (751, Int.ofNat 2), (819, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.negSucc 0), (51, Int.ofNat 1), (334,
    Int.negSucc 1), (349, Int.negSucc 1), (370, Int.ofNat 2), (687, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(67, Int.ofNat 1), (371, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(99, Int.negSucc 0), (372, Int.ofNat 3), (403,
    Int.negSucc 2), (426, Int.negSucc 0), (449, Int.ofNat 1), (456, Int.ofNat 1), (692, Int.ofNat
    2), (758, Int.ofNat 2), (816, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 5), (44, Int.negSucc 5), (48, Int.ofNat
    6), (316, Int.negSucc 7), (327, Int.negSucc 1), (343, Int.negSucc 5), (359, Int.ofNat 3),
    (365, Int.ofNat 3), (386, Int.ofNat 6), (392, Int.ofNat 2), (408, Int.negSucc 1), (682,
    Int.ofNat 6), (697, Int.negSucc 7), (700, Int.negSucc 3), (703, Int.negSucc 3), (813,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (70, Int.negSucc 1), (74, Int.ofNat
    2), (342, Int.negSucc 23), (366, Int.ofNat 7), (381, Int.ofNat 4), (393, Int.negSucc 5), (401,
    Int.negSucc 1), (405, Int.negSucc 3), (409, Int.ofNat 6), (438, Int.ofNat 2), (685,
    Int.negSucc 5), (698, Int.negSucc 15), (733, Int.negSucc 11), (736, Int.negSucc 11), (814,
    Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(100, Int.negSucc 1), (367, Int.negSucc 2), (431,
    Int.negSucc 3), (452, Int.ofNat 2), (699, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 7), (352, Int.ofNat 12), (379, Int.negSucc 15), (389,
    Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 8), (446, Int.negSucc
    3), (461, Int.negSucc 3), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    3), (357, Int.ofNat 6), (384, Int.negSucc 9), (395, Int.ofNat 2), (416, Int.negSucc 1), (427,
    Int.ofNat 2), (435, Int.ofNat 4), (440, Int.negSucc 1), (460, Int.negSucc 1), (693,
    Int.negSucc 1), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (99, Int.ofNat 2), (103, Int.negSucc
    3), (372, Int.ofNat 6), (403, Int.negSucc 4), (411, Int.ofNat 2), (426, Int.negSucc 1), (439,
    Int.ofNat 2), (445, Int.ofNat 2), (449, Int.ofNat 1), (456, Int.ofNat 2), (692, Int.ofNat 2),
    (758, Int.ofNat 4), (816, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 15), (390, Int.ofNat 12), (421, Int.negSucc 15), (464, Int.negSucc 5), (475,
    Int.ofNat 12), (487, Int.ofNat 4), (708, Int.negSucc 3), (765, Int.ofNat 8), (822, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (361, Int.ofNat 2), (376, Int.ofNat 4), (397, Int.negSucc 0), (410, Int.negSucc 3), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 7), (379, Int.ofNat 8), (389,
    Int.negSucc 1), (413, Int.ofNat 3), (423, Int.negSucc 2), (428, Int.negSucc 1), (446,
    Int.ofNat 2), (694, Int.ofNat 4), (726, Int.ofNat 2), (744, Int.negSucc 3), (821, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (380, Int.negSucc 1), (421,
    Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2), (708, Int.negSucc 1), (727, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (366, Int.ofNat 2), (381, Int.ofNat 4), (405, Int.negSucc 0), (409, Int.negSucc 3), (685,
    Int.ofNat 4), (698, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 7), (384, Int.ofNat 8), (395,
    Int.negSucc 1), (416, Int.ofNat 3), (427, Int.negSucc 1), (435, Int.negSucc 2), (440,
    Int.ofNat 2), (693, Int.ofNat 4), (737, Int.ofNat 2), (751, Int.negSucc 3), (819, Int.ofNat
    2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

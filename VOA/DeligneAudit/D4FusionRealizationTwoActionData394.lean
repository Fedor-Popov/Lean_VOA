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
def actionData394 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(16, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 2), (21, Int.negSucc 3), (336,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(313, Int.ofNat 2), (317, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(20, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(22, Int.ofNat 1), (321, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(320, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (29, Int.negSucc 0), (319, Int.ofNat
    1), (353, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (30, Int.negSucc 1), (308,
    Int.negSucc 1), (319, Int.ofNat 2), (340, Int.negSucc 1), (353, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(23, Int.ofNat 1), (320, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (30, Int.negSucc 0), (31, Int.negSucc
    0), (308, Int.negSucc 0), (315, Int.ofNat 1), (319, Int.ofNat 2), (332, Int.negSucc 0), (340,
    Int.negSucc 1), (348, Int.negSucc 0), (353, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(28, Int.ofNat 1), (339, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(23, Int.ofNat 1), (320, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (29, Int.negSucc 0), (30, Int.negSucc
    0), (308, Int.ofNat 2), (315, Int.ofNat 1), (319, Int.ofNat 2), (340, Int.negSucc 0), (348,
    Int.negSucc 0), (353, Int.negSucc 1), (368, Int.ofNat 1), (681, Int.negSucc 1), (683,
    Int.ofNat 1), (686, Int.ofNat 1), (689, Int.ofNat 2), (812, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 4), (35, Int.negSucc 3), (340,
    Int.negSucc 3), (353, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.ofNat 1), (338, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 2), (345, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 2), (355, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 2), (322, Int.ofNat 4), (355, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (350, Int.negSucc
    1), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(40, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (327, Int.ofNat 1), (343, Int.ofNat 2), (365, Int.negSucc 0), (392, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (49, Int.negSucc 0), (354, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(344, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (316, Int.ofNat 8), (343, Int.ofNat 2), (365, Int.negSucc 0), (386, Int.negSucc 1), (392,
    Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697, Int.ofNat 4), (700, Int.ofNat
    4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 2), (50, Int.negSucc 1), (322, Int.ofNat
    2), (355, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (51, Int.negSucc 1), (334, Int.ofNat
    2), (349, Int.ofNat 2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (49, Int.negSucc 0), (341, Int.ofNat
    2), (354, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(40, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(45, Int.ofNat 2), (49, Int.negSucc 0), (341, Int.ofNat
    4), (354, Int.ofNat 4), (369, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.ofNat 4), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (50, Int.negSucc 0), (322, Int.ofNat
    2), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(40, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(45, Int.ofNat 3), (49, Int.negSucc 2), (341, Int.ofNat
    2), (354, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (341, Int.ofNat 4), (354, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 4), (363, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 2), (346, Int.ofNat 4), (383, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 1), (323, Int.ofNat
    2), (346, Int.ofNat 4), (383, Int.negSucc 1), (394, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1), (356, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (323, Int.ofNat 8), (346, Int.negSucc
    3), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 1), (394,
    Int.negSucc 1), (691, Int.negSucc 1), (704, Int.negSucc 3), (711, Int.ofNat 4), (714,
    Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(351, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 2), (356, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(60, Int.ofNat 1), (356, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    1), (346, Int.ofNat 2), (373, Int.ofNat 1), (394, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (335, Int.ofNat 16), (361, Int.negSucc 1), (387, Int.ofNat 4), (397, Int.ofNat 3), (410,
    Int.negSucc 3), (444, Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat 8), (722, Int.ofNat
    8), (725, Int.ofNat 8), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (366, Int.ofNat 2), (393, Int.ofNat 4), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    1), (323, Int.ofNat 8), (346, Int.negSucc 1), (373, Int.negSucc 1), (377, Int.ofNat 2), (388,
    Int.negSucc 1), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704,
    Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(382, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (70, Int.ofNat 2), (74, Int.negSucc
    1), (342, Int.ofNat 8), (366, Int.negSucc 0), (393, Int.ofNat 2), (401, Int.ofNat 1), (405,
    Int.ofNat 1), (409, Int.negSucc 1), (438, Int.negSucc 1), (685, Int.ofNat 2), (698, Int.ofNat
    4), (733, Int.ofNat 4), (736, Int.ofNat 4), (814, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(60, Int.ofNat 3), (356, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(371, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 12), (74, Int.negSucc 3), (342, Int.ofNat
    8), (366, Int.ofNat 6), (393, Int.ofNat 12), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 6), (71, Int.ofNat 2), (74, Int.negSucc
    1), (342, Int.ofNat 12), (366, Int.ofNat 1), (381, Int.negSucc 1), (393, Int.ofNat 8), (401,
    Int.ofNat 1), (405, Int.ofNat 1), (409, Int.negSucc 1), (685, Int.ofNat 2), (698, Int.ofNat
    4), (733, Int.ofNat 4), (736, Int.ofNat 4), (814, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(60, Int.ofNat 3), (356, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 1), (70, Int.ofNat 4), (77, Int.ofNat
    2), (342, Int.ofNat 4), (366, Int.ofNat 4), (381, Int.ofNat 4), (393, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 2), (347, Int.ofNat 4), (432, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 2), (384, Int.ofNat 8), (435, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.negSucc 0), (85, Int.ofNat 2), (352, Int.ofNat
    16), (379, Int.negSucc 11), (389, Int.ofNat 4), (413, Int.negSucc 5), (423, Int.ofNat 6),
    (428, Int.ofNat 4), (446, Int.negSucc 3), (694, Int.negSucc 3), (744, Int.ofNat 8), (821,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (86, Int.ofNat 1), (357, Int.ofNat
    2), (384, Int.ofNat 6), (395, Int.ofNat 2), (435, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(87, Int.ofNat 1), (357, Int.ofNat 8), (384, Int.negSucc
    5), (395, Int.ofNat 2), (416, Int.negSucc 2), (427, Int.ofNat 2), (435, Int.ofNat 3), (440,
    Int.negSucc 1), (693, Int.negSucc 1), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 1), (86, Int.ofNat 6), (357, Int.ofNat
    12), (384, Int.ofNat 4), (395, Int.ofNat 12), (435, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 4), (87, Int.ofNat
    2), (357, Int.ofNat 24), (384, Int.negSucc 11), (395, Int.ofNat 16), (416, Int.negSucc 5),
    (427, Int.ofNat 4), (435, Int.ofNat 4), (693, Int.negSucc 3), (751, Int.ofNat 8), (819,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (87, Int.negSucc
    1), (357, Int.ofNat 12), (384, Int.negSucc 23), (395, Int.ofNat 4), (416, Int.negSucc 5),
    (427, Int.ofNat 12), (435, Int.ofNat 6), (693, Int.negSucc 3), (751, Int.ofNat 8), (819,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 16), (379, Int.negSucc 7), (389,
    Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat 6), (428, Int.ofNat 4), (446, Int.negSucc
    3), (461, Int.negSucc 3), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    1), (384, Int.ofNat 2), (395, Int.ofNat 2), (416, Int.ofNat 1), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (372, Int.ofNat 16), (403, Int.negSucc 3), (411, Int.ofNat 4), (426, Int.negSucc 3), (439,
    Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 3), (456, Int.ofNat 2), (692, Int.ofNat 4),
    (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.negSucc 0), (100, Int.ofNat 1), (367, Int.ofNat
    1), (431, Int.ofNat 2)] },
  { denominator := Int.ofNat 6, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    1), (357, Int.ofNat 8), (384, Int.negSucc 3), (395, Int.ofNat 2), (416, Int.negSucc 1), (427,
    Int.ofNat 4), (435, Int.ofNat 2), (440, Int.negSucc 1), (460, Int.negSucc 1), (693,
    Int.negSucc 1), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(406, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 2), (86, Int.ofNat 6), (98, Int.ofNat
    4), (357, Int.ofNat 16), (384, Int.ofNat 8), (395, Int.ofNat 16), (416, Int.ofNat 2), (435,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (99, Int.ofNat 4), (372, Int.ofNat
    16), (403, Int.negSucc 5), (411, Int.ofNat 4), (426, Int.negSucc 3), (445, Int.ofNat 4), (449,
    Int.ofNat 3), (456, Int.ofNat 3), (692, Int.ofNat 4), (758, Int.ofNat 8), (816, Int.ofNat 4)]
    },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (87, Int.ofNat
    4), (357, Int.ofNat 28), (384, Int.negSucc 27), (395, Int.ofNat 8), (416, Int.negSucc 11),
    (427, Int.ofNat 8), (435, Int.ofNat 12), (440, Int.negSucc 1), (460, Int.negSucc 1), (693,
    Int.negSucc 7), (751, Int.ofNat 16), (819, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(81, Int.negSucc 0), (86, Int.ofNat 6), (98, Int.ofNat
    4), (357, Int.ofNat 32), (395, Int.ofNat 20), (416, Int.negSucc 3), (427, Int.ofNat 8), (440,
    Int.negSucc 3), (460, Int.negSucc 3), (693, Int.negSucc 3), (751, Int.ofNat 8), (819,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.negSucc 3), (98, Int.ofNat
    12), (357, Int.ofNat 4), (384, Int.ofNat 12), (395, Int.ofNat 4), (416, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 2), (375, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 2), (380, Int.negSucc 11), (390, Int.ofNat 12), (421, Int.negSucc 11), (464,
    Int.negSucc 5), (475, Int.ofNat 12), (487, Int.ofNat 4), (494, Int.negSucc 3), (765, Int.ofNat
    8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 2), (385, Int.ofNat 4), (433, Int.ofNat
    4), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 2), (436, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(414, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 1), (417, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(115, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.ofNat 16), (429, Int.negSucc 15), (441, Int.ofNat 4), (447, Int.ofNat 4), (468,
    Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745, Int.negSucc
    7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.ofNat 1), (385, Int.ofNat
    8), (396, Int.ofNat 4), (433, Int.ofNat 12), (497, Int.negSucc 7)] },
  { denominator := Int.ofNat 3, terms := [(112, Int.ofNat 5), (436, Int.ofNat 30)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 11), (396, Int.ofNat 16), (433, Int.negSucc 3), (471,
    Int.negSucc 5), (486, Int.ofNat 4), (497, Int.ofNat 8), (773, Int.ofNat 8), (820, Int.negSucc
    3)] },
  { denominator := Int.ofNat 3, terms := [(112, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 2), (417, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (115, Int.negSucc 1), (117,
    Int.ofNat 2), (391, Int.ofNat 12), (429, Int.negSucc 15), (447, Int.ofNat 4), (468,
    Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745, Int.negSucc
    7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 4), (115, Int.negSucc 6), (117,
    Int.ofNat 6), (391, Int.ofNat 64), (429, Int.negSucc 87), (441, Int.ofNat 4), (447, Int.ofNat
    20), (468, Int.negSucc 29), (482, Int.ofNat 34), (490, Int.ofNat 30), (695, Int.ofNat 60),
    (745, Int.negSucc 39), (752, Int.negSucc 39), (759, Int.ofNat 40), (823, Int.ofNat 10)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 16), (429, Int.negSucc
    11), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 3), (482,
    Int.ofNat 6), (490, Int.ofNat 4), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc
    7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (131,
    Int.ofNat 4), (385, Int.ofNat 8), (396, Int.ofNat 4), (433, Int.ofNat 12), (471, Int.ofNat 2),
    (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 6, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 2), (130, Int.negSucc 2), (132,
    Int.ofNat 4), (404, Int.negSucc 5), (412, Int.ofNat 12), (454, Int.negSucc 5), (485,
    Int.negSucc 3), (493, Int.ofNat 4), (504, Int.ofNat 3), (512, Int.ofNat 6), (780, Int.ofNat
    8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(457, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.ofNat 2), (407, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 3), (118, Int.negSucc 2), (131,
    Int.ofNat 4), (385, Int.negSucc 7), (396, Int.ofNat 12), (433, Int.negSucc 7), (471,
    Int.negSucc 3), (479, Int.negSucc 3), (486, Int.ofNat 8), (497, Int.ofNat 8), (508,
    Int.negSucc 1), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(436, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 7), (417, Int.ofNat 7)] }
]

end VOA.DeligneAudit.D4Two.Certificate

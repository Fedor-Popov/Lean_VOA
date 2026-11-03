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
def actionData389 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (29, Int.negSucc 1), (315, Int.ofNat
    2), (319, Int.ofNat 2), (332, Int.negSucc 1), (340, Int.negSucc 1), (353, Int.negSucc 1),
    (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(22, Int.ofNat 1), (321, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(25, Int.ofNat 1), (333, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (29, Int.negSucc 0), (30, Int.negSucc
    0), (308, Int.negSucc 0), (315, Int.ofNat 1), (319, Int.ofNat 2), (332, Int.negSucc 1), (340,
    Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (31, Int.negSucc 0), (319, Int.ofNat
    1), (348, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 3), (29, Int.negSucc 1), (30, Int.negSucc
    0), (308, Int.ofNat 2), (315, Int.ofNat 3), (319, Int.ofNat 3), (332, Int.negSucc 2), (340,
    Int.negSucc 1), (348, Int.negSucc 0), (353, Int.negSucc 2), (368, Int.ofNat 3), (681,
    Int.negSucc 1), (683, Int.ofNat 1), (686, Int.ofNat 1), (689, Int.ofNat 2), (812, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(32, Int.ofNat 1), (331, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (35, Int.negSucc 1), (332,
    Int.negSucc 1), (348, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(37, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(322, Int.ofNat 4), (355, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(37, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (350, Int.negSucc
    1), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 2), (350, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 2), (344, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(334, Int.ofNat 2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(345, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (316, Int.ofNat 8), (343, Int.ofNat 2), (359, Int.negSucc 0), (386, Int.negSucc 1), (392,
    Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697, Int.ofNat 4), (700, Int.ofNat
    4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 3), (49, Int.negSucc 2), (341, Int.ofNat
    6), (354, Int.ofNat 6), (369, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (349, Int.ofNat
    2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (50, Int.negSucc 0), (322, Int.ofNat
    2), (350, Int.negSucc 1), (355, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (51, Int.negSucc 0), (334, Int.ofNat
    2), (349, Int.ofNat 2), (370, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 6), (44, Int.ofNat 6), (48, Int.negSucc
    5), (316, Int.ofNat 8), (327, Int.ofNat 2), (343, Int.ofNat 6), (359, Int.negSucc 2), (386,
    Int.negSucc 5), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697,
    Int.ofNat 4), (700, Int.ofNat 4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(38, Int.ofNat 1), (50, Int.negSucc 1), (322, Int.ofNat
    6), (350, Int.negSucc 1), (355, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.ofNat 1), (51, Int.negSucc 1), (334, Int.ofNat
    6), (349, Int.ofNat 2), (370, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (334, Int.ofNat 4), (349, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.ofNat 2), (358, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.negSucc 1), (378, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (323, Int.ofNat 8), (346, Int.negSucc
    3), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 1), (394,
    Int.negSucc 1), (691, Int.negSucc 1), (704, Int.negSucc 3), (711, Int.ofNat 4), (714,
    Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(356, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(351, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 2), (323, Int.ofNat
    12), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 5), (394,
    Int.negSucc 1), (691, Int.negSucc 1), (704, Int.negSucc 3), (711, Int.ofNat 4), (714,
    Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (61, Int.ofNat 1), (323, Int.ofNat
    2), (346, Int.ofNat 4), (377, Int.negSucc 1), (388, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (335, Int.ofNat 16), (361,
    Int.negSucc 3), (376, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 3), (402, Int.ofNat
    2), (410, Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat 8), (722, Int.ofNat 8), (725,
    Int.ofNat 8), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(371, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(378, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    1), (323, Int.ofNat 8), (346, Int.negSucc 1), (373, Int.negSucc 1), (383, Int.ofNat 2), (388,
    Int.negSucc 1), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704,
    Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (69, Int.ofNat 2), (73, Int.negSucc
    1), (335, Int.ofNat 8), (361, Int.negSucc 0), (387, Int.ofNat 2), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (410, Int.negSucc 1), (444, Int.negSucc 1), (688, Int.ofNat 2), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4), (815, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (342, Int.ofNat 16), (366, Int.negSucc 1), (393, Int.ofNat 4), (405, Int.ofNat 3), (409,
    Int.negSucc 3), (438, Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 8), (733, Int.ofNat
    8), (736, Int.ofNat 8), (814, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (66, Int.ofNat 4), (335, Int.ofNat
    24), (376, Int.negSucc 3), (387, Int.ofNat 12), (397, Int.ofNat 3), (402, Int.ofNat 2), (410,
    Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat 8), (722, Int.ofNat 8), (725, Int.ofNat
    8), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 1), (68, Int.ofNat 1),
    (72, Int.negSucc 0), (323, Int.ofNat 6), (346, Int.ofNat 1), (373, Int.negSucc 0), (377,
    Int.ofNat 1), (383, Int.ofNat 1), (388, Int.negSucc 3), (394, Int.negSucc 0), (691,
    Int.negSucc 0), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2), (818, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (66, Int.ofNat 2), (69, Int.ofNat 2),
    (73, Int.negSucc 1), (335, Int.ofNat 12), (361, Int.ofNat 1), (376, Int.negSucc 1), (387,
    Int.ofNat 8), (397, Int.ofNat 1), (402, Int.ofNat 1), (410, Int.negSucc 1), (688, Int.ofNat
    2), (701, Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4), (815, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(58, Int.negSucc 0), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.ofNat 2), (75, Int.ofNat 1), (335, Int.ofNat
    4), (361, Int.ofNat 4), (376, Int.ofNat 4), (387, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 3), (379, Int.negSucc 7), (428,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (352,
    Int.ofNat 12), (379, Int.negSucc 23), (389, Int.ofNat 4), (413, Int.negSucc 5), (423,
    Int.ofNat 6), (428, Int.ofNat 12), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(83, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (352, Int.ofNat 8), (379, Int.negSucc
    5), (389, Int.ofNat 2), (413, Int.negSucc 2), (423, Int.ofNat 3), (428, Int.ofNat 2), (446,
    Int.negSucc 1), (694, Int.negSucc 1), (744, Int.ofNat 4), (821, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 2), (347, Int.ofNat 4), (420, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (357, Int.ofNat 16), (384,
    Int.negSucc 11), (395, Int.ofNat 4), (416, Int.negSucc 5), (427, Int.ofNat 4), (435, Int.ofNat
    6), (440, Int.negSucc 3), (693, Int.negSucc 3), (751, Int.ofNat 8), (819, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    20), (379, Int.negSucc 15), (389, Int.ofNat 12), (413, Int.negSucc 5), (423, Int.ofNat 6),
    (428, Int.ofNat 4), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (85, Int.ofNat 2),
    (352, Int.ofNat 24), (379, Int.negSucc 11), (389, Int.ofNat 16), (413, Int.negSucc 5), (423,
    Int.ofNat 4), (428, Int.ofNat 4), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (85, Int.ofNat 3), (352, Int.ofNat
    2), (379, Int.ofNat 6), (389, Int.ofNat 2), (423, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 1), (352, Int.ofNat 8), (379, Int.negSucc
    5), (389, Int.ofNat 2), (413, Int.negSucc 2), (423, Int.ofNat 3), (428, Int.ofNat 2), (461,
    Int.negSucc 1), (694, Int.negSucc 1), (744, Int.ofNat 4), (821, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(398, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 2), (362, Int.ofNat 1), (419, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (372, Int.ofNat 16), (403,
    Int.negSucc 5), (411, Int.ofNat 4), (426, Int.negSucc 3), (439, Int.ofNat 4), (449, Int.ofNat
    3), (456, Int.ofNat 3), (692, Int.ofNat 4), (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 16), (379, Int.negSucc 7), (389,
    Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 8), (446, Int.negSucc
    3), (461, Int.negSucc 3), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    1), (357, Int.ofNat 8), (384, Int.negSucc 3), (395, Int.ofNat 2), (416, Int.negSucc 1), (427,
    Int.ofNat 2), (435, Int.ofNat 3), (440, Int.negSucc 1), (460, Int.negSucc 1), (693,
    Int.negSucc 1), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (372, Int.ofNat 16), (403, Int.negSucc 3), (411, Int.ofNat 4), (426, Int.negSucc 3), (439,
    Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 2), (456, Int.ofNat 3), (692, Int.ofNat 4),
    (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (95, Int.ofNat 2),
    (352, Int.ofNat 24), (379, Int.negSucc 11), (389, Int.ofNat 16), (413, Int.negSucc 3), (423,
    Int.ofNat 6), (428, Int.ofNat 4), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 4), (82, Int.negSucc 0), (85, Int.ofNat
    6), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 24), (389, Int.ofNat 16), (413,
    Int.negSucc 3), (428, Int.ofNat 4), (446, Int.negSucc 3), (694, Int.negSucc 3), (744,
    Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    1), (95, Int.ofNat 1), (352, Int.ofNat 24), (379, Int.negSucc 19), (389, Int.ofNat 10), (413,
    Int.negSucc 7), (423, Int.ofNat 8), (428, Int.ofNat 8), (446, Int.negSucc 1), (461,
    Int.negSucc 1), (694, Int.negSucc 5), (744, Int.ofNat 12), (821, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 1), (95, Int.ofNat 6), (352, Int.ofNat
    4), (379, Int.ofNat 12), (389, Int.ofNat 4), (413, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (107, Int.negSucc 1), (380,
    Int.negSucc 15), (390, Int.ofNat 12), (421, Int.negSucc 11), (464, Int.negSucc 5), (475,
    Int.ofNat 12), (487, Int.ofNat 4), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 5), (429, Int.negSucc 23), (490,
    Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(113, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 3), (107, Int.negSucc 1), (380,
    Int.negSucc 31), (390, Int.ofNat 28), (421, Int.negSucc 19), (464, Int.negSucc 11), (475,
    Int.ofNat 24), (487, Int.ofNat 8), (765, Int.ofNat 16), (822, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (391,
    Int.ofNat 12), (429, Int.negSucc 31), (441, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 6), (490, Int.ofNat 14), (695, Int.ofNat 12), (745, Int.negSucc 7), (752,
    Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(414, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (110, Int.ofNat 2), (380,
    Int.negSucc 11), (390, Int.ofNat 16), (421, Int.negSucc 3), (464, Int.negSucc 5), (475,
    Int.ofNat 8), (487, Int.ofNat 4), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (391, Int.ofNat 16), (429,
    Int.negSucc 15), (441, Int.ofNat 4), (447, Int.ofNat 4), (468, Int.negSucc 5), (482, Int.ofNat
    6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc 7), (759,
    Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (385,
    Int.negSucc 11), (396, Int.ofNat 12), (433, Int.negSucc 11), (471, Int.negSucc 5), (479,
    Int.negSucc 3), (486, Int.ofNat 4), (497, Int.ofNat 12), (773, Int.ofNat 8), (820, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.ofNat 5), (424, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(424, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (120, Int.ofNat 4), (380,
    Int.negSucc 11), (390, Int.ofNat 16), (421, Int.negSucc 3), (464, Int.negSucc 3), (475,
    Int.ofNat 12), (487, Int.ofNat 4), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 1), (391, Int.ofNat 16), (429,
    Int.negSucc 15), (441, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 5), (482, Int.ofNat
    6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc 7), (759,
    Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(450, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

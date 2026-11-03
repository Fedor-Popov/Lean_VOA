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
def actionData260 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 3), (29, Int.negSucc 1), (30, Int.negSucc
    0), (308, Int.ofNat 2), (315, Int.ofNat 3), (319, Int.ofNat 3), (332, Int.negSucc 2), (340,
    Int.negSucc 1), (348, Int.negSucc 0), (353, Int.negSucc 2), (368, Int.ofNat 3), (681,
    Int.negSucc 0), (683, Int.ofNat 1), (686, Int.ofNat 1), (689, Int.ofNat 1)] },
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
    1), (316, Int.ofNat 6), (327, Int.ofNat 1), (343, Int.ofNat 2), (359, Int.negSucc 0), (386,
    Int.negSucc 1), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 1), (697,
    Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat 2)] },
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
    5), (316, Int.ofNat 6), (327, Int.ofNat 3), (343, Int.ofNat 6), (359, Int.negSucc 2), (386,
    Int.negSucc 5), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 1), (697,
    Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat 2)] },
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
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (323, Int.ofNat 6), (346, Int.negSucc
    1), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 1), (394,
    Int.negSucc 1), (691, Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(356, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(351, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 2), (323, Int.ofNat
    10), (346, Int.ofNat 2), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (388,
    Int.negSucc 5), (394, Int.negSucc 1), (691, Int.negSucc 1), (704, Int.negSucc 1), (711,
    Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (61, Int.ofNat 1), (323, Int.ofNat
    2), (346, Int.ofNat 4), (377, Int.negSucc 1), (388, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (335, Int.ofNat 6), (361, Int.negSucc
    0), (376, Int.negSucc 1), (387, Int.ofNat 2), (397, Int.ofNat 1), (402, Int.ofNat 1), (410,
    Int.negSucc 1), (688, Int.ofNat 2), (701, Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(371, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(378, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    1), (323, Int.ofNat 6), (373, Int.negSucc 0), (383, Int.ofNat 2), (388, Int.negSucc 1), (394,
    Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704, Int.negSucc 1), (711,
    Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (335, Int.ofNat 12), (387, Int.ofNat 4), (397, Int.ofNat 1), (402, Int.ofNat 2), (410,
    Int.negSucc 3), (444, Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat 4), (722, Int.ofNat
    4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 2), (70, Int.ofNat 2), (74, Int.negSucc
    1), (342, Int.ofNat 6), (393, Int.ofNat 2), (405, Int.ofNat 1), (409, Int.negSucc 1), (438,
    Int.negSucc 1), (685, Int.ofNat 2), (698, Int.ofNat 2), (733, Int.ofNat 2), (736, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(63, Int.ofNat 2), (66, Int.ofNat 2), (335, Int.ofNat
    10), (361, Int.ofNat 1), (376, Int.negSucc 1), (387, Int.ofNat 6), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (410, Int.negSucc 1), (688, Int.ofNat 2), (701, Int.ofNat 2), (722, Int.ofNat
    2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 2), (59, Int.ofNat 2), (68, Int.ofNat 2),
    (72, Int.negSucc 1), (323, Int.ofNat 10), (346, Int.ofNat 4), (373, Int.negSucc 0), (377,
    Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 7), (394, Int.negSucc 1), (691,
    Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 8), (66, Int.ofNat 4), (69, Int.ofNat 4),
    (73, Int.negSucc 3), (335, Int.ofNat 20), (361, Int.ofNat 4), (376, Int.negSucc 3), (387,
    Int.ofNat 16), (397, Int.ofNat 1), (402, Int.ofNat 2), (410, Int.negSucc 3), (688, Int.ofNat
    4), (701, Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(58, Int.negSucc 0), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.ofNat 2), (75, Int.ofNat 1), (335, Int.ofNat
    4), (361, Int.ofNat 4), (376, Int.ofNat 4), (387, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 3), (379, Int.negSucc 7), (428,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (352,
    Int.ofNat 8), (379, Int.negSucc 19), (389, Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat
    4), (428, Int.ofNat 12), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(83, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (352, Int.ofNat 6), (379, Int.negSucc
    3), (389, Int.ofNat 2), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 2), (446,
    Int.negSucc 1), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 2), (347, Int.ofNat 4), (420, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (357, Int.ofNat 12), (384,
    Int.negSucc 7), (395, Int.ofNat 4), (416, Int.negSucc 3), (427, Int.ofNat 4), (435, Int.ofNat
    4), (440, Int.negSucc 3), (751, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    16), (379, Int.negSucc 11), (389, Int.ofNat 12), (413, Int.negSucc 3), (423, Int.ofNat 4),
    (428, Int.ofNat 4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (85, Int.ofNat 2),
    (352, Int.ofNat 20), (379, Int.negSucc 7), (389, Int.ofNat 16), (413, Int.negSucc 3), (423,
    Int.ofNat 2), (428, Int.ofNat 4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (85, Int.ofNat 3), (352, Int.ofNat
    2), (379, Int.ofNat 6), (389, Int.ofNat 2), (423, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 1), (352, Int.ofNat 6), (379, Int.negSucc
    3), (389, Int.ofNat 2), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 2), (461,
    Int.negSucc 1), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(398, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 2), (362, Int.ofNat 1), (419, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.ofNat 1), (372, Int.ofNat 6), (403, Int.negSucc
    1), (411, Int.ofNat 2), (426, Int.negSucc 1), (439, Int.ofNat 2), (449, Int.ofNat 1), (456,
    Int.ofNat 1), (758, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 12), (379, Int.negSucc 3), (389,
    Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 8), (446, Int.negSucc
    3), (461, Int.negSucc 3), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    1), (357, Int.ofNat 6), (384, Int.negSucc 1), (395, Int.ofNat 2), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 2), (440, Int.negSucc 1), (460, Int.negSucc 1), (751, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (372, Int.ofNat 12), (403, Int.negSucc 1), (411, Int.ofNat 4), (426, Int.negSucc 3), (439,
    Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 1), (456, Int.ofNat 2), (758, Int.ofNat 4)]
    },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (95, Int.ofNat 2),
    (352, Int.ofNat 20), (379, Int.negSucc 7), (389, Int.ofNat 16), (413, Int.negSucc 1), (423,
    Int.ofNat 4), (428, Int.ofNat 4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 4), (82, Int.negSucc 0), (85, Int.ofNat
    6), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 20), (379, Int.ofNat 4), (389,
    Int.ofNat 16), (413, Int.negSucc 1), (423, Int.negSucc 1), (428, Int.ofNat 4), (446,
    Int.negSucc 3), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    1), (95, Int.ofNat 1), (352, Int.ofNat 18), (379, Int.negSucc 13), (389, Int.ofNat 10), (413,
    Int.negSucc 4), (423, Int.ofNat 5), (428, Int.ofNat 8), (446, Int.negSucc 1), (461,
    Int.negSucc 1), (744, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 1), (95, Int.ofNat 6), (352, Int.ofNat
    4), (379, Int.ofNat 12), (389, Int.ofNat 4), (413, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (107, Int.negSucc 1), (380,
    Int.negSucc 11), (390, Int.ofNat 8), (421, Int.negSucc 7), (464, Int.negSucc 3), (475,
    Int.ofNat 8), (487, Int.ofNat 4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 5), (429, Int.negSucc 23), (490,
    Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(113, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 3), (107, Int.negSucc 1), (380,
    Int.negSucc 23), (390, Int.ofNat 20), (421, Int.negSucc 11), (464, Int.negSucc 7), (475,
    Int.ofNat 16), (487, Int.ofNat 8), (765, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (391,
    Int.ofNat 8), (429, Int.negSucc 27), (441, Int.ofNat 4), (468, Int.negSucc 3), (482, Int.ofNat
    4), (490, Int.ofNat 12), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(414, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (110, Int.ofNat 2), (380,
    Int.negSucc 7), (390, Int.ofNat 12), (464, Int.negSucc 3), (475, Int.ofNat 4), (487, Int.ofNat
    4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (391, Int.ofNat 12), (429,
    Int.negSucc 11), (441, Int.ofNat 4), (447, Int.ofNat 4), (468, Int.negSucc 3), (482, Int.ofNat
    4), (490, Int.ofNat 4), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (396, Int.ofNat 8), (433, Int.negSucc 7), (471, Int.negSucc 3), (479,
    Int.negSucc 3), (486, Int.ofNat 4), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.ofNat 5), (424, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(424, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (120, Int.ofNat 4), (380,
    Int.negSucc 7), (390, Int.ofNat 12), (464, Int.negSucc 1), (475, Int.ofNat 8), (487, Int.ofNat
    4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 1), (391, Int.ofNat 12), (429,
    Int.negSucc 11), (441, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 3), (482, Int.ofNat
    4), (490, Int.ofNat 4), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(450, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 6), (130, Int.negSucc 0), (404,
    Int.negSucc 3), (412, Int.ofNat 8), (454, Int.negSucc 3), (478, Int.ofNat 4), (485,
    Int.negSucc 3), (504, Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 2), (120, Int.ofNat 4), (380, Int.negSucc 3), (390, Int.ofNat 8), (421, Int.negSucc
    3), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 8), (494, Int.negSucc 3), (509,
    Int.negSucc 1), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 12), (429, Int.negSucc
    7), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 1), (482,
    Int.ofNat 2), (490, Int.ofNat 4), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 5), (414, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 1), (415, Int.negSucc 3), (465,
    Int.negSucc 1), (540, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 1), (425, Int.negSucc 3), (476,
    Int.negSucc 3), (544, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 2), (422, Int.ofNat 8)] }
]

end VOA.DeligneAudit.D4Two.Certificate

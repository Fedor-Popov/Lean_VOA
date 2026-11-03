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
def actionData236 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(815, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(816, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(818, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(819, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(820, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(821, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(823, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 2), (832, Int.negSucc 1), (840,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(825, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 2), (832, Int.negSucc 1), (840,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(828, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.negSucc 1), (832, Int.ofNat 2), (840,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(830, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(831, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 2), (832, Int.negSucc 1), (840,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(834, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(835, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(836, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(837, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(838, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(300, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(303, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(302, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(301, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(306, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(305, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1), (309, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(304, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(12, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1), (313, Int.negSucc 1), (317,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (318, Int.negSucc 0), (330, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(307, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1), (313, Int.negSucc 1), (317,
    Int.negSucc 0), (337, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(18, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1), (312, Int.ofNat 4), (329, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(20, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(19, Int.ofNat 1), (312, Int.ofNat 4), (329, Int.negSucc
    1), (336, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(22, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 1), (320, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(24, Int.ofNat 2), (326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    2), (332, Int.negSucc 1), (348, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(27, Int.ofNat 2), (325, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 4), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (348, Int.negSucc 1), (353, Int.negSucc 0),
    (368, Int.ofNat 1), (681, Int.negSucc 1), (683, Int.ofNat 2), (686, Int.ofNat 2), (689,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 2), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0),
    (353, Int.negSucc 0), (368, Int.ofNat 1), (681, Int.negSucc 0), (683, Int.ofNat 1), (686,
    Int.ofNat 1), (689, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    1), (332, Int.negSucc 1), (340, Int.negSucc 0), (348, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(32, Int.ofNat 1), (331, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 1), (324, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    2), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1), (345, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (350, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1), (344, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(41, Int.ofNat 2), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (316, Int.ofNat 8), (327, Int.negSucc
    0), (365, Int.ofNat 1), (386, Int.negSucc 3), (682, Int.negSucc 3), (697, Int.ofNat 4), (700,
    Int.ofNat 4), (703, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (349, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (316, Int.ofNat 6), (327, Int.ofNat
    1), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.ofNat 1), (386, Int.negSucc 3), (682,
    Int.negSucc 1), (697, Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (359, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.negSucc 1), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    14), (327, Int.ofNat 1), (343, Int.ofNat 2), (359, Int.negSucc 0), (386, Int.negSucc 5), (392,
    Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697, Int.ofNat 6), (700, Int.ofNat
    6), (703, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0), (354, Int.negSucc 1), (369,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (350, Int.negSucc
    1), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (349, Int.ofNat
    2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.ofNat 1), (358, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(53, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 1), (327, Int.ofNat 1), (343, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.negSucc 0), (363, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (323, Int.ofNat 8), (346, Int.negSucc
    5), (373, Int.negSucc 3), (377, Int.ofNat 4), (383, Int.ofNat 2), (388, Int.negSucc 3), (691,
    Int.negSucc 3), (704, Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (323, Int.ofNat 6), (346, Int.negSucc
    1), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3), (691,
    Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (346, Int.ofNat 2), (377, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.negSucc 0), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (335, Int.ofNat 8), (361, Int.negSucc
    2), (376, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 2), (402, Int.ofNat 1), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (342, Int.ofNat 16), (366,
    Int.negSucc 1), (405, Int.ofNat 3), (438, Int.negSucc 7), (685, Int.ofNat 8), (698, Int.ofNat
    8), (733, Int.ofNat 8), (736, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.ofNat 1), (335, Int.ofNat 6), (361, Int.negSucc
    0), (376, Int.negSucc 1), (387, Int.ofNat 4), (397, Int.ofNat 1), (402, Int.ofNat 1), (688,
    Int.ofNat 2), (701, Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(68, Int.ofNat 2), (323, Int.ofNat 6), (373, Int.negSucc
    0), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3), (691, Int.negSucc 1), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(69, Int.ofNat 4), (335, Int.ofNat 12), (376,
    Int.negSucc 3), (387, Int.ofNat 8), (397, Int.ofNat 1), (402, Int.ofNat 2), (688, Int.ofNat
    4), (701, Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.negSucc 3), (342, Int.ofNat
    20), (366, Int.negSucc 7), (381, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.ofNat 5), (438,
    Int.negSucc 7), (685, Int.ofNat 12), (698, Int.ofNat 12), (733, Int.ofNat 12), (736, Int.ofNat
    12)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 1), (366, Int.negSucc 0), (401,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    14), (346, Int.negSucc 3), (373, Int.negSucc 4), (377, Int.ofNat 4), (383, Int.ofNat 2), (388,
    Int.negSucc 5), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 5), (704,
    Int.negSucc 5), (711, Int.ofNat 6), (714, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (335, Int.ofNat
    28), (361, Int.negSucc 3), (376, Int.negSucc 7), (387, Int.ofNat 12), (397, Int.ofNat 5),
    (402, Int.ofNat 2), (410, Int.negSucc 3), (444, Int.negSucc 3), (688, Int.ofNat 12), (701,
    Int.ofNat 12), (722, Int.ofNat 12), (725, Int.ofNat 12)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 8), (70, Int.negSucc 3), (342, Int.ofNat
    36), (366, Int.negSucc 5), (393, Int.negSucc 3), (405, Int.ofNat 7), (409, Int.ofNat 4), (438,
    Int.negSucc 19), (685, Int.ofNat 20), (698, Int.ofNat 20), (733, Int.ofNat 20), (736,
    Int.ofNat 20)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.ofNat 1), (361, Int.ofNat 2), (376, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.negSucc 0), (400, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 0), (366, Int.negSucc 0), (381,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (352, Int.ofNat 8), (379, Int.negSucc
    9), (389, Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 2), (744,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.negSucc 1), (432, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (357, Int.ofNat 16), (384,
    Int.negSucc 11), (416, Int.negSucc 7), (427, Int.ofNat 8), (435, Int.ofNat 6), (440,
    Int.negSucc 7), (751, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.ofNat 1), (352, Int.ofNat 12), (379,
    Int.negSucc 11), (389, Int.ofNat 8), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat
    4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.ofNat 1), (352, Int.ofNat 6), (379, Int.negSucc
    3), (389, Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 1), (428, Int.ofNat 2), (744,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (86, Int.negSucc 0), (357, Int.ofNat
    10), (384, Int.negSucc 11), (416, Int.negSucc 5), (427, Int.ofNat 6), (435, Int.ofNat 5),
    (440, Int.negSucc 3), (751, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 2), (419, Int.ofNat 2), (453, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (372, Int.ofNat 16), (403,
    Int.negSucc 5), (426, Int.negSucc 7), (439, Int.ofNat 8), (449, Int.ofNat 4), (456, Int.ofNat
    3), (758, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 2), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.negSucc 1), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(95, Int.ofNat 1), (352, Int.ofNat 6), (379, Int.negSucc
    3), (389, Int.ofNat 4), (413, Int.negSucc 0), (423, Int.ofNat 2), (428, Int.ofNat 2), (744,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (97, Int.negSucc 1), (372, Int.ofNat
    20), (403, Int.negSucc 11), (426, Int.negSucc 11), (439, Int.ofNat 8), (449, Int.ofNat 6),
    (456, Int.ofNat 5), (758, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.negSucc 1), (357, Int.ofNat
    10), (384, Int.negSucc 13), (416, Int.negSucc 6), (427, Int.ofNat 6), (435, Int.ofNat 5),
    (440, Int.negSucc 3), (751, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 4), (99, Int.negSucc 3), (372, Int.ofNat
    20), (403, Int.negSucc 13), (426, Int.negSucc 11), (439, Int.ofNat 8), (449, Int.ofNat 7),
    (456, Int.ofNat 5), (758, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 3), (100, Int.negSucc 1), (367,
    Int.negSucc 2), (431, Int.negSucc 3), (452, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (352, Int.ofNat 28), (379, Int.negSucc 19), (389, Int.ofNat 12), (413,
    Int.negSucc 9), (423, Int.ofNat 10), (428, Int.ofNat 8), (446, Int.negSucc 3), (461,
    Int.negSucc 3), (744, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 2), (98, Int.negSucc 1), (357, Int.ofNat
    18), (384, Int.negSucc 15), (395, Int.negSucc 1), (416, Int.negSucc 10), (427, Int.ofNat 10),
    (435, Int.ofNat 7), (440, Int.negSucc 9), (460, Int.ofNat 2), (751, Int.ofNat 10)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 8), (99, Int.negSucc 3), (372, Int.ofNat
    36), (403, Int.negSucc 15), (411, Int.negSucc 3), (426, Int.negSucc 19), (439, Int.ofNat 20),
    (445, Int.negSucc 3), (449, Int.ofNat 11), (456, Int.ofNat 7), (758, Int.ofNat 20)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (380, Int.negSucc 15), (390,
    Int.ofNat 16), (421, Int.negSucc 7), (464, Int.negSucc 7), (475, Int.ofNat 16), (765,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.ofNat 2), (380,
    Int.negSucc 27), (390, Int.ofNat 28), (421, Int.negSucc 11), (464, Int.negSucc 11), (475,
    Int.ofNat 24), (487, Int.ofNat 4), (765, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (391, Int.ofNat 16), (429,
    Int.negSucc 19), (441, Int.ofNat 8), (468, Int.negSucc 7), (482, Int.ofNat 8), (490, Int.ofNat
    6), (695, Int.ofNat 8), (745, Int.negSucc 7), (752, Int.negSucc 7), (759, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (421, Int.ofNat 2), (475,
    Int.negSucc 1), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 2), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (396, Int.ofNat 4), (433, Int.negSucc 9), (471, Int.negSucc 3), (479,
    Int.negSucc 1), (486, Int.ofNat 4), (497, Int.ofNat 6), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (391,
    Int.ofNat 20), (429, Int.negSucc 31), (441, Int.ofNat 8), (468, Int.negSucc 11), (482,
    Int.ofNat 12), (490, Int.ofNat 10), (695, Int.ofNat 12), (745, Int.negSucc 11), (752,
    Int.negSucc 11), (759, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (117, Int.negSucc 0), (391,
    Int.ofNat 10), (429, Int.negSucc 17), (441, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 7), (490, Int.ofNat 5), (695, Int.ofNat 6), (745, Int.negSucc 5), (752, Int.negSucc
    5), (759, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 1), (385,
    Int.negSucc 19), (396, Int.ofNat 8), (433, Int.negSucc 21), (471, Int.negSucc 7), (479,
    Int.negSucc 1), (486, Int.ofNat 8), (497, Int.ofNat 14), (773, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 11), (396, Int.ofNat 4), (433, Int.negSucc 11), (471, Int.negSucc 3), (486,
    Int.ofNat 4), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.ofNat 2), (421, Int.ofNat 2), (464, Int.ofNat
    1), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 4), (130, Int.negSucc 0), (404,
    Int.negSucc 3), (412, Int.ofNat 4), (454, Int.negSucc 4), (478, Int.ofNat 2), (485,
    Int.negSucc 3), (504, Int.ofNat 2), (512, Int.ofNat 3), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(124, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (125, Int.ofNat 1), (131,
    Int.negSucc 1), (385, Int.negSucc 1), (433, Int.negSucc 1), (471, Int.negSucc 0), (508,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(126, Int.ofNat 2), (130, Int.ofNat 2), (132,
    Int.negSucc 3), (404, Int.negSucc 1), (454, Int.negSucc 1), (493, Int.negSucc 3), (504,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (128, Int.negSucc 0), (391,
    Int.ofNat 10), (429, Int.negSucc 17), (441, Int.ofNat 4), (468, Int.negSucc 6), (482,
    Int.ofNat 6), (490, Int.ofNat 5), (695, Int.ofNat 6), (745, Int.negSucc 5), (752, Int.negSucc
    5), (759, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.negSucc 0)] }
]

end VOA.DeligneAudit.D4Two.Certificate

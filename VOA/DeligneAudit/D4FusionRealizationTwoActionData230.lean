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
def actionData230 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(300, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(303, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(302, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(301, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(306, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(305, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1), (310, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(304, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(12, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (314, Int.negSucc 1), (318,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (314, Int.negSucc 1), (318,
    Int.negSucc 0), (330, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(307, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1), (317, Int.negSucc 0), (337, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(18, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1), (312, Int.ofNat 4), (336, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(20, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(19, Int.ofNat 1), (312, Int.ofNat 4), (329, Int.negSucc
    1), (336, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(22, Int.ofNat 1), (321, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(24, Int.ofNat 2), (326, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    2), (340, Int.negSucc 1), (353, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(27, Int.ofNat 2), (325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    1), (332, Int.negSucc 0), (340, Int.negSucc 1), (353, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 2), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0),
    (353, Int.negSucc 0), (368, Int.ofNat 1), (681, Int.negSucc 0), (683, Int.ofNat 1), (686,
    Int.ofNat 1), (689, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 4), (315, Int.ofNat
    2), (319, Int.ofNat 1), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 1),
    (368, Int.ofNat 1), (681, Int.negSucc 1), (683, Int.ofNat 2), (686, Int.ofNat 2), (689,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(32, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 1), (324, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.ofNat 1), (338, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    2), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1), (345, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (355, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1), (344, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(41, Int.negSucc 1), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (327, Int.ofNat 1), (365, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (316, Int.ofNat 6), (327, Int.ofNat
    1), (343, Int.ofNat 2), (359, Int.ofNat 1), (365, Int.negSucc 0), (392, Int.negSucc 3), (682,
    Int.negSucc 1), (697, Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 4), (354, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (316, Int.ofNat 8), (327, Int.negSucc
    0), (359, Int.ofNat 1), (392, Int.negSucc 3), (682, Int.negSucc 3), (697, Int.ofNat 4), (700,
    Int.ofNat 4), (703, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.ofNat 2), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    6), (327, Int.ofNat 3), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 1), (386,
    Int.negSucc 1), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 1), (697,
    Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 4), (354, Int.ofNat
    2), (369, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.ofNat 1), (322, Int.ofNat 4), (350, Int.negSucc
    1), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.negSucc 0), (349, Int.negSucc 1), (370,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.negSucc 0), (358, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(53, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 1), (327, Int.ofNat 1), (343, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 1), (363, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.negSucc 0), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (346, Int.ofNat 2), (383, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (323, Int.ofNat 6), (346, Int.negSucc
    1), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (394, Int.negSucc 3), (691,
    Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1), (356, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (323, Int.ofNat 8), (346, Int.negSucc
    5), (373, Int.negSucc 3), (377, Int.ofNat 2), (383, Int.ofNat 4), (394, Int.negSucc 3), (691,
    Int.negSucc 3), (704, Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (361, Int.negSucc 0), (402,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (405, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (335, Int.ofNat 2), (361,
    Int.negSucc 2), (376, Int.negSucc 1), (397, Int.ofNat 1), (402, Int.ofNat 1), (688, Int.ofNat
    2), (701, Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(68, Int.ofNat 2), (323, Int.ofNat 6), (373, Int.negSucc
    0), (377, Int.ofNat 2), (383, Int.ofNat 2), (394, Int.negSucc 3), (691, Int.negSucc 1), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(66, Int.negSucc 3), (69, Int.ofNat 4), (335, Int.ofNat
    20), (361, Int.negSucc 7), (376, Int.negSucc 3), (397, Int.ofNat 5), (402, Int.ofNat 2), (444,
    Int.negSucc 7), (688, Int.ofNat 12), (701, Int.ofNat 12), (722, Int.ofNat 12), (725, Int.ofNat
    12)] },
  { denominator := Int.ofNat 4, terms := [(70, Int.ofNat 4), (342, Int.ofNat 12), (381,
    Int.negSucc 3), (393, Int.ofNat 8), (401, Int.ofNat 2), (405, Int.ofNat 1), (685, Int.ofNat
    4), (698, Int.ofNat 4), (733, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.ofNat 2), (342, Int.ofNat 8), (366, Int.negSucc
    2), (381, Int.negSucc 3), (393, Int.ofNat 4), (401, Int.ofNat 1), (405, Int.ofNat 2), (685,
    Int.ofNat 4), (698, Int.ofNat 4), (733, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    6), (346, Int.ofNat 4), (373, Int.negSucc 0), (383, Int.negSucc 1), (388, Int.negSucc 1),
    (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704, Int.negSucc 1), (711,
    Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 3), (66, Int.negSucc 3), (69, Int.ofNat
    4), (335, Int.ofNat 4), (361, Int.negSucc 3), (387, Int.negSucc 3), (397, Int.ofNat 1), (402,
    Int.ofNat 2), (410, Int.ofNat 4), (444, Int.negSucc 3), (688, Int.ofNat 4), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (342, Int.ofNat
    12), (366, Int.ofNat 6), (393, Int.ofNat 4), (405, Int.negSucc 0), (409, Int.negSucc 3), (438,
    Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 4), (733, Int.ofNat 4), (736, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.negSucc 0), (361, Int.negSucc 1), (376,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.negSucc 0), (400, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.ofNat 1), (366, Int.ofNat 1), (381, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 0), (379, Int.negSucc 1), (428,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.ofNat 2), (432, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (384, Int.ofNat 4), (435, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (352, Int.ofNat 4), (379,
    Int.negSucc 11), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 4), (744, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (85, Int.ofNat 1), (352, Int.ofNat
    10), (379, Int.negSucc 11), (413, Int.negSucc 5), (423, Int.ofNat 5), (428, Int.ofNat 6),
    (446, Int.negSucc 3), (744, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.ofNat 1), (357, Int.ofNat 6), (384, Int.negSucc
    3), (395, Int.ofNat 4), (416, Int.negSucc 1), (427, Int.ofNat 2), (435, Int.ofNat 1), (751,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.ofNat 1), (357, Int.ofNat 8), (384, Int.negSucc
    9), (395, Int.ofNat 4), (416, Int.negSucc 3), (427, Int.ofNat 2), (435, Int.ofNat 4), (751,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(88, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (362, Int.negSucc 1), (419,
    Int.negSucc 1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (403, Int.negSucc 1), (456,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 1), (92, Int.ofNat 1), (362,
    Int.negSucc 0), (419, Int.negSucc 1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(95, Int.negSucc 0), (352, Int.ofNat 2), (379,
    Int.negSucc 7), (413, Int.negSucc 2), (423, Int.ofNat 2), (428, Int.ofNat 2), (744, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.negSucc 1), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (372, Int.ofNat 4), (403,
    Int.negSucc 7), (426, Int.negSucc 3), (449, Int.ofNat 2), (456, Int.ofNat 3), (758, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(98, Int.ofNat 2), (357, Int.ofNat 6), (384, Int.negSucc
    1), (395, Int.ofNat 4), (416, Int.negSucc 0), (427, Int.ofNat 2), (435, Int.ofNat 1), (751,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(97, Int.negSucc 3), (99, Int.ofNat 4), (372, Int.ofNat
    20), (403, Int.negSucc 13), (426, Int.negSucc 11), (445, Int.ofNat 8), (449, Int.ofNat 5),
    (456, Int.ofNat 7), (758, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(100, Int.ofNat 1), (431, Int.ofNat 2), (452, Int.ofNat
    1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.negSucc 1), (352, Int.ofNat 4), (379, Int.negSucc 11), (389, Int.negSucc 3),
    (413, Int.negSucc 5), (423, Int.ofNat 2), (428, Int.ofNat 8), (446, Int.negSucc 3), (461,
    Int.ofNat 4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (357, Int.ofNat
    6), (384, Int.ofNat 4), (395, Int.ofNat 2), (416, Int.negSucc 0), (427, Int.ofNat 2), (435,
    Int.negSucc 0), (440, Int.negSucc 1), (460, Int.negSucc 1), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 3), (97, Int.negSucc 3), (99, Int.ofNat
    4), (372, Int.ofNat 4), (403, Int.negSucc 7), (411, Int.negSucc 3), (426, Int.negSucc 3),
    (439, Int.negSucc 3), (445, Int.ofNat 4), (449, Int.ofNat 1), (456, Int.ofNat 5), (758,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 11), (390, Int.ofNat 4), (421, Int.negSucc 11), (464, Int.negSucc 3), (475,
    Int.ofNat 8), (487, Int.ofNat 4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 1), (380, Int.negSucc 7), (390, Int.ofNat 4), (421, Int.negSucc 9), (464,
    Int.negSucc 3), (475, Int.ofNat 6), (487, Int.ofNat 4), (494, Int.negSucc 1), (765, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (433, Int.ofNat 2), (479, Int.ofNat
    2), (497, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 4), (429,
    Int.negSucc 15), (468, Int.negSucc 3), (482, Int.ofNat 4), (490, Int.ofNat 6), (695, Int.ofNat
    4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 1), (417, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (117, Int.ofNat 1), (391,
    Int.ofNat 10), (429, Int.negSucc 17), (447, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 5), (490, Int.ofNat 7), (695, Int.ofNat 6), (745, Int.negSucc 5), (752, Int.negSucc
    5), (759, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (385, Int.negSucc 11), (396,
    Int.ofNat 12), (433, Int.negSucc 1), (471, Int.negSucc 3), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 6), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 4), (385, Int.negSucc 27), (396, Int.ofNat 28), (433, Int.negSucc 11), (471,
    Int.negSucc 11), (486, Int.ofNat 4), (497, Int.ofNat 24), (773, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (380, Int.negSucc 3), (421,
    Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (404, Int.negSucc 1), (454,
    Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(120, Int.negSucc 1), (124, Int.ofNat 1), (380,
    Int.negSucc 1), (421, Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(125, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.negSucc 1), (126, Int.ofNat 1), (404,
    Int.negSucc 0), (454, Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(128, Int.negSucc 0), (391, Int.ofNat 2), (429,
    Int.negSucc 9), (468, Int.negSucc 2), (482, Int.ofNat 2), (490, Int.ofNat 3), (695, Int.ofNat
    2), (745, Int.negSucc 1), (752, Int.negSucc 1), (759, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 1), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.negSucc 0), (404, Int.negSucc 7), (412,
    Int.ofNat 4), (454, Int.negSucc 6), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 5), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(131, Int.ofNat 2), (385, Int.negSucc 11), (396,
    Int.ofNat 12), (471, Int.negSucc 2), (479, Int.ofNat 2), (486, Int.ofNat 4), (497, Int.ofNat
    6), (508, Int.ofNat 1), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 4), (130, Int.negSucc 5), (132,
    Int.ofNat 4), (404, Int.negSucc 23), (412, Int.ofNat 16), (454, Int.negSucc 23), (478,
    Int.negSucc 3), (485, Int.negSucc 15), (493, Int.ofNat 4), (504, Int.ofNat 7), (512, Int.ofNat
    18), (780, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.negSucc 1), (391, Int.ofNat 4), (429, Int.negSucc 19), (441,
    Int.negSucc 3), (447, Int.ofNat 4), (462, Int.negSucc 3), (468, Int.negSucc 5), (482,
    Int.ofNat 2), (490, Int.ofNat 10), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (404,
    Int.negSucc 5), (412, Int.ofNat 4), (454, Int.negSucc 5), (485, Int.negSucc 3), (504,
    Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (415, Int.negSucc 2), (465,
    Int.negSucc 1), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 0), (544,
    Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

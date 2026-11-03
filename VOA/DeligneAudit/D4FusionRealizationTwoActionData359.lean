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
def actionData359 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(767, Int.negSucc 0), (825, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(831, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(834, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(750, Int.ofNat 1), (770, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(771, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(772, Int.negSucc 0), (838, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(820, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(774, Int.ofNat 1), (826, Int.negSucc 0), (832,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(775, Int.negSucc 0), (825, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(828, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(834, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(757, Int.ofNat 1), (778, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(779, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(817, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(781, Int.ofNat 1), (826, Int.ofNat 1), (829, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(782, Int.negSucc 0), (825, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(828, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(831, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(764, Int.ofNat 1), (785, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(786, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.ofNat 1), (709, Int.ofNat 2), (824, Int.ofNat
    4), (832, Int.negSucc 5), (840, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(788, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(789, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(772, Int.ofNat 1), (792, Int.ofNat 1), (838, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(793, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(794, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.ofNat 1), (709, Int.ofNat 2), (824, Int.ofNat
    4), (832, Int.negSucc 5), (840, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(796, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(797, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(772, Int.ofNat 1), (800, Int.ofNat 1), (838, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(801, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.ofNat 1), (709, Int.ofNat 2), (824, Int.ofNat
    4), (832, Int.negSucc 5), (840, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(803, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(804, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(772, Int.ofNat 1), (807, Int.ofNat 1), (838, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(808, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(809, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(810, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(811, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(681, Int.negSucc 2), (689, Int.ofNat 3), (812,
    Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(813, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(814, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(815, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(817, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(818, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(820, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(822, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(823, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.negSucc 0), (824, Int.negSucc 5), (826,
    Int.negSucc 1), (829, Int.negSucc 1), (832, Int.ofNat 6), (840, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(825, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.negSucc 0), (826, Int.negSucc 1), (829,
    Int.negSucc 1), (840, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(827, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(828, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.negSucc 0), (826, Int.negSucc 1), (829,
    Int.negSucc 1), (840, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(830, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(831, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(696, Int.negSucc 0), (826, Int.negSucc 1), (829,
    Int.negSucc 1), (840, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(833, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(834, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(838, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(839, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.negSucc 2), (832, Int.ofNat 3), (840,
    Int.ofNat 3)] },
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
    (353, Int.negSucc 0), (368, Int.ofNat 1), (681, Int.negSucc 1), (683, Int.ofNat 1), (686,
    Int.ofNat 1), (689, Int.ofNat 2), (812, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 4), (315, Int.ofNat
    2), (319, Int.ofNat 1), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 1),
    (368, Int.ofNat 1), (681, Int.negSucc 3), (683, Int.ofNat 2), (686, Int.ofNat 2), (689,
    Int.ofNat 4), (812, Int.ofNat 2)] },
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
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (316, Int.ofNat 8), (343, Int.ofNat
    2), (359, Int.ofNat 1), (365, Int.negSucc 0), (392, Int.negSucc 3), (682, Int.negSucc 5),
    (697, Int.ofNat 4), (700, Int.ofNat 4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 4), (354, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (316, Int.ofNat 12), (327,
    Int.negSucc 2), (359, Int.ofNat 1), (392, Int.negSucc 3), (682, Int.negSucc 11), (697,
    Int.ofNat 8), (700, Int.ofNat 8), (703, Int.ofNat 8), (813, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.ofNat 2), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    8), (327, Int.ofNat 2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 1), (386,
    Int.negSucc 1), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697,
    Int.ofNat 4), (700, Int.ofNat 4), (703, Int.ofNat 4), (813, Int.ofNat 2)] },
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
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (323, Int.ofNat 8), (346, Int.negSucc
    3), (373, Int.negSucc 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (394, Int.negSucc 3), (691,
    Int.negSucc 1), (704, Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1), (356, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (323, Int.ofNat 12), (346,
    Int.negSucc 9), (373, Int.negSucc 5), (377, Int.ofNat 2), (383, Int.ofNat 4), (394,
    Int.negSucc 3), (691, Int.negSucc 3), (704, Int.negSucc 7), (711, Int.ofNat 8), (714,
    Int.ofNat 8), (818, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (361, Int.negSucc 0), (402,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (405, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.negSucc 1), (335, Int.ofNat 8), (361,
    Int.negSucc 7), (376, Int.negSucc 3), (397, Int.ofNat 3), (402, Int.ofNat 2), (688, Int.ofNat
    4), (701, Int.ofNat 8), (722, Int.ofNat 8), (725, Int.ofNat 8), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(68, Int.ofNat 1), (323, Int.ofNat 4), (346, Int.negSucc
    0), (373, Int.negSucc 0), (377, Int.ofNat 1), (383, Int.ofNat 1), (394, Int.negSucc 1), (691,
    Int.negSucc 0), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2), (818, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.negSucc 1), (69, Int.ofNat 2), (335, Int.ofNat
    16), (361, Int.negSucc 6), (376, Int.negSucc 1), (397, Int.ofNat 4), (402, Int.ofNat 1), (444,
    Int.negSucc 3), (688, Int.ofNat 6), (701, Int.ofNat 12), (722, Int.ofNat 12), (725, Int.ofNat
    12), (815, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 2), (342, Int.ofNat 8), (366, Int.negSucc
    0), (381, Int.negSucc 1), (393, Int.ofNat 4), (401, Int.ofNat 1), (405, Int.ofNat 1), (685,
    Int.ofNat 2), (698, Int.ofNat 4), (733, Int.ofNat 4), (736, Int.ofNat 4), (814, Int.negSucc
    1)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.ofNat 2), (342, Int.ofNat 12), (366,
    Int.negSucc 4), (381, Int.negSucc 3), (393, Int.ofNat 4), (401, Int.ofNat 1), (405, Int.ofNat
    3), (685, Int.ofNat 4), (698, Int.ofNat 8), (733, Int.ofNat 8), (736, Int.ofNat 8), (814,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    8), (346, Int.ofNat 2), (373, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.negSucc 1),
    (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704, Int.negSucc 3), (711,
    Int.ofNat 4), (714, Int.ofNat 4), (818, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (66, Int.negSucc 1), (69, Int.ofNat
    2), (335, Int.ofNat 4), (361, Int.negSucc 2), (387, Int.negSucc 1), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (410, Int.ofNat 2), (444, Int.negSucc 1), (688, Int.ofNat 2), (701, Int.ofNat
    4), (722, Int.ofNat 4), (725, Int.ofNat 4), (815, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 1), (70, Int.ofNat 1), (342, Int.ofNat
    4), (366, Int.ofNat 1), (393, Int.ofNat 1), (409, Int.negSucc 0), (438, Int.negSucc 0), (685,
    Int.ofNat 1), (698, Int.ofNat 2), (733, Int.ofNat 2), (736, Int.ofNat 2), (814, Int.negSucc
    0)] },
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
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (352, Int.ofNat 8), (379,
    Int.negSucc 15), (413, Int.negSucc 5), (423, Int.ofNat 6), (428, Int.ofNat 4), (694,
    Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (85, Int.ofNat 1), (352, Int.ofNat
    16), (379, Int.negSucc 17), (413, Int.negSucc 8), (423, Int.ofNat 8), (428, Int.ofNat 6),
    (446, Int.negSucc 3), (694, Int.negSucc 5), (744, Int.ofNat 12), (821, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.ofNat 1), (357, Int.ofNat 8), (384, Int.negSucc
    5), (395, Int.ofNat 4), (416, Int.negSucc 2), (427, Int.ofNat 2), (435, Int.ofNat 2), (693,
    Int.negSucc 1), (751, Int.ofNat 4), (819, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.ofNat 1), (357, Int.ofNat 12), (384,
    Int.negSucc 13), (395, Int.ofNat 4), (416, Int.negSucc 5), (427, Int.ofNat 2), (435, Int.ofNat
    6), (693, Int.negSucc 3), (751, Int.ofNat 8), (819, Int.negSucc 3)] },
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
  { denominator := Int.ofNat 1, terms := [(95, Int.negSucc 0), (352, Int.ofNat 4), (379,
    Int.negSucc 9), (413, Int.negSucc 3), (423, Int.ofNat 3), (428, Int.ofNat 2), (694,
    Int.negSucc 1), (744, Int.ofNat 4), (821, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.negSucc 1), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (372, Int.ofNat 8), (403,
    Int.negSucc 9), (426, Int.negSucc 3), (449, Int.ofNat 3), (456, Int.ofNat 4), (692, Int.ofNat
    4), (758, Int.ofNat 8), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(98, Int.ofNat 1), (357, Int.ofNat 4), (384, Int.negSucc
    1), (395, Int.ofNat 2), (416, Int.negSucc 0), (427, Int.ofNat 1), (435, Int.ofNat 1), (693,
    Int.negSucc 0), (751, Int.ofNat 2), (819, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.negSucc 1), (99, Int.ofNat 2), (372, Int.ofNat
    16), (403, Int.negSucc 9), (426, Int.negSucc 5), (445, Int.ofNat 4), (449, Int.ofNat 4), (456,
    Int.ofNat 5), (692, Int.ofNat 6), (758, Int.ofNat 12), (816, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(100, Int.ofNat 1), (431, Int.ofNat 2), (452, Int.ofNat
    1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.negSucc 1), (352, Int.ofNat 8), (379, Int.negSucc 15), (389, Int.negSucc 3),
    (413, Int.negSucc 7), (423, Int.ofNat 4), (428, Int.ofNat 8), (446, Int.negSucc 3), (461,
    Int.ofNat 4), (694, Int.negSucc 3), (744, Int.ofNat 8), (821, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (357, Int.ofNat
    8), (384, Int.ofNat 2), (395, Int.ofNat 2), (416, Int.negSucc 1), (427, Int.ofNat 2), (440,
    Int.negSucc 1), (460, Int.negSucc 1), (693, Int.negSucc 1), (751, Int.ofNat 4), (819,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (97, Int.negSucc 1), (99, Int.ofNat
    2), (372, Int.ofNat 4), (403, Int.negSucc 4), (411, Int.negSucc 1), (426, Int.negSucc 1),
    (439, Int.negSucc 1), (445, Int.ofNat 2), (449, Int.ofNat 1), (456, Int.ofNat 3), (692,
    Int.ofNat 2), (758, Int.ofNat 4), (816, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 15), (390, Int.ofNat 8), (421, Int.negSucc 15), (464, Int.negSucc 5), (475,
    Int.ofNat 12), (487, Int.ofNat 4), (765, Int.ofNat 8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 1), (380, Int.negSucc 11), (390, Int.ofNat 8), (421, Int.negSucc 13), (464,
    Int.negSucc 5), (475, Int.ofNat 10), (487, Int.ofNat 4), (494, Int.negSucc 1), (765, Int.ofNat
    8), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (433, Int.ofNat 2), (479, Int.ofNat
    2), (497, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (391, Int.ofNat 8), (429,
    Int.negSucc 19), (468, Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 8), (695, Int.ofNat
    12), (745, Int.negSucc 7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 1), (417, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (117, Int.ofNat 1), (391,
    Int.ofNat 16), (429, Int.negSucc 23), (447, Int.ofNat 4), (468, Int.negSucc 8), (482,
    Int.ofNat 8), (490, Int.ofNat 10), (695, Int.ofNat 18), (745, Int.negSucc 11), (752,
    Int.negSucc 11), (759, Int.ofNat 12), (823, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (385, Int.negSucc 15), (396,
    Int.ofNat 16), (433, Int.negSucc 5), (471, Int.negSucc 5), (479, Int.ofNat 2), (486, Int.ofNat
    4), (497, Int.ofNat 10), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 4), (385, Int.negSucc 39), (396, Int.ofNat 40), (433, Int.negSucc 23), (471,
    Int.negSucc 17), (486, Int.ofNat 4), (497, Int.ofNat 36), (773, Int.ofNat 24), (820,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (380, Int.negSucc 3), (421,
    Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (404, Int.negSucc 1), (454,
    Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(120, Int.negSucc 1), (124, Int.ofNat 1), (380,
    Int.negSucc 1), (421, Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(125, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

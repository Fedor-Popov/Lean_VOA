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
def actionData115 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(357, Int.ofNat 2), (384, Int.negSucc 1), (416,
    Int.negSucc 0), (435, Int.ofNat 1), (751, Int.ofNat 2), (819, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(695, Int.ofNat 2), (752, Int.negSucc 3), (823,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(696, Int.ofNat 1), (753, Int.negSucc 0), (829,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(754, Int.negSucc 0), (827, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(755, Int.negSucc 0), (833, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(756, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(836, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(372, Int.negSucc 3), (403, Int.ofNat 2), (449,
    Int.negSucc 0), (456, Int.negSucc 0), (758, Int.negSucc 3), (816, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(695, Int.ofNat 2), (823, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(696, Int.ofNat 1), (760, Int.ofNat 1), (832, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(761, Int.ofNat 1), (827, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(762, Int.negSucc 0), (830, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(763, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(835, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(380, Int.ofNat 2), (390, Int.negSucc 1), (421,
    Int.ofNat 2), (464, Int.ofNat 1), (475, Int.negSucc 1), (708, Int.ofNat 2), (765, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(710, Int.negSucc 0), (767, Int.ofNat 2), (825,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(768, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(769, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(750, Int.negSucc 0), (770, Int.negSucc 1), (837,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(838, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 1), (396, Int.ofNat 2), (433,
    Int.negSucc 1), (471, Int.negSucc 0), (497, Int.ofNat 2), (707, Int.negSucc 1), (773,
    Int.ofNat 2), (820, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(696, Int.negSucc 0), (774, Int.negSucc 1), (824,
    Int.ofNat 2), (829, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(710, Int.ofNat 1), (775, Int.negSucc 1), (825,
    Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(776, Int.negSucc 0), (828, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(777, Int.negSucc 0), (834, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(757, Int.negSucc 0), (778, Int.negSucc 1), (836,
    Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(404, Int.ofNat 2), (412, Int.negSucc 3), (454,
    Int.ofNat 2), (504, Int.negSucc 0), (512, Int.negSucc 1), (706, Int.negSucc 3), (780,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(710, Int.ofNat 1), (782, Int.ofNat 2), (825,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(783, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(784, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(764, Int.negSucc 0), (785, Int.negSucc 1), (835,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(430, Int.ofNat 2), (442, Int.negSucc 1), (480,
    Int.ofNat 2), (516, Int.ofNat 1), (528, Int.negSucc 1), (709, Int.negSucc 1), (741, Int.ofNat
    2), (766, Int.ofNat 2), (787, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(743, Int.negSucc 0), (789, Int.ofNat 2), (828,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(790, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(791, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(772, Int.negSucc 0), (792, Int.negSucc 1), (838,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(839, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(430, Int.negSucc 1), (448, Int.ofNat 2), (495,
    Int.negSucc 1), (524, Int.negSucc 0), (550, Int.ofNat 2), (696, Int.negSucc 1), (709,
    Int.negSucc 1), (729, Int.negSucc 1), (774, Int.negSucc 1), (795, Int.ofNat 2), (824,
    Int.ofNat 4), (829, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(796, Int.negSucc 1), (830, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(732, Int.ofNat 1), (797, Int.negSucc 1), (831,
    Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(798, Int.negSucc 0), (835, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(799, Int.negSucc 0), (837, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(772, Int.negSucc 0), (800, Int.negSucc 1), (838,
    Int.negSucc 2)] },
  { denominator := Int.ofNat 3, terms := [(839, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(430, Int.ofNat 4), (463, Int.negSucc 3), (510,
    Int.ofNat 2), (556, Int.negSucc 0), (560, Int.negSucc 1), (709, Int.negSucc 3), (717,
    Int.negSucc 3), (781, Int.negSucc 3), (802, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(721, Int.ofNat 1), (804, Int.ofNat 2), (834, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(805, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(806, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(772, Int.negSucc 0), (807, Int.negSucc 1), (838,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(813, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(814, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(815, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(816, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(818, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(819, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(820, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(821, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(823, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 1), (832, Int.negSucc 0), (840,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(825, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 1), (832, Int.negSucc 0), (840,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(828, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.negSucc 0), (832, Int.ofNat 1), (840,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(830, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(831, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(824, Int.ofNat 1), (832, Int.negSucc 0), (840,
    Int.negSucc 0)] },
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
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 2), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (348, Int.negSucc 1), (353, Int.negSucc 0),
    (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 1), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0),
    (353, Int.negSucc 0), (368, Int.ofNat 1)] },
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
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (316, Int.ofNat 4), (327, Int.ofNat
    1), (365, Int.ofNat 1), (386, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (349, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (316, Int.ofNat 4), (327, Int.ofNat
    2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.ofNat 1), (386, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (359, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.negSucc 1), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    8), (327, Int.ofNat 4), (343, Int.ofNat 2), (359, Int.negSucc 0), (386, Int.negSucc 5), (392,
    Int.negSucc 1), (408, Int.ofNat 2)] },
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
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (323, Int.ofNat 4), (346, Int.negSucc
    1), (373, Int.negSucc 1), (377, Int.ofNat 4), (383, Int.ofNat 2), (388, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.ofNat 1), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (323, Int.ofNat 4), (373, Int.negSucc
    0), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (346, Int.ofNat 2), (377, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.negSucc 0), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (335, Int.ofNat 4), (361, Int.negSucc
    0), (376, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 1), (402, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (342, Int.ofNat 8), (366, Int.ofNat
    2), (405, Int.ofNat 1), (438, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.ofNat 2), (335, Int.ofNat 8), (376, Int.negSucc
    3), (387, Int.ofNat 8), (397, Int.ofNat 1), (402, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(68, Int.ofNat 1), (323, Int.ofNat 2), (346, Int.ofNat
    1), (377, Int.ofNat 1), (383, Int.ofNat 1), (388, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(69, Int.ofNat 2), (335, Int.ofNat 4), (361, Int.ofNat
    1), (376, Int.negSucc 1), (387, Int.ofNat 4), (402, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (70, Int.negSucc 1), (342, Int.ofNat
    4), (366, Int.negSucc 0), (381, Int.negSucc 1), (401, Int.ofNat 1), (405, Int.ofNat 1), (438,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 1), (366, Int.negSucc 0), (401,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    8), (346, Int.ofNat 2), (373, Int.negSucc 1), (377, Int.ofNat 4), (383, Int.ofNat 2), (388,
    Int.negSucc 5), (394, Int.negSucc 1), (459, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (69, Int.ofNat 2), (335, Int.ofNat
    8), (361, Int.ofNat 1), (376, Int.negSucc 3), (387, Int.ofNat 6), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (410, Int.negSucc 1), (444, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.negSucc 1), (342, Int.ofNat
    8), (366, Int.ofNat 2), (393, Int.negSucc 1), (405, Int.ofNat 1), (409, Int.ofNat 2), (438,
    Int.negSucc 9)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.ofNat 1), (361, Int.ofNat 2), (376, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.negSucc 0), (400, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 0), (366, Int.negSucc 0), (381,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (352, Int.ofNat 4), (379, Int.negSucc
    5), (389, Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.negSucc 1), (432, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (357, Int.ofNat 8), (384, Int.negSucc
    3), (416, Int.negSucc 3), (427, Int.ofNat 8), (435, Int.ofNat 2), (440, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.ofNat 1), (352, Int.ofNat 8), (379, Int.negSucc
    7), (389, Int.ofNat 8), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.ofNat 1), (352, Int.ofNat 4), (379, Int.negSucc
    1), (389, Int.ofNat 4), (413, Int.negSucc 0), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (86, Int.negSucc 0), (357, Int.ofNat
    4), (384, Int.negSucc 5), (416, Int.negSucc 2), (427, Int.ofNat 6), (435, Int.ofNat 2), (440,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 2), (419, Int.ofNat 2), (453, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (372, Int.ofNat 8), (403, Int.negSucc
    1), (426, Int.negSucc 7), (439, Int.ofNat 8), (449, Int.ofNat 2), (456, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 2), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.negSucc 1), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(95, Int.ofNat 1), (352, Int.ofNat 4), (379, Int.negSucc
    1), (389, Int.ofNat 4), (423, Int.ofNat 1), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (97, Int.negSucc 1), (372, Int.ofNat
    8), (403, Int.negSucc 5), (426, Int.negSucc 11), (439, Int.ofNat 8), (449, Int.ofNat 3), (456,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.negSucc 1), (357, Int.ofNat
    4), (384, Int.negSucc 7), (416, Int.negSucc 3), (427, Int.ofNat 6), (435, Int.ofNat 2), (440,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (99, Int.negSucc 1), (372, Int.ofNat
    4), (403, Int.negSucc 3), (426, Int.negSucc 5), (439, Int.ofNat 4), (449, Int.ofNat 2), (456,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 3), (100, Int.negSucc 1), (367,
    Int.negSucc 2), (431, Int.negSucc 3), (452, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (352, Int.ofNat 16), (379, Int.negSucc 7), (389, Int.ofNat 12), (413,
    Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 8), (446, Int.negSucc 3), (461,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (98, Int.negSucc 0), (357, Int.ofNat
    4), (384, Int.negSucc 2), (395, Int.negSucc 0), (416, Int.negSucc 2), (427, Int.ofNat 5),
    (435, Int.ofNat 1), (440, Int.negSucc 4), (460, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (99, Int.negSucc 1), (372, Int.ofNat
    8), (403, Int.negSucc 2), (411, Int.negSucc 1), (426, Int.negSucc 9), (439, Int.ofNat 10),
    (445, Int.negSucc 1), (449, Int.ofNat 3), (456, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.negSucc 0), (403, Int.negSucc 1), (426,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (380, Int.negSucc 7), (390,
    Int.ofNat 8), (464, Int.negSucc 3), (475, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.ofNat 2), (380,
    Int.negSucc 15), (390, Int.ofNat 16), (464, Int.negSucc 5), (475, Int.ofNat 12), (487,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (391, Int.ofNat 8), (429,
    Int.negSucc 11), (441, Int.ofNat 8), (468, Int.negSucc 3), (482, Int.ofNat 4), (490, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (421, Int.ofNat 2), (475,
    Int.negSucc 1), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 2), (118, Int.negSucc 0), (385,
    Int.negSucc 3), (433, Int.negSucc 5), (471, Int.negSucc 1), (479, Int.negSucc 1), (486,
    Int.ofNat 4), (497, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (391,
    Int.ofNat 8), (429, Int.negSucc 19), (441, Int.ofNat 8), (468, Int.negSucc 5), (482, Int.ofNat
    6), (490, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 1), (117, Int.negSucc 0), (391,
    Int.ofNat 4), (429, Int.negSucc 11), (441, Int.ofNat 4), (468, Int.negSucc 2), (482, Int.ofNat
    4), (490, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 1), (385,
    Int.negSucc 11), (433, Int.negSucc 13), (471, Int.negSucc 3), (479, Int.negSucc 1), (486,
    Int.ofNat 8), (497, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (433, Int.negSucc 7), (471, Int.negSucc 1), (486, Int.ofNat 4), (497,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.ofNat 2), (421, Int.ofNat 2), (464, Int.ofNat
    1), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 4), (130, Int.negSucc 0), (404,
    Int.negSucc 1), (454, Int.negSucc 2), (478, Int.ofNat 2), (485, Int.negSucc 3), (504,
    Int.ofNat 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.negSucc 1), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(124, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

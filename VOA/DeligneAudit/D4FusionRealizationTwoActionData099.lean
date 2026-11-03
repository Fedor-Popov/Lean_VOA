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
def actionData099 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(677, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 8, terms := [(299, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(645, Int.negSucc 0), (647, Int.ofNat 2), (793,
    Int.negSucc 1), (794, Int.ofNat 4), (801, Int.negSucc 1), (808, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(670, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(677, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(645, Int.negSucc 0), (652, Int.ofNat 2), (793,
    Int.negSucc 1), (794, Int.ofNat 4), (801, Int.negSucc 1), (808, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(668, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(677, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (430, Int.negSucc 3), (442,
    Int.ofNat 4), (443, Int.negSucc 7), (448, Int.ofNat 4), (463, Int.ofNat 4), (480, Int.ofNat
    8), (528, Int.ofNat 4), (535, Int.negSucc 3), (547, Int.negSucc 7), (550, Int.ofNat 4), (556,
    Int.ofNat 1), (560, Int.ofNat 2), (696, Int.negSucc 11), (709, Int.negSucc 7), (729,
    Int.negSucc 3), (741, Int.negSucc 3), (746, Int.ofNat 4), (753, Int.ofNat 4), (760,
    Int.negSucc 7), (766, Int.ofNat 4), (774, Int.ofNat 4), (781, Int.negSucc 7), (787, Int.ofNat
    4), (795, Int.ofNat 4), (824, Int.ofNat 4), (826, Int.negSucc 3), (829, Int.negSucc 3), (832,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(481, Int.ofNat 2), (489, Int.negSucc 3), (496,
    Int.ofNat 2), (511, Int.ofNat 1), (710, Int.negSucc 4), (767, Int.ofNat 2), (775, Int.ofNat
    2), (782, Int.negSucc 1), (825, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(534, Int.negSucc 1), (549, Int.ofNat 4), (552,
    Int.negSucc 1), (562, Int.negSucc 0), (743, Int.ofNat 3), (776, Int.ofNat 2), (783,
    Int.negSucc 1), (789, Int.negSucc 1), (828, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(530, Int.negSucc 3), (537, Int.ofNat 4), (558,
    Int.negSucc 0), (732, Int.ofNat 6), (768, Int.ofNat 4), (784, Int.negSucc 3), (797,
    Int.negSucc 3), (831, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(583, Int.ofNat 4), (589, Int.negSucc 3), (602,
    Int.ofNat 1), (764, Int.negSucc 5), (785, Int.negSucc 3), (790, Int.negSucc 3), (798,
    Int.negSucc 3), (835, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(518, Int.ofNat 1), (522, Int.negSucc 1), (526,
    Int.ofNat 1), (721, Int.negSucc 2), (769, Int.ofNat 2), (777, Int.ofNat 2), (804, Int.negSucc
    1), (834, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(569, Int.negSucc 0), (576, Int.ofNat 2), (577,
    Int.negSucc 0), (757, Int.ofNat 3), (778, Int.ofNat 2), (791, Int.negSucc 1), (805,
    Int.negSucc 1), (836, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(563, Int.negSucc 0), (570, Int.ofNat 1), (750,
    Int.ofNat 3), (770, Int.ofNat 2), (799, Int.negSucc 1), (806, Int.negSucc 1), (837, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(604, Int.ofNat 1), (614, Int.negSucc 0), (772,
    Int.negSucc 4), (792, Int.negSucc 1), (800, Int.negSucc 1), (807, Int.negSucc 1), (838,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 6, terms := [(793, Int.negSucc 2), (794, Int.ofNat 6), (801,
    Int.negSucc 2), (808, Int.negSucc 2), (839, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 6, terms := [(793, Int.negSucc 2), (794, Int.ofNat 6), (801,
    Int.negSucc 2), (808, Int.negSucc 2), (839, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 6, terms := [(793, Int.negSucc 2), (794, Int.ofNat 6), (801,
    Int.negSucc 2), (808, Int.negSucc 2), (839, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 6, terms := [(793, Int.negSucc 2), (794, Int.ofNat 6), (801,
    Int.negSucc 2), (808, Int.negSucc 2), (839, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(300, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(303, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(302, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(301, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 1), (311, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(306, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(305, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(304, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(12, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (314, Int.negSucc 1), (330, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1), (313, Int.negSucc 1), (337, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (314, Int.negSucc 1), (318,
    Int.negSucc 0), (330, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(307, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 1), (313, Int.negSucc 1), (317,
    Int.negSucc 0), (337, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(18, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(20, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(19, Int.ofNat 1), (329, Int.negSucc 1), (336,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(22, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(23, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(24, Int.ofNat 2), (326, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 1), (333, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (332, Int.negSucc
    1), (340, Int.negSucc 1), (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(27, Int.ofNat 2), (325, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.ofNat 1), (339, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    1), (332, Int.negSucc 0), (340, Int.negSucc 1), (353, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 1), (315, Int.ofNat
    2), (319, Int.ofNat 1), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0),
    (353, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (315, Int.ofNat 2), (319, Int.ofNat
    1), (332, Int.negSucc 1), (340, Int.negSucc 0), (348, Int.negSucc 0), (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(32, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 1), (324, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 2), (315, Int.ofNat
    2), (332, Int.negSucc 0), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0),
    (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.negSucc 0), (345, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.negSucc 0), (344, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(41, Int.ofNat 2), (360, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (327, Int.ofNat 1), (365, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (370, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (316, Int.ofNat 4), (327, Int.ofNat
    2), (343, Int.negSucc 1), (359, Int.negSucc 0), (365, Int.negSucc 0), (408, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 4), (369, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (359, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.ofNat 2), (364, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    4), (327, Int.ofNat 4), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 1), (386,
    Int.negSucc 1), (392, Int.negSucc 1), (408, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 4), (354, Int.ofNat
    2), (369, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(38, Int.negSucc 0), (350, Int.ofNat 2), (355, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.ofNat 1), (334, Int.ofNat 4), (349, Int.ofNat
    2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.ofNat 1), (358, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(53, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 1), (316, Int.ofNat 4), (327, Int.ofNat
    1), (343, Int.negSucc 1), (408, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 1), (363, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.negSucc 0), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (346, Int.negSucc 1), (383,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (346, Int.negSucc 3), (373,
    Int.negSucc 0), (377, Int.ofNat 2), (383, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.negSucc 0), (346, Int.negSucc 1), (377,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.negSucc 0), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (361, Int.ofNat 1), (402, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (405, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.ofNat 2), (335, Int.ofNat 8), (376, Int.negSucc
    3), (397, Int.ofNat 1), (402, Int.ofNat 2), (410, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.ofNat 1), (371, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (68, Int.ofNat 1), (323, Int.ofNat
    2), (346, Int.negSucc 0), (373, Int.negSucc 0), (377, Int.ofNat 1), (383, Int.ofNat 1), (459,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(69, Int.ofNat 2), (335, Int.ofNat 4), (361, Int.ofNat
    1), (376, Int.negSucc 1), (402, Int.ofNat 1), (410, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 2), (342, Int.ofNat 4), (366, Int.ofNat
    1), (381, Int.negSucc 1), (401, Int.ofNat 1), (409, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.ofNat 2), (366, Int.ofNat 1), (401, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (59, Int.negSucc 1), (68, Int.ofNat
    2), (346, Int.negSucc 1), (383, Int.ofNat 2), (388, Int.ofNat 2), (394, Int.ofNat 2), (459,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (69, Int.ofNat 2), (335, Int.ofNat
    4), (361, Int.ofNat 3), (387, Int.ofNat 2), (402, Int.negSucc 0), (410, Int.negSucc 1), (444,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (70, Int.ofNat 2), (342, Int.ofNat
    4), (366, Int.ofNat 4), (393, Int.ofNat 2), (405, Int.negSucc 0), (409, Int.negSucc 1), (438,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.ofNat 1), (335, Int.ofNat 8), (361, Int.negSucc
    1), (376, Int.negSucc 3), (397, Int.ofNat 2), (402, Int.ofNat 4), (410, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.ofNat 1), (400, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.ofNat 1), (342, Int.ofNat 4), (366, Int.negSucc
    0), (381, Int.negSucc 1), (401, Int.ofNat 2), (405, Int.ofNat 1), (409, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 0), (379, Int.negSucc 1), (428,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (347, Int.negSucc 3), (420,
    Int.ofNat 2), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (384, Int.negSucc 3), (435,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (379, Int.negSucc 7), (413,
    Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.negSucc 0), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(85, Int.negSucc 0), (379, Int.negSucc 5), (413,
    Int.negSucc 0), (423, Int.ofNat 2), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (384, Int.negSucc 5), (416,
    Int.negSucc 0), (427, Int.ofNat 2), (435, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.negSucc 0), (384, Int.negSucc 1), (427,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 2), (419, Int.negSucc 1), (453,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (403, Int.ofNat 2), (456, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (91, Int.ofNat 1), (347,
    Int.negSucc 1), (420, Int.ofNat 2), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (95, Int.ofNat 1), (352, Int.ofNat
    4), (379, Int.negSucc 5), (413, Int.negSucc 1), (423, Int.ofNat 3), (428, Int.ofNat 6), (461,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.ofNat 2), (372, Int.ofNat 8), (403, Int.negSucc
    1), (411, Int.ofNat 8), (426, Int.negSucc 3), (449, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (98, Int.ofNat 1), (357, Int.ofNat
    2), (384, Int.negSucc 3), (416, Int.negSucc 0), (427, Int.ofNat 3), (435, Int.ofNat 2), (460,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(99, Int.ofNat 1), (372, Int.ofNat 2), (411, Int.ofNat
    2), (426, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(100, Int.ofNat 1), (431, Int.negSucc 1), (452,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (85,
    Int.negSucc 1), (95, Int.ofNat 2), (379, Int.negSucc 7), (389, Int.negSucc 3), (423, Int.ofNat
    4), (428, Int.ofNat 8), (446, Int.ofNat 4), (461, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.negSucc 1), (98, Int.ofNat
    2), (384, Int.negSucc 5), (395, Int.negSucc 1), (427, Int.ofNat 2), (435, Int.ofNat 4), (440,
    Int.ofNat 2), (460, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 2), (99, Int.ofNat 2), (372, Int.ofNat
    4), (403, Int.ofNat 3), (411, Int.ofNat 2), (426, Int.negSucc 1), (439, Int.ofNat 2), (445,
    Int.ofNat 2), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(104, Int.ofNat 1), (372, Int.ofNat 8), (403,
    Int.negSucc 5), (411, Int.ofNat 8), (426, Int.negSucc 3), (449, Int.ofNat 2), (456, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(105, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (380,
    Int.negSucc 7), (421, Int.negSucc 7), (464, Int.negSucc 1), (475, Int.ofNat 4), (487,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (429, Int.negSucc 3), (490,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (380, Int.negSucc 3), (421,
    Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (385, Int.negSucc 3), (433,
    Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.negSucc 0), (436, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.negSucc 0), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.negSucc 0), (424, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (429, Int.negSucc 11), (468,
    Int.negSucc 1), (482, Int.ofNat 2), (490, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.negSucc 0), (417, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(117, Int.negSucc 0), (429, Int.negSucc 7), (468,
    Int.negSucc 0), (482, Int.ofNat 2), (490, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 0), (385, Int.negSucc 11), (433,
    Int.negSucc 9), (471, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.ofNat 4), (497, Int.ofNat
    6)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (433, Int.negSucc 7), (471, Int.negSucc 1), (486, Int.ofNat 4), (497,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (120,
    Int.ofNat 2), (380, Int.negSucc 3), (421, Int.negSucc 5), (464, Int.negSucc 0), (475,
    Int.ofNat 4), (487, Int.ofNat 4), (509, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (454, Int.ofNat 1), (478,
    Int.negSucc 1), (512, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(123, Int.ofNat 2), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.negSucc 0), (124, Int.ofNat 1), (380,
    Int.negSucc 1), (421, Int.negSucc 1), (475, Int.ofNat 2), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (125, Int.ofNat 1), (385,
    Int.negSucc 1), (433, Int.negSucc 1), (479, Int.ofNat 2), (497, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(126, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (128, Int.ofNat 1), (391,
    Int.ofNat 4), (429, Int.negSucc 11), (462, Int.ofNat 4), (468, Int.negSucc 1), (482, Int.ofNat
    3), (490, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(130, Int.ofNat 1), (404, Int.negSucc 3), (412,
    Int.ofNat 8), (454, Int.ofNat 1), (478, Int.negSucc 1), (485, Int.negSucc 3), (504, Int.ofNat
    1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (131,
    Int.ofNat 2), (385, Int.negSucc 15), (433, Int.negSucc 15), (471, Int.negSucc 2), (479,
    Int.ofNat 2), (486, Int.ofNat 8), (497, Int.ofNat 10), (508, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(132, Int.ofNat 4), (404, Int.negSucc 7), (412,
    Int.ofNat 16), (454, Int.ofNat 4), (478, Int.negSucc 3), (485, Int.negSucc 7), (493,
    Int.negSucc 3), (504, Int.ofNat 1), (512, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

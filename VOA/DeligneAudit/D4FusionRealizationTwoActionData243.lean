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
def actionData243 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(36, Int.ofNat 1), (345, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 1), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 4), (44, Int.ofNat 2), (316, Int.ofNat
    14), (327, Int.negSucc 0), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.ofNat 2), (386,
    Int.negSucc 5), (392, Int.negSucc 1), (408, Int.ofNat 2), (682, Int.negSucc 5), (697,
    Int.ofNat 6), (700, Int.ofNat 6), (703, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(52, Int.ofNat 1), (358, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 1), (327, Int.ofNat 1), (343, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 2), (323, Int.ofNat 8), (346, Int.negSucc
    7), (373, Int.negSucc 3), (377, Int.ofNat 4), (383, Int.ofNat 4), (388, Int.negSucc 3), (691,
    Int.negSucc 3), (704, Int.negSucc 3), (711, Int.ofNat 4), (714, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.ofNat 2), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 1), (323, Int.ofNat
    6), (346, Int.negSucc 1), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (388,
    Int.negSucc 3), (691, Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (346, Int.ofNat 2), (377, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(63, Int.ofNat 2), (335, Int.ofNat 4), (361, Int.negSucc
    1), (376, Int.negSucc 1), (387, Int.ofNat 2), (397, Int.ofNat 1), (402, Int.ofNat 1), (688,
    Int.ofNat 2), (701, Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 3), (342, Int.ofNat 12), (366,
    Int.negSucc 2), (405, Int.ofNat 3), (438, Int.negSucc 5), (685, Int.ofNat 6), (698, Int.ofNat
    6), (733, Int.ofNat 6), (736, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(63, Int.ofNat 2), (66, Int.ofNat 1), (335, Int.ofNat
    6), (361, Int.negSucc 0), (376, Int.negSucc 1), (387, Int.ofNat 4), (397, Int.ofNat 1), (402,
    Int.ofNat 1), (688, Int.ofNat 2), (701, Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat 2)]
    },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    6), (373, Int.negSucc 0), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3), (691,
    Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (335, Int.ofNat
    12), (376, Int.negSucc 3), (387, Int.ofNat 8), (397, Int.ofNat 1), (402, Int.ofNat 2), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 3), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1), (378, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 2), (68, Int.ofNat 2), (323, Int.ofNat
    14), (346, Int.negSucc 7), (373, Int.negSucc 4), (377, Int.ofNat 4), (383, Int.ofNat 6), (388,
    Int.negSucc 5), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 5), (704,
    Int.negSucc 5), (711, Int.ofNat 6), (714, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 8), (69, Int.ofNat 4), (335, Int.ofNat
    28), (361, Int.negSucc 7), (376, Int.negSucc 7), (387, Int.ofNat 12), (397, Int.ofNat 5),
    (402, Int.ofNat 6), (410, Int.negSucc 3), (444, Int.negSucc 3), (688, Int.ofNat 12), (701,
    Int.ofNat 12), (722, Int.ofNat 12), (725, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.ofNat 1), (361, Int.ofNat 2), (376, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(78, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (352, Int.ofNat 8), (379, Int.negSucc
    11), (389, Int.ofNat 4), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 4), (744,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.negSucc 1), (432, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 3), (357, Int.ofNat 24), (384,
    Int.negSucc 23), (416, Int.negSucc 11), (427, Int.ofNat 12), (435, Int.ofNat 12), (440,
    Int.negSucc 11), (751, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    12), (379, Int.negSucc 11), (389, Int.ofNat 8), (413, Int.negSucc 3), (423, Int.ofNat 4),
    (428, Int.ofNat 4), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (85, Int.ofNat 1), (352, Int.ofNat
    6), (379, Int.negSucc 3), (389, Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 1), (428,
    Int.ofNat 2), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 3), (347, Int.ofNat 4), (420, Int.negSucc
    5), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (347, Int.ofNat 2), (420, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 2), (419, Int.ofNat 2), (453, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.ofNat 3), (372, Int.ofNat 12), (403,
    Int.negSucc 5), (426, Int.negSucc 5), (439, Int.ofNat 6), (449, Int.ofNat 3), (456, Int.ofNat
    3), (758, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 3), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (95, Int.ofNat 1), (352, Int.ofNat
    6), (379, Int.negSucc 3), (389, Int.ofNat 4), (413, Int.negSucc 0), (423, Int.ofNat 2), (428,
    Int.ofNat 2), (744, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 6), (362, Int.ofNat 2), (419, Int.ofNat
    6), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.ofNat 3), (91, Int.ofNat 2), (347, Int.ofNat
    6), (420, Int.negSucc 5), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 6), (92, Int.ofNat 2), (362, Int.ofNat
    3), (419, Int.ofNat 6), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 4), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (352, Int.ofNat 28), (379, Int.negSucc 27), (389, Int.ofNat 12), (413,
    Int.negSucc 9), (423, Int.ofNat 10), (428, Int.ofNat 16), (446, Int.negSucc 3), (461,
    Int.negSucc 3), (744, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 4), (362, Int.ofNat 2), (419, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 4), (380, Int.negSucc 15), (390,
    Int.ofNat 16), (421, Int.negSucc 7), (464, Int.negSucc 7), (475, Int.ofNat 16), (765,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (107, Int.ofNat 1), (380,
    Int.negSucc 13), (390, Int.ofNat 14), (421, Int.negSucc 5), (464, Int.negSucc 5), (475,
    Int.ofNat 12), (487, Int.ofNat 2), (765, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 3), (391, Int.ofNat 24), (429,
    Int.negSucc 35), (441, Int.ofNat 12), (468, Int.negSucc 11), (482, Int.ofNat 12), (490,
    Int.ofNat 12), (695, Int.ofNat 12), (745, Int.negSucc 11), (752, Int.negSucc 11), (759,
    Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (421, Int.ofNat 2), (475,
    Int.negSucc 1), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (385,
    Int.negSucc 7), (396, Int.ofNat 4), (433, Int.negSucc 11), (471, Int.negSucc 3), (479,
    Int.negSucc 3), (486, Int.ofNat 4), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 1), (107, Int.ofNat 6), (380,
    Int.negSucc 11), (390, Int.ofNat 20), (421, Int.ofNat 4), (464, Int.negSucc 3), (475,
    Int.ofNat 8), (487, Int.ofNat 4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 3), (110,
    Int.ofNat 1), (380, Int.negSucc 3), (390, Int.ofNat 10), (421, Int.ofNat 4), (464, Int.negSucc
    1), (475, Int.ofNat 2), (487, Int.ofNat 2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (380, Int.ofNat 2), (421, Int.ofNat
    2), (475, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(120, Int.ofNat 2), (421, Int.ofNat 2), (464, Int.ofNat
    1), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 6), (130, Int.negSucc 0), (404,
    Int.negSucc 3), (412, Int.ofNat 4), (454, Int.negSucc 5), (478, Int.ofNat 4), (485,
    Int.negSucc 3), (504, Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(124, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (125, Int.ofNat 2), (131,
    Int.negSucc 1), (385, Int.negSucc 1), (433, Int.negSucc 1), (471, Int.negSucc 0), (508,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(126, Int.ofNat 4), (130, Int.ofNat 2), (132,
    Int.negSucc 3), (404, Int.negSucc 1), (454, Int.negSucc 1), (493, Int.negSucc 3), (504,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 3), (120,
    Int.ofNat 2), (380, Int.negSucc 3), (390, Int.ofNat 10), (421, Int.ofNat 4), (464, Int.negSucc
    0), (475, Int.ofNat 4), (487, Int.ofNat 2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(110, Int.ofNat 3), (124, Int.ofNat 2), (380, Int.ofNat
    6), (421, Int.ofNat 6), (475, Int.negSucc 5), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 2), (110, Int.ofNat 1), (120, Int.ofNat
    2), (380, Int.negSucc 13), (390, Int.ofNat 16), (421, Int.negSucc 5), (464, Int.negSucc 4),
    (475, Int.ofNat 10), (487, Int.ofNat 8), (494, Int.negSucc 1), (509, Int.negSucc 0), (765,
    Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(120, Int.ofNat 4), (380, Int.ofNat 4), (421, Int.ofNat
    4), (464, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 2), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 6), (430, Int.negSucc 47), (442,
    Int.ofNat 48), (480, Int.negSucc 23), (516, Int.negSucc 23), (528, Int.ofNat 48), (766,
    Int.negSucc 23), (787, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 1), (415, Int.negSucc 0), (540,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (425, Int.negSucc 0), (544,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 5), (422, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 3), (139, Int.ofNat 6), (148,
    Int.negSucc 0), (430, Int.negSucc 87), (442, Int.ofNat 72), (443, Int.ofNat 8), (480,
    Int.negSucc 39), (488, Int.negSucc 23), (516, Int.negSucc 31), (520, Int.negSucc 7), (528,
    Int.ofNat 64), (535, Int.ofNat 8), (547, Int.ofNat 16), (696, Int.ofNat 8), (709, Int.ofNat
    8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 39),
    (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat 32)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 2), (149, Int.negSucc 1), (418,
    Int.negSucc 3), (472, Int.negSucc 3), (539, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 3), (422, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.ofNat 4), (148, Int.ofNat 3), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 15), (448, Int.ofNat 8), (480, Int.ofNat
    8), (488, Int.negSucc 7), (495, Int.negSucc 15), (524, Int.negSucc 7), (528, Int.negSucc 7),
    (535, Int.ofNat 4), (550, Int.ofNat 16), (774, Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (415, Int.ofNat 2), (465, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 2), (425, Int.ofNat 2), (476, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 1), (415, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 5), (425, Int.ofNat 3), (476, Int.ofNat
    8), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 3), (422, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 3), (153, Int.ofNat 8), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 15), (463, Int.ofNat 8), (480, Int.ofNat
    8), (488, Int.negSucc 7), (510, Int.negSucc 7), (516, Int.ofNat 4), (520, Int.negSucc 3),
    (556, Int.ofNat 4), (560, Int.ofNat 8), (781, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 2), (161, Int.negSucc 0), (451,
    Int.negSucc 0), (505, Int.negSucc 0), (543, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(455, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.ofNat 2), (148, Int.negSucc 1), (150,
    Int.ofNat 4), (157, Int.ofNat 4), (162, Int.negSucc 3), (430, Int.negSucc 3), (495,
    Int.negSucc 3), (510, Int.negSucc 1), (524, Int.negSucc 1), (556, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 5), (415, Int.ofNat 3), (465, Int.ofNat
    4), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 3), (152, Int.ofNat 2), (425, Int.ofNat
    2), (476, Int.ofNat 4), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(165, Int.ofNat 2), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.ofNat 2), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 2), (172, Int.ofNat 3), (481,
    Int.negSucc 23), (489, Int.negSucc 15), (500, Int.ofNat 28), (564, Int.negSucc 7), (578,
    Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 16), (767, Int.negSucc 7), (775,
    Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 12), (492, Int.negSucc 95), (501,
    Int.ofNat 96), (567, Int.negSucc 47), (581, Int.ofNat 96), (788, Int.negSucc 95)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 3), (466, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

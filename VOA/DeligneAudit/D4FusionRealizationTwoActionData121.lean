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
def actionData121 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(314, Int.ofNat 1), (330, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(18, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 2), (312, Int.ofNat 4), (329, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(314, Int.ofNat 1), (318, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(22, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 2), (320, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(24, Int.ofNat 2), (326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(24, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (315, Int.ofNat 2), (319, Int.ofNat
    2), (332, Int.negSucc 1), (348, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(27, Int.ofNat 2), (325, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(24, Int.ofNat 1), (326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (308, Int.ofNat 2), (315, Int.ofNat
    2), (319, Int.ofNat 2), (332, Int.negSucc 1), (348, Int.negSucc 1), (353, Int.negSucc 1),
    (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(321, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(333, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(32, Int.ofNat 2), (331, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 1), (324, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1), (345, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(37, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 2), (322, Int.ofNat 4), (350, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1), (344, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(41, Int.ofNat 2), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 2), (316, Int.ofNat 2), (365, Int.ofNat
    1), (386, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (334, Int.ofNat 4), (349, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(36, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (316, Int.ofNat
    4), (327, Int.ofNat 2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.ofNat 1), (386,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (359, Int.negSucc
    0)] },
  { denominator := Int.ofNat 2, terms := [(36, Int.ofNat 1), (345, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 1), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 4), (44, Int.ofNat 2), (316, Int.ofNat
    8), (327, Int.ofNat 2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.ofNat 2), (386,
    Int.negSucc 5), (392, Int.negSucc 1), (408, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(52, Int.ofNat 1), (358, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 1), (327, Int.ofNat 1), (343, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1), (378, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 2), (323, Int.ofNat 4), (346, Int.negSucc
    3), (373, Int.negSucc 1), (377, Int.ofNat 4), (383, Int.ofNat 4), (388, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(58, Int.ofNat 2), (351, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 1), (323, Int.ofNat
    4), (373, Int.negSucc 0), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (346, Int.ofNat 2), (377, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (335, Int.ofNat 4), (361, Int.negSucc
    1), (376, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 1), (402, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 6), (342, Int.ofNat 12), (405, Int.ofNat
    3), (438, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (66, Int.ofNat 2), (335, Int.ofNat
    8), (376, Int.negSucc 3), (387, Int.ofNat 8), (397, Int.ofNat 1), (402, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    4), (346, Int.ofNat 2), (377, Int.ofNat 2), (383, Int.ofNat 2), (388, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 2), (69, Int.ofNat 2), (335, Int.ofNat
    4), (361, Int.ofNat 1), (376, Int.negSucc 1), (387, Int.ofNat 4), (402, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 3), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1), (378, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (68, Int.ofNat 1), (323, Int.ofNat
    4), (346, Int.negSucc 0), (373, Int.negSucc 0), (377, Int.ofNat 2), (383, Int.ofNat 3), (388,
    Int.negSucc 2), (394, Int.negSucc 0), (459, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.ofNat 4), (69, Int.ofNat 2), (335, Int.ofNat
    8), (361, Int.negSucc 0), (376, Int.negSucc 3), (387, Int.ofNat 6), (397, Int.ofNat 1), (402,
    Int.ofNat 3), (410, Int.negSucc 1), (444, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.ofNat 1), (361, Int.ofNat 2), (376, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(78, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(78, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (352, Int.ofNat 4), (379, Int.negSucc
    7), (389, Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.negSucc 1), (432, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 3), (357, Int.ofNat 12), (384,
    Int.negSucc 11), (416, Int.negSucc 5), (427, Int.ofNat 12), (435, Int.ofNat 6), (440,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    8), (379, Int.negSucc 7), (389, Int.ofNat 8), (413, Int.negSucc 1), (423, Int.ofNat 2), (428,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 1), (374, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (85, Int.ofNat 1), (352, Int.ofNat
    4), (379, Int.negSucc 1), (389, Int.ofNat 4), (413, Int.negSucc 0), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 3), (347, Int.ofNat 4), (420, Int.negSucc
    5), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (347, Int.ofNat 2), (420, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 2), (419, Int.ofNat 2), (453, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 6), (372, Int.ofNat 12), (403,
    Int.negSucc 5), (426, Int.negSucc 11), (439, Int.ofNat 12), (449, Int.ofNat 3), (456,
    Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 3), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 1), (95, Int.ofNat 1), (352, Int.ofNat
    4), (379, Int.negSucc 1), (389, Int.ofNat 4), (423, Int.ofNat 1), (428, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 6), (362, Int.ofNat 2), (419, Int.ofNat
    6), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.ofNat 3), (91, Int.ofNat 2), (347, Int.ofNat
    6), (420, Int.negSucc 5), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.ofNat 6), (92, Int.ofNat 2), (362, Int.ofNat
    3), (419, Int.ofNat 6), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 4), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (352, Int.ofNat 16), (379, Int.negSucc 15), (389, Int.ofNat 12), (413,
    Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 16), (446, Int.negSucc 3), (461,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 4), (362, Int.ofNat 2), (419, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 4), (380, Int.negSucc 7), (390,
    Int.ofNat 8), (464, Int.negSucc 3), (475, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 2), (107, Int.ofNat 1), (380,
    Int.negSucc 7), (390, Int.ofNat 8), (464, Int.negSucc 2), (475, Int.ofNat 6), (487, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 3), (391, Int.ofNat 12), (429,
    Int.negSucc 23), (441, Int.ofNat 12), (468, Int.negSucc 5), (482, Int.ofNat 6), (490,
    Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (421, Int.ofNat 2), (475,
    Int.negSucc 1), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (385,
    Int.negSucc 3), (433, Int.negSucc 7), (471, Int.negSucc 1), (479, Int.negSucc 3), (486,
    Int.ofNat 4), (497, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 1), (107, Int.ofNat 6), (380,
    Int.negSucc 7), (390, Int.ofNat 16), (421, Int.ofNat 8), (464, Int.negSucc 1), (475, Int.ofNat
    4), (487, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 3), (110,
    Int.ofNat 1), (380, Int.negSucc 1), (390, Int.ofNat 8), (421, Int.ofNat 6), (464, Int.negSucc
    0), (487, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (380, Int.ofNat 2), (421, Int.ofNat
    2), (475, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(120, Int.ofNat 2), (421, Int.ofNat 2), (464, Int.ofNat
    1), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 6), (130, Int.negSucc 0), (404,
    Int.negSucc 1), (454, Int.negSucc 3), (478, Int.ofNat 4), (485, Int.negSucc 3), (504,
    Int.ofNat 1), (512, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(124, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (125, Int.ofNat 2), (131,
    Int.negSucc 1), (385, Int.negSucc 1), (433, Int.negSucc 1), (471, Int.negSucc 0), (508,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(126, Int.ofNat 4), (130, Int.ofNat 2), (132,
    Int.negSucc 3), (404, Int.negSucc 1), (454, Int.negSucc 1), (493, Int.negSucc 3), (504,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 3), (120,
    Int.ofNat 2), (380, Int.negSucc 1), (390, Int.ofNat 8), (421, Int.ofNat 6), (475, Int.ofNat
    2), (487, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(110, Int.ofNat 3), (124, Int.ofNat 2), (380, Int.ofNat
    6), (421, Int.ofNat 6), (475, Int.negSucc 5), (494, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 2), (110, Int.ofNat 1), (120, Int.ofNat
    2), (380, Int.negSucc 7), (390, Int.ofNat 10), (464, Int.negSucc 1), (475, Int.ofNat 4), (487,
    Int.ofNat 8), (494, Int.negSucc 1), (509, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(120, Int.ofNat 4), (380, Int.ofNat 4), (421, Int.ofNat
    4), (464, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 2), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 6), (430, Int.negSucc 23), (442,
    Int.ofNat 24), (516, Int.negSucc 11), (528, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 1), (415, Int.negSucc 0), (540,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (425, Int.negSucc 0), (544,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 5), (422, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 4), (139, Int.ofNat 6), (148,
    Int.negSucc 0), (430, Int.negSucc 47), (442, Int.ofNat 40), (488, Int.negSucc 15), (516,
    Int.negSucc 15), (520, Int.negSucc 3), (528, Int.ofNat 32), (535, Int.ofNat 4), (547,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 2), (149, Int.negSucc 1), (418,
    Int.negSucc 3), (472, Int.negSucc 3), (539, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 3), (422, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.ofNat 4), (148, Int.ofNat 3), (150,
    Int.negSucc 5), (151, Int.ofNat 2), (430, Int.negSucc 7), (480, Int.ofNat 8), (488,
    Int.negSucc 7), (495, Int.negSucc 7), (524, Int.negSucc 3), (528, Int.negSucc 7), (535,
    Int.ofNat 4), (550, Int.ofNat 8)] },
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
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 7), (480, Int.ofNat 8), (488,
    Int.negSucc 7), (510, Int.negSucc 3), (516, Int.ofNat 4), (520, Int.negSucc 3), (556,
    Int.ofNat 2), (560, Int.ofNat 4)] },
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
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 4), (489, Int.negSucc 7), (500,
    Int.ofNat 8), (564, Int.negSucc 3), (578, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 8), (492, Int.negSucc 47), (501,
    Int.ofNat 48), (567, Int.negSucc 23), (581, Int.ofNat 48)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 3), (466, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (180, Int.negSucc 2), (192,
    Int.ofNat 1), (470, Int.negSucc 5), (521, Int.negSucc 3), (541, Int.negSucc 3), (585,
    Int.ofNat 2), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 3), (477, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 1), (181, Int.negSucc 2), (183,
    Int.ofNat 1), (484, Int.negSucc 5), (536, Int.negSucc 3), (545, Int.negSucc 3), (573,
    Int.negSucc 1), (593, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.ofNat 11), (172, Int.ofNat 3), (481,
    Int.negSucc 15), (489, Int.negSucc 47), (500, Int.ofNat 52), (564, Int.negSucc 19), (578,
    Int.ofNat 40), (596, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(174, Int.ofNat 2), (182, Int.negSucc 1), (470,
    Int.negSucc 3), (525, Int.negSucc 1), (541, Int.negSucc 3), (585, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(473, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 3), (477, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 3), (172, Int.ofNat 3), (481,
    Int.negSucc 15), (489, Int.negSucc 31), (496, Int.negSucc 7), (500, Int.ofNat 36), (564,
    Int.negSucc 11), (578, Int.ofNat 24), (596, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(166, Int.ofNat 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

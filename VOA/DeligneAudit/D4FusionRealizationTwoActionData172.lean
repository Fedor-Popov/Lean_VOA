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
def actionData172 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.ofNat 1), (346, Int.ofNat 2), (377, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1), (382, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 1), (69, Int.ofNat 4), (73, Int.ofNat
    2), (335, Int.ofNat 2), (361, Int.ofNat 4), (397, Int.negSucc 0), (402, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(71, Int.ofNat 2), (74, Int.ofNat 2), (342, Int.ofNat
    2), (366, Int.ofNat 4), (401, Int.negSucc 0), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(58, Int.ofNat 1), (351, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 3), (66, Int.ofNat 2), (69, Int.negSucc
    3), (73, Int.ofNat 4), (335, Int.negSucc 7), (361, Int.ofNat 2), (376, Int.ofNat 4), (387,
    Int.negSucc 3), (397, Int.negSucc 0), (402, Int.negSucc 1), (410, Int.ofNat 4), (444,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(67, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (68, Int.ofNat 2), (72, Int.ofNat
    1), (323, Int.ofNat 1), (346, Int.ofNat 4), (373, Int.ofNat 1), (383, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(73, Int.ofNat 4), (75, Int.ofNat 1), (335, Int.ofNat
    4), (361, Int.ofNat 6), (376, Int.ofNat 4), (402, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(74, Int.ofNat 2), (77, Int.ofNat 1), (342, Int.ofNat
    2), (366, Int.ofNat 4), (381, Int.ofNat 2), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(76, Int.ofNat 1), (400, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (74, Int.ofNat 2), (342,
    Int.negSucc 3), (366, Int.ofNat 2), (381, Int.ofNat 2), (393, Int.negSucc 1), (401,
    Int.negSucc 0), (405, Int.negSucc 0), (409, Int.ofNat 2), (438, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (379, Int.ofNat 4), (428, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 4), (347, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 2), (384, Int.ofNat 8), (435, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 4), (362, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.ofNat 4), (403, Int.ofNat 4), (456, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 8), (367, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(94, Int.ofNat 4), (406, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 0), (82, Int.ofNat 1), (85, Int.negSucc
    0), (95, Int.negSucc 0), (101, Int.ofNat 2), (352, Int.negSucc 3), (379, Int.ofNat 4), (389,
    Int.negSucc 1), (413, Int.ofNat 1), (423, Int.negSucc 0), (428, Int.negSucc 3), (446,
    Int.ofNat 2), (461, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(83, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 2), (374, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(101, Int.ofNat 2), (352, Int.ofNat 2), (379, Int.ofNat
    4), (428, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(102, Int.ofNat 2), (357, Int.ofNat 2), (384, Int.ofNat
    6), (435, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(96, Int.ofNat 2), (398, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(103, Int.ofNat 2), (372, Int.ofNat 2), (403, Int.ofNat
    3), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.negSucc 1), (82, Int.ofNat 1), (95, Int.negSucc
    1), (101, Int.ofNat 4), (352, Int.negSucc 7), (379, Int.ofNat 12), (389, Int.negSucc 3), (413,
    Int.ofNat 2), (423, Int.negSucc 3), (428, Int.negSucc 7), (446, Int.ofNat 4), (461, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.ofNat 1), (98, Int.negSucc
    1), (102, Int.ofNat 2), (357, Int.negSucc 3), (384, Int.ofNat 6), (395, Int.negSucc 1), (416,
    Int.ofNat 1), (427, Int.negSucc 3), (435, Int.negSucc 1), (440, Int.ofNat 2), (460, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.ofNat 1), (384, Int.ofNat 2), (427, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(97, Int.negSucc 1), (99, Int.ofNat 4), (103, Int.ofNat
    2), (372, Int.ofNat 2), (403, Int.ofNat 5), (449, Int.negSucc 0), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.ofNat 1), (85, Int.negSucc
    1), (101, Int.ofNat 4), (352, Int.negSucc 7), (379, Int.ofNat 12), (389, Int.negSucc 3), (413,
    Int.ofNat 4), (423, Int.negSucc 1), (428, Int.negSucc 7), (446, Int.ofNat 4), (461, Int.ofNat
    4)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 3), (97, Int.ofNat 2), (99, Int.negSucc
    3), (103, Int.ofNat 4), (372, Int.negSucc 7), (403, Int.ofNat 6), (411, Int.negSucc 3), (426,
    Int.ofNat 8), (439, Int.negSucc 3), (445, Int.negSucc 3), (449, Int.negSucc 0), (456,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (98, Int.ofNat 2), (102, Int.ofNat
    1), (357, Int.ofNat 1), (384, Int.ofNat 5), (416, Int.ofNat 1), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(103, Int.ofNat 4), (104, Int.ofNat 1), (372, Int.ofNat
    4), (403, Int.ofNat 8), (426, Int.ofNat 4), (456, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 1), (107, Int.ofNat 4), (110,
    Int.negSucc 1), (120, Int.negSucc 3), (124, Int.ofNat 4), (380, Int.ofNat 8), (390,
    Int.negSucc 3), (421, Int.ofNat 8), (464, Int.ofNat 2), (475, Int.negSucc 3), (487,
    Int.negSucc 7), (494, Int.ofNat 4), (509, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (429, Int.ofNat 8), (490,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 4), (375, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(124, Int.ofNat 4), (380, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(125, Int.ofNat 4), (385, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 2), (436, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(121, Int.ofNat 8), (399, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(126, Int.ofNat 4), (404, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(123, Int.ofNat 4), (457, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 8), (407, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1), (414, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (117,
    Int.negSucc 0), (128, Int.negSucc 0), (133, Int.ofNat 2), (391, Int.negSucc 3), (429,
    Int.ofNat 8), (441, Int.negSucc 1), (447, Int.negSucc 1), (462, Int.negSucc 1), (468,
    Int.ofNat 1), (482, Int.negSucc 0), (490, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 2), (417, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(133, Int.ofNat 2), (391, Int.ofNat 2), (429, Int.ofNat
    6), (490, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (128,
    Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 7), (429, Int.ofNat 20), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.ofNat 2), (482,
    Int.negSucc 3), (490, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 3), (118, Int.ofNat 4), (125,
    Int.ofNat 6), (131, Int.negSucc 3), (385, Int.ofNat 10), (396, Int.negSucc 3), (433, Int.ofNat
    8), (471, Int.ofNat 2), (479, Int.ofNat 4), (486, Int.negSucc 7), (497, Int.negSucc 3), (508,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (117,
    Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 7), (429, Int.ofNat 20), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.ofNat 4), (482,
    Int.negSucc 1), (490, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 7), (126, Int.ofNat 6), (130,
    Int.ofNat 4), (132, Int.negSucc 3), (404, Int.ofNat 5), (412, Int.negSucc 3), (454, Int.ofNat
    4), (478, Int.negSucc 3), (485, Int.ofNat 8), (493, Int.negSucc 3), (504, Int.negSucc 0),
    (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 2), (415, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 4), (425, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (143,
    Int.negSucc 1), (153, Int.negSucc 3), (157, Int.ofNat 4), (430, Int.ofNat 8), (442,
    Int.negSucc 3), (480, Int.ofNat 8), (488, Int.ofNat 8), (495, Int.negSucc 3), (510,
    Int.negSucc 1), (516, Int.ofNat 2), (528, Int.negSucc 3), (547, Int.negSucc 7), (550,
    Int.ofNat 4), (560, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 4), (418, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(157, Int.ofNat 4), (430, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 4), (437, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 8), (451, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(159, Int.ofNat 4), (458, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 7), (139, Int.negSucc 11), (143,
    Int.negSucc 1), (148, Int.ofNat 6), (150, Int.negSucc 3), (153, Int.negSucc 3), (157,
    Int.ofNat 4), (160, Int.negSucc 3), (163, Int.ofNat 8), (430, Int.ofNat 32), (442, Int.negSucc
    11), (443, Int.ofNat 8), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 8), (488,
    Int.ofNat 32), (495, Int.negSucc 11), (510, Int.negSucc 5), (516, Int.ofNat 2), (520,
    Int.ofNat 4), (528, Int.negSucc 3), (535, Int.negSucc 3), (547, Int.negSucc 15), (550,
    Int.ofNat 4), (560, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 7), (139, Int.negSucc 11), (143,
    Int.negSucc 1), (148, Int.ofNat 1), (150, Int.ofNat 6), (151, Int.negSucc 1), (153,
    Int.negSucc 3), (157, Int.ofNat 8), (160, Int.negSucc 3), (162, Int.negSucc 3), (163,
    Int.ofNat 8), (430, Int.ofNat 40), (442, Int.negSucc 11), (443, Int.ofNat 8), (448,
    Int.negSucc 11), (463, Int.negSucc 7), (480, Int.ofNat 4), (488, Int.ofNat 40), (495,
    Int.negSucc 11), (510, Int.negSucc 7), (516, Int.ofNat 2), (520, Int.ofNat 4), (524, Int.ofNat
    2), (535, Int.negSucc 7), (547, Int.negSucc 15), (556, Int.ofNat 1), (560, Int.ofNat 2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

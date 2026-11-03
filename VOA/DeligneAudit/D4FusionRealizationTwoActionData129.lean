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
def actionData129 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(356, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(371, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(76, Int.ofNat 2), (400, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.ofNat 2), (379, Int.ofNat 4), (428, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.negSucc
    3), (379, Int.ofNat 12), (389, Int.negSucc 3), (413, Int.ofNat 2), (423, Int.negSucc 1), (428,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(83, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(374, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 3), (379, Int.ofNat 2), (389,
    Int.negSucc 1), (413, Int.ofNat 1), (423, Int.negSucc 0), (428, Int.negSucc 1), (446,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 3), (384, Int.ofNat 2), (395,
    Int.negSucc 1), (416, Int.ofNat 1), (427, Int.negSucc 1), (435, Int.negSucc 0), (440,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(83, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(83, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357,
    Int.negSucc 7), (384, Int.ofNat 10), (395, Int.negSucc 5), (416, Int.ofNat 3), (427,
    Int.negSucc 5), (435, Int.negSucc 2), (440, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (87, Int.ofNat
    2), (357, Int.negSucc 3), (384, Int.ofNat 12), (395, Int.negSucc 3), (416, Int.ofNat 2), (427,
    Int.negSucc 7), (435, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(352, Int.negSucc 3), (379, Int.ofNat 2), (389,
    Int.negSucc 1), (413, Int.ofNat 1), (423, Int.negSucc 0), (428, Int.negSucc 1), (461,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(398, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(372, Int.negSucc 7), (403, Int.ofNat 2), (411,
    Int.negSucc 3), (426, Int.ofNat 4), (439, Int.negSucc 3), (449, Int.negSucc 0), (456,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.ofNat 1), (85, Int.negSucc
    1), (95, Int.negSucc 1), (101, Int.ofNat 4), (352, Int.negSucc 7), (379, Int.negSucc 3), (389,
    Int.negSucc 3), (428, Int.negSucc 3), (446, Int.ofNat 4), (461, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (98, Int.negSucc 1), (102,
    Int.ofNat 2), (357, Int.negSucc 3), (384, Int.negSucc 1), (395, Int.negSucc 1), (427,
    Int.negSucc 1), (440, Int.ofNat 2), (460, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (99, Int.negSucc 1), (103,
    Int.ofNat 2), (372, Int.negSucc 3), (403, Int.negSucc 0), (411, Int.negSucc 1), (426,
    Int.ofNat 2), (439, Int.negSucc 1), (445, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(406, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(83, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 3), (97, Int.ofNat 4), (372,
    Int.negSucc 15), (403, Int.ofNat 10), (411, Int.negSucc 11), (426, Int.ofNat 12), (439,
    Int.negSucc 3), (449, Int.negSucc 2), (456, Int.negSucc 2)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357,
    Int.negSucc 11), (384, Int.ofNat 12), (395, Int.negSucc 7), (416, Int.ofNat 4), (427,
    Int.negSucc 7), (435, Int.negSucc 3), (440, Int.ofNat 2), (460, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 0), (97, Int.ofNat 1), (372,
    Int.negSucc 5), (403, Int.ofNat 3), (411, Int.negSucc 3), (426, Int.ofNat 4), (439,
    Int.negSucc 0), (445, Int.negSucc 0), (449, Int.negSucc 0), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(83, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 1), (97, Int.ofNat 2), (104, Int.ofNat
    1), (372, Int.negSucc 3), (403, Int.ofNat 6), (411, Int.negSucc 3), (426, Int.ofNat 8), (449,
    Int.negSucc 0), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (380,
    Int.ofNat 8), (390, Int.negSucc 3), (421, Int.ofNat 4), (464, Int.ofNat 2), (475, Int.negSucc
    3), (487, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (429, Int.ofNat 8), (490,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(114, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 2), (115, Int.ofNat 1), (391,
    Int.negSucc 3), (429, Int.ofNat 20), (441, Int.negSucc 3), (468, Int.ofNat 2), (482,
    Int.negSucc 1), (490, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(414, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.negSucc 3), (429, Int.ofNat 4), (441,
    Int.negSucc 1), (447, Int.negSucc 1), (468, Int.ofNat 1), (482, Int.negSucc 0), (490,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (385,
    Int.ofNat 8), (396, Int.negSucc 3), (433, Int.ofNat 4), (471, Int.ofNat 2), (486, Int.negSucc
    3), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(112, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 3), (115, Int.ofNat 5), (391,
    Int.negSucc 3), (429, Int.ofNat 28), (441, Int.negSucc 3), (468, Int.ofNat 6), (482,
    Int.negSucc 5), (490, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 4), (115, Int.ofNat 5), (117,
    Int.ofNat 2), (391, Int.negSucc 7), (429, Int.ofNat 40), (441, Int.negSucc 3), (447,
    Int.negSucc 3), (468, Int.ofNat 8), (482, Int.negSucc 9), (490, Int.negSucc 9)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (115, Int.negSucc 1), (117,
    Int.ofNat 6), (391, Int.negSucc 3), (429, Int.ofNat 20), (447, Int.negSucc 3), (468, Int.ofNat
    2), (482, Int.negSucc 7), (490, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(424, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(391, Int.negSucc 3), (429, Int.ofNat 4), (441,
    Int.negSucc 1), (462, Int.negSucc 1), (468, Int.ofNat 1), (482, Int.negSucc 0), (490,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(450, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (404,
    Int.ofNat 4), (412, Int.negSucc 3), (454, Int.ofNat 2), (485, Int.ofNat 4), (504, Int.negSucc
    0), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 3, terms := [(123, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (117,
    Int.negSucc 1), (128, Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 7), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(436, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(457, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 4), (115, Int.ofNat 5), (128,
    Int.ofNat 2), (391, Int.negSucc 7), (429, Int.ofNat 40), (441, Int.negSucc 3), (462,
    Int.negSucc 3), (468, Int.ofNat 10), (482, Int.negSucc 7), (490, Int.negSucc 9)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.negSucc 11), (429, Int.ofNat 20), (441, Int.negSucc 1), (447, Int.negSucc 7), (462,
    Int.negSucc 1), (468, Int.ofNat 4), (482, Int.negSucc 5), (490, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 4), (115, Int.ofNat 5), (133,
    Int.ofNat 4), (391, Int.negSucc 7), (429, Int.ofNat 40), (441, Int.negSucc 7), (468, Int.ofNat
    8), (482, Int.negSucc 7), (490, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(108, Int.negSucc 0), (115, Int.negSucc 1), (128,
    Int.ofNat 6), (391, Int.negSucc 3), (429, Int.ofNat 20), (462, Int.negSucc 3), (468, Int.ofNat
    8), (482, Int.negSucc 1), (490, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (415, Int.ofNat 4), (465, Int.ofNat
    2), (540, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 2), (425, Int.ofNat 4), (476, Int.ofNat
    4), (544, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 0), (139, Int.ofNat 2), (430,
    Int.ofNat 8), (442, Int.negSucc 3), (480, Int.ofNat 4), (488, Int.ofNat 4), (516, Int.ofNat
    2), (528, Int.negSucc 3), (547, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 0), (139, Int.ofNat 4), (148,
    Int.ofNat 2), (430, Int.ofNat 48), (442, Int.negSucc 15), (480, Int.ofNat 24), (488, Int.ofNat
    32), (516, Int.ofNat 8), (520, Int.ofNat 4), (528, Int.negSucc 15), (535, Int.negSucc 3),
    (547, Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 10)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 2), (472, Int.ofNat
    1), (539, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (148, Int.negSucc 0), (150,
    Int.ofNat 6), (151, Int.negSucc 1), (430, Int.ofNat 48), (442, Int.negSucc 7), (448,
    Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 32), (516, Int.ofNat 4), (520, Int.ofNat
    4), (524, Int.ofNat 4), (528, Int.negSucc 7), (535, Int.negSucc 7), (547, Int.negSucc 15),
    (550, Int.negSucc 7)] },
  { denominator := Int.ofNat 3, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (532,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.ofNat 2), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 2), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 11), (483, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(483, Int.negSucc 0)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 1), (148, Int.negSucc 0), (160,
    Int.ofNat 6), (164, Int.negSucc 0), (430, Int.ofNat 48), (442, Int.negSucc 7), (463,
    Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 32), (516, Int.ofNat 4), (520, Int.ofNat
    8), (528, Int.negSucc 7), (535, Int.negSucc 3), (547, Int.negSucc 15), (556, Int.negSucc 1),
    (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 6, terms := [(140, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(161, Int.ofNat 2), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 2), (458, Int.ofNat 1), (531, Int.ofNat
    2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 7), (139, Int.negSucc 13), (148,
    Int.ofNat 9), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 8), (430, Int.ofNat 32), (442, Int.negSucc
    7), (443, Int.ofNat 8), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 8), (495,
    Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 4), (524, Int.ofNat 4), (528, Int.negSucc
    7), (550, Int.negSucc 7), (556, Int.negSucc 1), (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 11), (469, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.ofNat 3), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (470, Int.ofNat 4), (517, Int.ofNat
    2), (541, Int.ofNat 4), (590, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (484, Int.ofNat 4), (529, Int.ofNat
    4), (545, Int.ofNat 4), (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 3), (172, Int.negSucc 0), (481,
    Int.ofNat 24), (489, Int.ofNat 16), (500, Int.negSucc 19), (564, Int.ofNat 4), (578,
    Int.negSucc 7), (596, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.negSucc 4), (173, Int.ofNat 6), (492,
    Int.ofNat 24), (501, Int.negSucc 11), (533, Int.negSucc 11), (548, Int.ofNat 24), (567,
    Int.ofNat 6), (581, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] }
]

end VOA.DeligneAudit.D4Two.Certificate

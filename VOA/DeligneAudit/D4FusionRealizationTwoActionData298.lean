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
def actionData298 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(46, Int.ofNat 2), (48, Int.ofNat 2), (316, Int.ofNat
    2), (327, Int.ofNat 3), (359, Int.negSucc 0), (365, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (341, Int.ofNat 4), (369, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.ofNat 4), (364, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(50, Int.ofNat 4), (322, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(51, Int.ofNat 4), (334, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (322, Int.ofNat 2), (350, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 1), (51, Int.ofNat 8), (334, Int.ofNat
    10), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(43, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(48, Int.ofNat 2), (54, Int.ofNat 1), (316, Int.ofNat
    2), (327, Int.ofNat 3), (343, Int.ofNat 2), (365, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (341, Int.ofNat 2), (354, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(52, Int.ofNat 1), (358, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(53, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 1), (363, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (48, Int.ofNat 2), (316,
    Int.negSucc 5), (327, Int.ofNat 1), (386, Int.ofNat 2), (392, Int.ofNat 2), (408, Int.negSucc
    1), (682, Int.ofNat 2), (697, Int.negSucc 1), (700, Int.negSucc 1), (703, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 1), (50, Int.ofNat 8), (322, Int.ofNat
    10), (355, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (51, Int.ofNat 4), (334, Int.ofNat
    8), (349, Int.ofNat 2), (370, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(56, Int.ofNat 2), (378, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 2), (346, Int.ofNat 4), (383, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(63, Int.ofNat 4), (361, Int.ofNat 2), (402, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 8), (328, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 4), (366, Int.ofNat 4), (405, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(58, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(72, Int.ofNat 2), (323, Int.ofNat 2), (346, Int.ofNat
    4), (383, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1), (356, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(73, Int.ofNat 2), (335, Int.ofNat 2), (361, Int.ofNat
    2), (402, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.ofNat 1), (371, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 4), (74, Int.ofNat 4), (342, Int.ofNat
    4), (366, Int.ofNat 10), (405, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (59, Int.ofNat 1), (68, Int.negSucc
    1), (72, Int.ofNat 2), (323, Int.negSucc 5), (346, Int.ofNat 4), (373, Int.ofNat 2), (377,
    Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat 2), (459,
    Int.negSucc 1), (691, Int.ofNat 2), (704, Int.ofNat 2), (711, Int.negSucc 1), (714,
    Int.negSucc 1)] },
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
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (66, Int.ofNat 1), (69, Int.negSucc
    1), (73, Int.ofNat 2), (335, Int.negSucc 5), (361, Int.ofNat 2), (376, Int.ofNat 2), (387,
    Int.negSucc 1), (397, Int.negSucc 0), (402, Int.negSucc 0), (410, Int.ofNat 2), (444,
    Int.ofNat 2), (688, Int.negSucc 1), (701, Int.negSucc 1), (722, Int.negSucc 1), (725,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(67, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (68, Int.ofNat 2), (72, Int.ofNat
    1), (323, Int.ofNat 1), (346, Int.ofNat 4), (373, Int.ofNat 1), (383, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(73, Int.ofNat 4), (75, Int.ofNat 1), (335, Int.ofNat
    4), (361, Int.ofNat 6), (376, Int.ofNat 4), (402, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(74, Int.ofNat 2), (77, Int.ofNat 1), (342, Int.ofNat
    2), (366, Int.ofNat 4), (381, Int.ofNat 2), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(76, Int.ofNat 1), (400, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.negSucc 3), (74, Int.ofNat 4), (342,
    Int.negSucc 11), (366, Int.ofNat 6), (381, Int.ofNat 4), (393, Int.negSucc 3), (401,
    Int.negSucc 1), (405, Int.negSucc 2), (409, Int.ofNat 4), (438, Int.ofNat 4), (685,
    Int.negSucc 3), (698, Int.negSucc 3), (733, Int.negSucc 3), (736, Int.negSucc 3)] },
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
    0), (95, Int.negSucc 0), (101, Int.ofNat 2), (352, Int.negSucc 5), (379, Int.ofNat 6), (389,
    Int.negSucc 1), (413, Int.ofNat 2), (423, Int.negSucc 1), (428, Int.negSucc 3), (446,
    Int.ofNat 2), (461, Int.ofNat 2), (744, Int.negSucc 1)] },
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
    1), (101, Int.ofNat 4), (352, Int.negSucc 11), (379, Int.ofNat 16), (389, Int.negSucc 3),
    (413, Int.ofNat 4), (423, Int.negSucc 5), (428, Int.negSucc 7), (446, Int.ofNat 4), (461,
    Int.ofNat 4), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.ofNat 1), (98, Int.negSucc
    1), (102, Int.ofNat 2), (357, Int.negSucc 5), (384, Int.ofNat 8), (395, Int.negSucc 1), (416,
    Int.ofNat 2), (427, Int.negSucc 3), (435, Int.negSucc 2), (440, Int.ofNat 2), (460, Int.ofNat
    2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(87, Int.ofNat 1), (384, Int.ofNat 2), (427, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(97, Int.negSucc 1), (99, Int.ofNat 4), (103, Int.ofNat
    2), (372, Int.ofNat 2), (403, Int.ofNat 5), (449, Int.negSucc 0), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.ofNat 1), (85, Int.negSucc
    1), (101, Int.ofNat 4), (352, Int.negSucc 11), (379, Int.ofNat 16), (389, Int.negSucc 3),
    (413, Int.ofNat 6), (423, Int.negSucc 3), (428, Int.negSucc 7), (446, Int.ofNat 4), (461,
    Int.ofNat 4), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 3), (97, Int.ofNat 2), (99, Int.negSucc
    3), (103, Int.ofNat 4), (372, Int.negSucc 11), (403, Int.ofNat 8), (411, Int.negSucc 3), (426,
    Int.ofNat 8), (439, Int.negSucc 3), (445, Int.negSucc 3), (449, Int.negSucc 1), (456,
    Int.negSucc 2), (758, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (98, Int.ofNat 2), (102, Int.ofNat
    1), (357, Int.ofNat 1), (384, Int.ofNat 5), (416, Int.ofNat 1), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(103, Int.ofNat 4), (104, Int.ofNat 1), (372, Int.ofNat
    4), (403, Int.ofNat 8), (426, Int.ofNat 4), (456, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.negSucc 1), (107, Int.ofNat 4), (110,
    Int.negSucc 1), (120, Int.negSucc 3), (124, Int.ofNat 4), (380, Int.ofNat 12), (390,
    Int.negSucc 7), (421, Int.ofNat 12), (464, Int.ofNat 4), (475, Int.negSucc 7), (487,
    Int.negSucc 7), (494, Int.ofNat 4), (509, Int.ofNat 2), (765, Int.negSucc 3)] },
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
    Int.negSucc 0), (128, Int.negSucc 0), (133, Int.ofNat 2), (391, Int.negSucc 5), (429,
    Int.ofNat 10), (441, Int.negSucc 1), (447, Int.negSucc 1), (462, Int.negSucc 1), (468,
    Int.ofNat 2), (482, Int.negSucc 1), (490, Int.negSucc 2), (695, Int.negSucc 1), (745,
    Int.ofNat 2), (752, Int.ofNat 2), (759, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 2), (417, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(133, Int.ofNat 2), (391, Int.ofNat 2), (429, Int.ofNat
    6), (490, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 2), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (128,
    Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 11), (429, Int.ofNat 24), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.ofNat 4), (482,
    Int.negSucc 5), (490, Int.negSucc 5), (695, Int.negSucc 3), (745, Int.ofNat 4), (752,
    Int.ofNat 4), (759, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 3), (118, Int.ofNat 4), (125,
    Int.ofNat 6), (131, Int.negSucc 3), (385, Int.ofNat 14), (396, Int.negSucc 7), (433, Int.ofNat
    12), (471, Int.ofNat 4), (479, Int.ofNat 4), (486, Int.negSucc 7), (497, Int.negSucc 7), (508,
    Int.ofNat 2), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 1), (115, Int.ofNat 1), (117,
    Int.negSucc 1), (133, Int.ofNat 4), (391, Int.negSucc 11), (429, Int.ofNat 24), (441,
    Int.negSucc 3), (447, Int.negSucc 3), (462, Int.negSucc 3), (468, Int.ofNat 6), (482,
    Int.negSucc 3), (490, Int.negSucc 5), (695, Int.negSucc 3), (745, Int.ofNat 4), (752,
    Int.ofNat 4), (759, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 7), (126, Int.ofNat 6), (130,
    Int.ofNat 4), (132, Int.negSucc 3), (404, Int.ofNat 7), (412, Int.negSucc 7), (454, Int.ofNat
    6), (478, Int.negSucc 3), (485, Int.ofNat 8), (493, Int.negSucc 3), (504, Int.negSucc 1),
    (512, Int.negSucc 3), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.ofNat 2), (415, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 4), (425, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (143,
    Int.negSucc 1), (153, Int.negSucc 3), (157, Int.ofNat 4), (430, Int.ofNat 12), (442,
    Int.negSucc 7), (480, Int.ofNat 12), (488, Int.ofNat 8), (495, Int.negSucc 3), (510,
    Int.negSucc 1), (516, Int.ofNat 4), (528, Int.negSucc 7), (547, Int.negSucc 7), (550,
    Int.ofNat 4), (560, Int.ofNat 2), (766, Int.ofNat 4), (787, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.ofNat 2), (491, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 4), (418, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(157, Int.ofNat 4), (430, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 4), (437, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 8), (451, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(159, Int.ofNat 4), (458, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(146, Int.ofNat 1), (469, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(147, Int.ofNat 1), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 4), (139, Int.negSucc 5), (143,
    Int.negSucc 0), (148, Int.ofNat 3), (150, Int.negSucc 1), (153, Int.negSucc 1), (157,
    Int.ofNat 2), (160, Int.negSucc 1), (163, Int.ofNat 4), (430, Int.ofNat 22), (442, Int.negSucc
    7), (448, Int.negSucc 3), (463, Int.negSucc 3), (480, Int.ofNat 10), (488, Int.ofNat 20),
    (495, Int.negSucc 5), (510, Int.negSucc 2), (516, Int.ofNat 2), (520, Int.ofNat 4), (528,
    Int.negSucc 3), (535, Int.negSucc 3), (547, Int.negSucc 11), (550, Int.ofNat 2), (560,
    Int.ofNat 1), (696, Int.negSucc 3), (709, Int.negSucc 3), (746, Int.ofNat 4), (753, Int.ofNat
    4), (760, Int.negSucc 3), (766, Int.ofNat 6), (774, Int.ofNat 4), (781, Int.negSucc 3), (787,
    Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

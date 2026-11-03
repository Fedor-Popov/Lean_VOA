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
def actionData247 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(320, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (308, Int.ofNat 2), (315, Int.ofNat
    1), (319, Int.ofNat 1), (340, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0),
    (368, Int.ofNat 1), (681, Int.negSucc 0), (683, Int.ofNat 1), (686, Int.ofNat 1), (689,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 2), (324, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.ofNat 2), (338, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1), (345, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 2), (322, Int.ofNat 4), (355, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(40, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1), (344, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (327, Int.ofNat 1), (365, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(44, Int.ofNat 2), (316, Int.ofNat 2), (327, Int.ofNat
    2), (343, Int.ofNat 2), (365, Int.negSucc 0), (392, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 2), (341, Int.ofNat 4), (354, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(39, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.ofNat 2), (46, Int.ofNat 2), (316, Int.ofNat
    6), (327, Int.ofNat 1), (343, Int.ofNat 2), (359, Int.ofNat 1), (365, Int.negSucc 0), (392,
    Int.negSucc 3), (682, Int.negSucc 1), (697, Int.ofNat 2), (700, Int.ofNat 2), (703, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(47, Int.ofNat 2), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(344, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 1), (44, Int.ofNat 1), (316, Int.ofNat
    3), (327, Int.ofNat 1), (343, Int.ofNat 1), (365, Int.negSucc 0), (386, Int.negSucc 0), (392,
    Int.negSucc 0), (408, Int.ofNat 1), (682, Int.negSucc 0), (697, Int.ofNat 1), (700, Int.ofNat
    1), (703, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.ofNat 2), (327, Int.ofNat 2), (343, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 2), (363, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (346, Int.ofNat 2), (383, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 2), (323, Int.ofNat 4), (346, Int.ofNat
    4), (394, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 2), (356, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(59, Int.ofNat 1), (61, Int.ofNat 1), (323, Int.ofNat
    6), (346, Int.negSucc 1), (373, Int.negSucc 1), (377, Int.ofNat 2), (383, Int.ofNat 2), (394,
    Int.negSucc 3), (691, Int.negSucc 1), (704, Int.negSucc 1), (711, Int.ofNat 2), (714,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1), (382, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(64, Int.ofNat 2), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (405, Int.negSucc
    0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(68, Int.ofNat 2), (323, Int.ofNat 2), (346, Int.ofNat
    4), (373, Int.ofNat 1), (394, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (69, Int.ofNat 2), (335, Int.ofNat
    4), (361, Int.negSucc 0), (397, Int.ofNat 1), (444, Int.negSucc 1), (688, Int.ofNat 2), (701,
    Int.ofNat 2), (722, Int.ofNat 2), (725, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 4), (342, Int.ofNat 4), (366, Int.ofNat
    4), (393, Int.ofNat 4), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(62, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(70, Int.ofNat 4), (71, Int.ofNat 4), (342, Int.ofNat
    12), (381, Int.negSucc 3), (393, Int.ofNat 8), (401, Int.ofNat 2), (405, Int.ofNat 1), (685,
    Int.ofNat 4), (698, Int.ofNat 4), (733, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (323, Int.ofNat
    6), (346, Int.ofNat 2), (373, Int.negSucc 0), (377, Int.ofNat 2), (383, Int.negSucc 1), (388,
    Int.negSucc 1), (394, Int.negSucc 1), (459, Int.ofNat 2), (691, Int.negSucc 1), (704,
    Int.negSucc 1), (711, Int.ofNat 2), (714, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(382, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (342, Int.ofNat
    12), (366, Int.ofNat 4), (393, Int.ofNat 4), (401, Int.ofNat 2), (405, Int.negSucc 0), (409,
    Int.negSucc 3), (438, Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat 4), (733, Int.ofNat
    4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.ofNat 2), (366, Int.ofNat 2), (381, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (347, Int.ofNat 2), (432, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (384, Int.ofNat 4), (435, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 1), (420, Int.ofNat 2), (432, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 2), (374, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(82, Int.negSucc 0), (85, Int.ofNat 2), (352, Int.ofNat
    8), (379, Int.negSucc 7), (413, Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 4), (446,
    Int.negSucc 3), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.ofNat 2), (357, Int.ofNat 4), (384, Int.ofNat
    4), (395, Int.ofNat 4), (435, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(86, Int.ofNat 1), (87, Int.ofNat 1), (357, Int.ofNat
    6), (384, Int.negSucc 3), (395, Int.ofNat 4), (416, Int.negSucc 1), (427, Int.ofNat 2), (435,
    Int.ofNat 1), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1), (347, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (92, Int.ofNat 2), (362,
    Int.negSucc 0), (419, Int.negSucc 1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 2), (367, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(91, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(98, Int.ofNat 2), (357, Int.ofNat 2), (384, Int.ofNat
    4), (395, Int.ofNat 2), (416, Int.ofNat 1), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(97, Int.negSucc 0), (99, Int.ofNat 2), (372, Int.ofNat
    4), (403, Int.negSucc 1), (426, Int.negSucc 1), (445, Int.ofNat 2), (449, Int.ofNat 1), (456,
    Int.ofNat 1), (758, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(100, Int.ofNat 2), (367, Int.ofNat 3), (431, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 0), (100, Int.ofNat 3), (367, Int.ofNat
    3), (431, Int.ofNat 6), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (357, Int.ofNat
    6), (384, Int.ofNat 2), (395, Int.ofNat 2), (416, Int.negSucc 0), (427, Int.ofNat 4), (435,
    Int.negSucc 0), (440, Int.negSucc 1), (460, Int.negSucc 1), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.negSucc 1), (100, Int.ofNat 2), (367, Int.ofNat
    2), (431, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 2), (380, Int.negSucc 7), (390, Int.ofNat 4), (421, Int.negSucc 11), (464,
    Int.negSucc 3), (475, Int.ofNat 8), (487, Int.ofNat 4), (494, Int.negSucc 3), (765, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (385, Int.ofNat 2), (433, Int.ofNat
    2), (497, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(109, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (433, Int.ofNat 2), (479, Int.ofNat
    2), (497, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 2), (417, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 0), (117, Int.ofNat 2), (391,
    Int.ofNat 8), (429, Int.negSucc 11), (447, Int.ofNat 4), (468, Int.negSucc 3), (482, Int.ofNat
    4), (490, Int.ofNat 4), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc 3), (759,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 2), (385, Int.ofNat 4), (396, Int.ofNat
    8), (433, Int.ofNat 12), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(118, Int.ofNat 1), (119, Int.ofNat 1), (385,
    Int.negSucc 3), (396, Int.ofNat 10), (433, Int.ofNat 4), (471, Int.negSucc 1), (486, Int.ofNat
    2), (497, Int.ofNat 2), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 2), (118, Int.negSucc 1), (119,
    Int.ofNat 5), (385, Int.negSucc 13), (396, Int.ofNat 14), (433, Int.negSucc 5), (471,
    Int.negSucc 5), (486, Int.ofNat 2), (497, Int.ofNat 12), (773, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(120, Int.negSucc 1), (124, Int.ofNat 2), (380,
    Int.negSucc 1), (421, Int.negSucc 1), (464, Int.negSucc 0), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(125, Int.ofNat 1), (385, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (126, Int.ofNat 2), (404,
    Int.negSucc 0), (454, Int.negSucc 0), (478, Int.negSucc 1), (512, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(127, Int.ofNat 2), (407, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(125, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(127, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(131, Int.ofNat 2), (385, Int.ofNat 4), (396, Int.ofNat
    4), (433, Int.ofNat 8), (471, Int.ofNat 1), (497, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (130, Int.negSucc 2), (132,
    Int.ofNat 4), (404, Int.negSucc 3), (412, Int.ofNat 4), (454, Int.negSucc 5), (485,
    Int.negSucc 3), (493, Int.ofNat 4), (504, Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (131, Int.ofNat 2), (385, Int.negSucc 11), (396, Int.ofNat 12), (471,
    Int.negSucc 2), (479, Int.ofNat 2), (486, Int.ofNat 4), (497, Int.ofNat 6), (508, Int.ofNat
    1), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 0), (131,
    Int.ofNat 2), (385, Int.ofNat 2), (396, Int.ofNat 4), (433, Int.ofNat 2), (471, Int.negSucc
    0), (479, Int.negSucc 1), (486, Int.ofNat 4), (497, Int.negSucc 1), (508, Int.negSucc 0),
    (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(118, Int.negSucc 1), (131, Int.ofNat 4), (385,
    Int.ofNat 4), (433, Int.ofNat 4), (471, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (141, Int.ofNat 1), (415,
    Int.negSucc 1), (465, Int.negSucc 1), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (418, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 2), (430, Int.negSucc 7), (442, Int.ofNat 4), (480, Int.negSucc 11), (488,
    Int.negSucc 3), (495, Int.ofNat 4), (516, Int.negSucc 3), (528, Int.ofNat 8), (547, Int.ofNat
    4), (550, Int.negSucc 3), (766, Int.negSucc 3), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (437, Int.ofNat 2), (498, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(144, Int.ofNat 3), (434, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (498, Int.ofNat 4), (532, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 2), (418, Int.ofNat 2), (472, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 2), (139, Int.ofNat 2), (148,
    Int.negSucc 2), (150, Int.ofNat 4), (430, Int.negSucc 23), (443, Int.ofNat 8), (448, Int.ofNat
    8), (480, Int.negSucc 15), (488, Int.negSucc 23), (495, Int.ofNat 8), (520, Int.negSucc 7),
    (535, Int.ofNat 8), (547, Int.ofNat 16), (696, Int.ofNat 8), (709, Int.ofNat 8), (746,
    Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 7), (774,
    Int.negSucc 7), (781, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.negSucc 4), (139, Int.ofNat 2), (143,
    Int.ofNat 2), (148, Int.negSucc 3), (150, Int.ofNat 4), (151, Int.ofNat 4), (430, Int.negSucc
    71), (442, Int.ofNat 4), (443, Int.ofNat 16), (448, Int.ofNat 32), (480, Int.negSucc 43),
    (488, Int.negSucc 51), (495, Int.ofNat 12), (516, Int.negSucc 3), (520, Int.negSucc 15), (524,
    Int.negSucc 7), (528, Int.ofNat 8), (535, Int.ofNat 16), (547, Int.ofNat 36), (550, Int.ofNat
    12), (696, Int.ofNat 16), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15),
    (760, Int.ofNat 16), (766, Int.negSucc 19), (774, Int.negSucc 23), (781, Int.ofNat 16), (787,
    Int.ofNat 4), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (157, Int.ofNat 2), (430,
    Int.negSucc 1), (480, Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 1), (437, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(455, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.negSucc 1), (159, Int.ofNat 2), (458,
    Int.negSucc 0), (513, Int.negSucc 1), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1), (149, Int.ofNat 4), (418, Int.ofNat
    5), (472, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

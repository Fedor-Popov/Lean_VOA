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
def actionData160 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(14, Int.negSucc 0), (313, Int.ofNat 2), (337,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(19, Int.negSucc 0), (312, Int.negSucc 3), (336,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(20, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 2), (21, Int.negSucc 3), (336,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(20, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(24, Int.negSucc 3), (326, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(29, Int.negSucc 1), (315, Int.negSucc 1), (340,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(27, Int.negSucc 1), (325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.negSucc 1), (339, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(30, Int.negSucc 3), (308, Int.negSucc 3), (315,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(320, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (30, Int.negSucc 1), (31, Int.negSucc
    1), (308, Int.negSucc 1), (315, Int.negSucc 1), (340, Int.negSucc 1), (368, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.negSucc 0), (339, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.ofNat 1), (339, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(33, Int.negSucc 0), (324, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(34, Int.negSucc 0), (338, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(325, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(324, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 2), (30, Int.negSucc 1), (35, Int.negSucc
    1), (308, Int.negSucc 1), (315, Int.negSucc 1), (340, Int.negSucc 1), (353, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(331, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(34, Int.negSucc 0), (338, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(339, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(338, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc
    0), (308, Int.ofNat 1), (315, Int.negSucc 0), (348, Int.negSucc 0), (353, Int.negSucc 0),
    (368, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.negSucc 0), (339, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(34, Int.negSucc 0), (338, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(34, Int.ofNat 1), (338, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 3), (327, Int.negSucc 1), (365,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(48, Int.negSucc 1), (316, Int.negSucc 1), (327,
    Int.negSucc 1), (365, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(49, Int.negSucc 1), (341, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(344, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (46, Int.negSucc
    1), (48, Int.negSucc 1), (365, Int.negSucc 0), (408, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.negSucc 1), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(38, Int.ofNat 2), (50, Int.negSucc 3), (355,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.ofNat 2), (51, Int.negSucc 3), (370,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(49, Int.negSucc 1), (341, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(40, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (49, Int.negSucc 0), (369,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.negSucc 1), (364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.ofNat 2), (364, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (54, Int.negSucc 0), (365, Int.negSucc 0), (392, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(358, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(55, Int.negSucc 0), (363, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.ofNat 2), (48, Int.negSucc
    1), (316, Int.ofNat 4), (327, Int.ofNat 1), (365, Int.negSucc 0), (386, Int.negSucc 1), (392,
    Int.negSucc 1), (408, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(363, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(45, Int.ofNat 1), (49, Int.negSucc 0), (354, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(53, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.negSucc 0), (363, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(363, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(45, Int.ofNat 1), (49, Int.negSucc 2), (341,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 2), (363, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.negSucc 3), (328, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 3), (366, Int.negSucc 3), (405,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (59, Int.ofNat 1), (72, Int.negSucc
    1), (394, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(63, Int.ofNat 2), (66, Int.ofNat 1), (73, Int.negSucc
    1), (410, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(74, Int.negSucc 1), (342, Int.negSucc 1), (366,
    Int.negSucc 2), (405, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(57, Int.ofNat 1), (68, Int.ofNat 2), (72, Int.negSucc
    1), (323, Int.ofNat 4), (373, Int.negSucc 0), (377, Int.ofNat 2), (388, Int.negSucc 1), (394,
    Int.negSucc 1), (459, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(382, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (71, Int.negSucc
    3), (74, Int.negSucc 3), (401, Int.ofNat 2), (405, Int.negSucc 0), (409, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(60, Int.ofNat 1), (356, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(67, Int.ofNat 1), (371, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 4), (74, Int.negSucc 3), (342,
    Int.negSucc 3), (366, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(62, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 1), (70, Int.ofNat 2), (74, Int.negSucc
    1), (409, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 0), (70, Int.ofNat 2), (71, Int.ofNat
    4), (342, Int.ofNat 2), (366, Int.ofNat 3), (401, Int.negSucc 1), (409, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (69, Int.ofNat 4), (73, Int.negSucc
    3), (335, Int.ofNat 8), (376, Int.negSucc 3), (387, Int.ofNat 4), (397, Int.ofNat 1), (410,
    Int.negSucc 3), (444, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(65, Int.ofNat 4), (70, Int.ofNat 4), (74, Int.negSucc
    3), (77, Int.negSucc 1), (381, Int.negSucc 3), (393, Int.ofNat 4), (405, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(400, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (70, Int.ofNat 2), (74, Int.negSucc
    1), (342, Int.ofNat 4), (381, Int.negSucc 1), (393, Int.ofNat 2), (401, Int.ofNat 1), (409,
    Int.negSucc 1), (438, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 1), (70, Int.ofNat 2), (74, Int.negSucc
    1), (393, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(76, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(70, Int.ofNat 6), (74, Int.negSucc 1), (77, Int.ofNat
    1), (342, Int.ofNat 8), (366, Int.ofNat 2), (381, Int.negSucc 1), (393, Int.ofNat 2), (401,
    Int.ofNat 2), (409, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 5), (70, Int.ofNat 2), (74, Int.negSucc
    5), (342, Int.negSucc 3), (366, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 1), (70, Int.ofNat 4), (77, Int.ofNat
    4), (342, Int.ofNat 4), (366, Int.ofNat 6), (381, Int.ofNat 8), (393, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.ofNat 2), (91, Int.negSucc 3), (432,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.ofNat 4), (92, Int.negSucc 3), (453,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.negSucc 3), (367, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(94, Int.negSucc 3), (406, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 2), (82, Int.negSucc 0), (85, Int.ofNat
    2), (95, Int.ofNat 2), (101, Int.negSucc 3), (352, Int.ofNat 8), (379, Int.negSucc 3), (389,
    Int.ofNat 4), (413, Int.negSucc 1), (423, Int.ofNat 2), (428, Int.ofNat 4), (446, Int.negSucc
    3), (461, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (86, Int.ofNat 1), (102, Int.negSucc
    1), (395, Int.ofNat 2), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.ofNat 4), (97, Int.ofNat 2), (103, Int.negSucc
    3), (411, Int.ofNat 4), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.negSucc 7), (367, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(94, Int.negSucc 7), (406, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.ofNat 1), (98, Int.ofNat 2), (102, Int.negSucc
    1), (357, Int.ofNat 4), (384, Int.negSucc 1), (395, Int.ofNat 2), (416, Int.negSucc 0), (427,
    Int.ofNat 4), (440, Int.negSucc 1), (460, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(93, Int.negSucc 2), (100, Int.ofNat 1), (452,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 3, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (357, Int.ofNat
    4), (395, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 1), (97, Int.ofNat 2), (372, Int.ofNat
    4), (411, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(86, Int.negSucc 0), (87, Int.ofNat 1), (98, Int.ofNat
    2), (357, Int.ofNat 4), (384, Int.negSucc 1), (395, Int.ofNat 2), (416, Int.negSucc 0), (427,
    Int.ofNat 2), (435, Int.ofNat 1), (460, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 3), (97, Int.ofNat 6), (99, Int.ofNat
    8), (103, Int.negSucc 3), (372, Int.ofNat 16), (403, Int.ofNat 4), (411, Int.ofNat 20), (449,
    Int.negSucc 1), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (372, Int.ofNat 8), (403, Int.negSucc 1), (411, Int.ofNat 4), (426, Int.negSucc 7), (439,
    Int.ofNat 4), (445, Int.ofNat 4), (449, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 2), (100, Int.ofNat 1), (431, Int.ofNat
    2)] },
  { denominator := Int.ofNat 6, terms := [(94, Int.ofNat 2), (406, Int.ofNat 3)] },
  { denominator := Int.ofNat 8, terms := [(105, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 2), (100, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(406, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.ofNat 3), (98, Int.ofNat
    4), (102, Int.negSucc 1), (357, Int.ofNat 8), (384, Int.ofNat 4), (395, Int.ofNat 10), (416,
    Int.ofNat 2), (435, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(97, Int.ofNat 4), (99, Int.ofNat 4), (103, Int.negSucc
    3), (104, Int.ofNat 1), (372, Int.ofNat 16), (403, Int.negSucc 1), (411, Int.ofNat 16), (426,
    Int.negSucc 3), (445, Int.ofNat 4), (449, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(106, Int.ofNat 1), (107, Int.negSucc 1), (110,
    Int.ofNat 2), (120, Int.ofNat 4), (124, Int.negSucc 3), (380, Int.negSucc 3), (390, Int.ofNat
    4), (421, Int.negSucc 3), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 4), (494,
    Int.negSucc 3), (509, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 2), (125, Int.negSucc 3), (433,
    Int.ofNat 4), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 4), (126, Int.negSucc 3), (454,
    Int.ofNat 2), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(127, Int.negSucc 3), (407, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 8), (429, Int.negSucc
    7), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 1), (482,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.ofNat 1), (125,
    Int.negSucc 3), (396, Int.ofNat 4), (433, Int.ofNat 8), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.negSucc 3), (130,
    Int.ofNat 1), (412, Int.ofNat 4), (454, Int.ofNat 4), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 3, terms := [(123, Int.ofNat 2), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.negSucc 7), (407, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 4), (385, Int.negSucc 3), (396, Int.ofNat 4), (433,
    Int.negSucc 3), (471, Int.negSucc 1), (479, Int.negSucc 3), (486, Int.ofNat 8), (508,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(436, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (118, Int.negSucc 1), (119,
    Int.ofNat 1), (131, Int.ofNat 2), (385, Int.negSucc 1), (396, Int.ofNat 2), (433, Int.negSucc
    1), (471, Int.negSucc 0), (486, Int.ofNat 2), (497, Int.ofNat 2), (508, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 8), (404, Int.ofNat 4), (412, Int.ofNat 4), (454, Int.ofNat
    8), (504, Int.negSucc 1), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 4), (417, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 1), (117, Int.ofNat 2), (128,
    Int.ofNat 2), (391, Int.ofNat 8), (429, Int.negSucc 7), (447, Int.ofNat 4), (462, Int.ofNat
    4), (468, Int.negSucc 1), (482, Int.ofNat 2), (490, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 4), (450, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (404, Int.negSucc 1), (412, Int.ofNat 4), (454,
    Int.negSucc 1), (478, Int.ofNat 4), (485, Int.negSucc 7), (493, Int.ofNat 4), (504, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(457, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 8), (385, Int.ofNat 8), (396, Int.ofNat 4), (433, Int.ofNat
    16), (471, Int.ofNat 4), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (134, Int.ofNat 1), (404, Int.negSucc 1), (412, Int.ofNat
    8), (454, Int.ofNat 2), (485, Int.negSucc 3), (493, Int.ofNat 4), (504, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 2), (153, Int.ofNat 4), (157, Int.negSucc 3), (430, Int.negSucc 3), (442, Int.ofNat
    4), (480, Int.negSucc 3), (488, Int.negSucc 3), (495, Int.ofNat 4), (510, Int.ofNat 2), (516,
    Int.negSucc 1), (528, Int.ofNat 4), (547, Int.ofNat 4), (550, Int.negSucc 3), (560,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 2), (158, Int.negSucc 3), (498,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 4), (159, Int.negSucc 3), (513,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] }
]

end VOA.DeligneAudit.D4Two.Certificate

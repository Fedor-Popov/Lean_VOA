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
def actionData168 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(66, Int.negSucc 1), (69, Int.ofNat 4), (335, Int.ofNat
    8), (361, Int.negSucc 1), (397, Int.ofNat 1), (444, Int.negSucc 3), (688, Int.ofNat 4), (701,
    Int.ofNat 4), (722, Int.ofNat 4), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.negSucc 1), (324, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(400, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 1), (316, Int.negSucc 3), (343,
    Int.negSucc 1), (408, Int.negSucc 1), (682, Int.ofNat 2), (697, Int.negSucc 1), (700,
    Int.negSucc 1), (703, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(33, Int.negSucc 0), (324, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(78, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 2), (327, Int.ofNat 1), (343, Int.ofNat
    2), (365, Int.negSucc 0), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (323, Int.negSucc 3), (346,
    Int.ofNat 4), (373, Int.ofNat 2), (377, Int.negSucc 1), (388, Int.ofNat 2), (691, Int.ofNat
    2), (704, Int.ofNat 4), (711, Int.negSucc 1), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(420, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.ofNat 8), (379, Int.negSucc 11), (413,
    Int.negSucc 3), (423, Int.ofNat 4), (428, Int.ofNat 4), (694, Int.negSucc 3), (744, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(44, Int.ofNat 2), (316, Int.ofNat 2), (327, Int.ofNat
    2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 0), (408, Int.ofNat 2), (703,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (323, Int.negSucc 5), (346,
    Int.ofNat 4), (373, Int.ofNat 2), (377, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat
    2), (394, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat 4), (711, Int.negSucc 1), (714,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(347, Int.negSucc 1), (420, Int.ofNat 2), (432,
    Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.ofNat 8), (384, Int.negSucc 11), (416,
    Int.negSucc 3), (427, Int.ofNat 4), (435, Int.ofNat 4), (693, Int.negSucc 3), (751, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (343, Int.ofNat
    2), (359, Int.negSucc 0), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.negSucc 0), (323, Int.negSucc 3), (346,
    Int.ofNat 4), (373, Int.ofNat 2), (383, Int.negSucc 1), (394, Int.ofNat 2), (691, Int.ofNat
    2), (704, Int.ofNat 4), (711, Int.negSucc 1), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (327, Int.negSucc 0), (359,
    Int.ofNat 1), (365, Int.ofNat 1), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 1), (335, Int.negSucc 3), (361,
    Int.ofNat 2), (376, Int.ofNat 2), (387, Int.negSucc 1), (397, Int.negSucc 0), (688,
    Int.negSucc 1), (701, Int.negSucc 3), (722, Int.negSucc 1), (725, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(419, Int.negSucc 0), (702, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(363, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 1), (342, Int.negSucc 3), (438,
    Int.ofNat 2), (685, Int.negSucc 1), (698, Int.negSucc 1), (733, Int.negSucc 1), (736,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(44, Int.negSucc 1), (316, Int.negSucc 1), (327,
    Int.negSucc 1), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (392, Int.ofNat
    2), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (335, Int.negSucc 5), (361,
    Int.ofNat 2), (376, Int.ofNat 2), (387, Int.negSucc 1), (397, Int.negSucc 0), (402,
    Int.negSucc 0), (410, Int.ofNat 2), (688, Int.negSucc 1), (701, Int.negSucc 3), (722,
    Int.negSucc 1), (725, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(362, Int.negSucc 0), (419, Int.negSucc 1), (453,
    Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(372, Int.ofNat 8), (403, Int.negSucc 5), (426,
    Int.negSucc 3), (449, Int.ofNat 2), (456, Int.ofNat 2), (692, Int.ofNat 4), (758, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(39, Int.negSucc 0), (344, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(36, Int.negSucc 0), (345, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(59, Int.ofNat 1), (68, Int.negSucc 3), (323,
    Int.negSucc 9), (346, Int.ofNat 4), (373, Int.ofNat 2), (377, Int.negSucc 1), (383,
    Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat 2), (459, Int.negSucc 1), (691, Int.ofNat
    4), (704, Int.ofNat 6), (711, Int.negSucc 3), (714, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(347, Int.negSucc 0), (420, Int.ofNat 1), (432,
    Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(52, Int.ofNat 1), (358, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.negSucc 0), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.ofNat 1), (69, Int.negSucc 3), (335,
    Int.negSucc 9), (361, Int.ofNat 2), (376, Int.ofNat 2), (387, Int.negSucc 1), (397,
    Int.negSucc 0), (402, Int.negSucc 0), (410, Int.ofNat 2), (444, Int.ofNat 2), (688,
    Int.negSucc 3), (701, Int.negSucc 5), (722, Int.negSucc 3), (725, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(362, Int.negSucc 0), (419, Int.negSucc 1), (453,
    Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (44, Int.negSucc 1), (316,
    Int.negSucc 5), (327, Int.negSucc 0), (343, Int.negSucc 1), (359, Int.ofNat 1), (365,
    Int.ofNat 1), (386, Int.ofNat 4), (682, Int.ofNat 2), (697, Int.negSucc 3), (700, Int.negSucc
    1), (703, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 0), (70, Int.negSucc 1), (342,
    Int.negSucc 9), (366, Int.ofNat 2), (381, Int.ofNat 2), (393, Int.negSucc 1), (401,
    Int.negSucc 0), (405, Int.negSucc 0), (409, Int.ofNat 2), (438, Int.ofNat 2), (685,
    Int.negSucc 3), (698, Int.negSucc 5), (733, Int.negSucc 3), (736, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(367, Int.negSucc 0), (431, Int.negSucc 1), (452,
    Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.negSucc 1), (327, Int.negSucc 0), (359,
    Int.ofNat 1), (365, Int.ofNat 1), (697, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(71, Int.negSucc 1), (342, Int.negSucc 3), (366,
    Int.ofNat 2), (381, Int.ofNat 2), (393, Int.negSucc 1), (405, Int.negSucc 0), (685,
    Int.negSucc 1), (698, Int.negSucc 3), (733, Int.negSucc 1), (736, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(431, Int.negSucc 0), (699, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 0), (91, Int.ofNat 2), (347,
    Int.negSucc 1), (420, Int.ofNat 4), (432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (92, Int.ofNat 2), (362,
    Int.negSucc 0), (419, Int.negSucc 3), (453, Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 3), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 1), (327, Int.negSucc 1), (343,
    Int.negSucc 3), (359, Int.ofNat 2), (700, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.negSucc 0), (335, Int.negSucc 7), (361,
    Int.ofNat 4), (397, Int.negSucc 1), (402, Int.negSucc 1), (410, Int.ofNat 4), (688,
    Int.negSucc 3), (701, Int.negSucc 7), (722, Int.negSucc 3), (725, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(453, Int.ofNat 2), (702, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(105, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 0), (327, Int.negSucc 0), (343,
    Int.negSucc 1), (365, Int.ofNat 1), (697, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 0), (342, Int.negSucc 3), (366,
    Int.ofNat 2), (401, Int.negSucc 0), (405, Int.negSucc 0), (409, Int.ofNat 2), (685,
    Int.negSucc 1), (698, Int.negSucc 3), (733, Int.negSucc 1), (736, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(452, Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (380, Int.negSucc 7), (390,
    Int.ofNat 8), (421, Int.negSucc 7), (464, Int.negSucc 3), (475, Int.ofNat 8), (708,
    Int.negSucc 3), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 2), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (381, Int.ofNat
    4), (405, Int.negSucc 0), (685, Int.ofNat 4), (698, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (357, Int.negSucc 7), (384,
    Int.ofNat 8), (416, Int.ofNat 4), (427, Int.negSucc 3), (435, Int.negSucc 1), (440, Int.ofNat
    4), (693, Int.ofNat 4), (737, Int.ofNat 4), (751, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(479, Int.ofNat 4), (707, Int.negSucc 3), (738,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 11), (390, Int.ofNat 8), (421,
    Int.negSucc 11), (464, Int.negSucc 3), (475, Int.ofNat 8), (487, Int.ofNat 4), (708,
    Int.negSucc 3), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.ofNat 16), (429, Int.negSucc 23), (468,
    Int.negSucc 7), (482, Int.ofNat 8), (490, Int.ofNat 8), (695, Int.ofNat 16), (745, Int.negSucc
    7), (752, Int.negSucc 7), (759, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(69, Int.ofNat 4), (335, Int.ofNat 4), (361, Int.ofNat
    4), (376, Int.ofNat 4), (387, Int.ofNat 4), (397, Int.negSucc 0), (410, Int.negSucc 3), (688,
    Int.ofNat 8), (701, Int.ofNat 8), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (85, Int.negSucc 1), (352,
    Int.negSucc 15), (379, Int.ofNat 20), (413, Int.ofNat 8), (423, Int.negSucc 5), (428,
    Int.negSucc 7), (446, Int.ofNat 4), (694, Int.ofNat 8), (726, Int.ofNat 4), (744, Int.negSucc
    7)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 5), (390, Int.ofNat 4), (421,
    Int.negSucc 5), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 2), (494, Int.ofNat
    2), (708, Int.negSucc 3), (727, Int.ofNat 2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(385, Int.negSucc 5), (396, Int.ofNat 4), (433,
    Int.negSucc 5), (471, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (707, Int.negSucc 3), (738, Int.ofNat 2), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 7), (396, Int.ofNat 8), (433, Int.negSucc 7), (471,
    Int.negSucc 3), (497, Int.ofNat 8), (707, Int.negSucc 3), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(64, Int.negSucc 1), (328, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (366, Int.negSucc 1), (401,
    Int.ofNat 2), (405, Int.ofNat 1), (685, Int.negSucc 3), (698, Int.negSucc 3), (733,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (372, Int.negSucc 7), (403,
    Int.ofNat 4), (426, Int.ofNat 4), (439, Int.negSucc 3), (449, Int.negSucc 1), (456,
    Int.negSucc 0), (692, Int.negSucc 3), (734, Int.negSucc 3), (758, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(478, Int.negSucc 1), (706, Int.ofNat 2), (735,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(68, Int.negSucc 1), (323, Int.negSucc 1), (346,
    Int.negSucc 3), (373, Int.negSucc 0), (377, Int.ofNat 2), (388, Int.ofNat 2), (394, Int.ofNat
    2), (691, Int.ofNat 4), (704, Int.ofNat 4), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (95, Int.negSucc 1), (352,
    Int.negSucc 15), (379, Int.ofNat 20), (413, Int.ofNat 6), (423, Int.negSucc 7), (428,
    Int.negSucc 7), (461, Int.ofNat 4), (694, Int.ofNat 8), (715, Int.negSucc 3), (744,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 5), (390, Int.ofNat 4), (421,
    Int.negSucc 5), (464, Int.negSucc 1), (475, Int.ofNat 4), (487, Int.ofNat 2), (509, Int.ofNat
    1), (708, Int.negSucc 3), (716, Int.negSucc 1), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 2), (412, Int.ofNat 4), (454,
    Int.negSucc 2), (478, Int.negSucc 1), (485, Int.negSucc 1), (504, Int.ofNat 1), (512,
    Int.ofNat 2), (706, Int.ofNat 4), (735, Int.negSucc 1), (780, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (323,
    Int.negSucc 5), (373, Int.ofNat 1), (377, Int.negSucc 1), (383, Int.ofNat 2), (388, Int.ofNat
    4), (394, Int.ofNat 2), (691, Int.ofNat 6), (704, Int.ofNat 8), (711, Int.negSucc 3), (714,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (98, Int.negSucc
    3), (357, Int.negSucc 23), (384, Int.ofNat 28), (416, Int.ofNat 10), (427, Int.negSucc 11),
    (435, Int.negSucc 9), (440, Int.ofNat 4), (460, Int.ofNat 4), (693, Int.ofNat 12), (712,
    Int.negSucc 3), (737, Int.ofNat 4), (751, Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 5), (396, Int.ofNat 4), (433,
    Int.negSucc 5), (471, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (508, Int.ofNat 1), (707, Int.negSucc 5), (713, Int.negSucc 1), (738, Int.ofNat 2), (773,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 3), (69, Int.negSucc 3), (335,
    Int.negSucc 11), (376, Int.ofNat 4), (387, Int.negSucc 7), (397, Int.negSucc 0), (402,
    Int.ofNat 2), (410, Int.ofNat 4), (688, Int.negSucc 11), (701, Int.negSucc 15), (722,
    Int.negSucc 7), (725, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 1), (97, Int.ofNat 2), (99, Int.negSucc
    3), (372, Int.negSucc 23), (403, Int.ofNat 14), (426, Int.ofNat 12), (439, Int.negSucc 3),
    (445, Int.negSucc 3), (449, Int.negSucc 4), (456, Int.negSucc 4), (692, Int.negSucc 11), (723,
    Int.negSucc 3), (734, Int.negSucc 3), (758, Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(404, Int.negSucc 2), (412, Int.ofNat 4), (454,
    Int.negSucc 2), (478, Int.negSucc 1), (485, Int.negSucc 1), (493, Int.negSucc 1), (504,
    Int.ofNat 1), (512, Int.ofNat 2), (706, Int.ofNat 6), (724, Int.negSucc 1), (735, Int.negSucc
    1), (780, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.negSucc 2), (328, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.negSucc 2), (100, Int.negSucc 0), (431,
    Int.ofNat 2), (452, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 1), (110, Int.negSucc 0), (120,
    Int.negSucc 1), (124, Int.ofNat 2), (380, Int.negSucc 7), (390, Int.ofNat 6), (421,
    Int.negSucc 5), (464, Int.negSucc 2), (475, Int.ofNat 6), (494, Int.ofNat 2), (509, Int.ofNat
    1), (708, Int.negSucc 3), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 3), (125,
    Int.ofNat 4), (131, Int.negSucc 3), (385, Int.negSucc 7), (396, Int.ofNat 4), (433,
    Int.negSucc 3), (471, Int.negSucc 1), (479, Int.ofNat 12), (497, Int.ofNat 4), (508, Int.ofNat
    2), (707, Int.negSucc 11), (738, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (126, Int.ofNat 4), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.negSucc 3), (412, Int.ofNat 4), (454,
    Int.negSucc 1), (478, Int.negSucc 11), (493, Int.negSucc 3), (504, Int.ofNat 1), (512,
    Int.ofNat 2), (706, Int.ofNat 12), (735, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(122, Int.ofNat 2), (130, Int.negSucc 0), (134,
    Int.ofNat 1), (404, Int.negSucc 3), (412, Int.ofNat 8), (454, Int.negSucc 3), (504, Int.ofNat
    2), (512, Int.ofNat 4), (706, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (430, Int.negSucc 15), (442,
    Int.ofNat 16), (480, Int.negSucc 15), (516, Int.negSucc 7), (528, Int.ofNat 16), (709,
    Int.ofNat 8), (741, Int.negSucc 7), (766, Int.negSucc 7), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(92, Int.ofNat 2), (362, Int.ofNat 1), (419, Int.ofNat
    2), (702, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 1), (380, Int.ofNat 8), (390, Int.negSucc 3), (421, Int.ofNat 12), (464, Int.ofNat
    4), (475, Int.negSucc 3), (487, Int.negSucc 3), (708, Int.ofNat 4), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

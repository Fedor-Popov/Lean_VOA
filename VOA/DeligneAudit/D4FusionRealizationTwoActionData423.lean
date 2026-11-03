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
def actionData423 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 3), (316, Int.negSucc 7), (327,
    Int.ofNat 2), (365, Int.ofNat 1), (386, Int.ofNat 2), (682, Int.ofNat 10), (697, Int.negSucc
    5), (700, Int.negSucc 5), (703, Int.negSucc 5), (813, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (315, Int.negSucc 1), (319,
    Int.negSucc 1), (332, Int.ofNat 2), (340, Int.ofNat 2), (353, Int.ofNat 2), (686, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(43, Int.negSucc 0), (334, Int.negSucc 1), (349,
    Int.negSucc 1), (370, Int.ofNat 2), (687, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(335, Int.ofNat 8), (361, Int.negSucc 4), (376,
    Int.negSucc 1), (397, Int.ofNat 2), (402, Int.ofNat 1), (701, Int.ofNat 6), (722, Int.ofNat
    6), (725, Int.ofNat 6), (815, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(33, Int.ofNat 1), (324, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(27, Int.negSucc 1), (325, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(24, Int.negSucc 1), (326, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.negSucc 3), (316, Int.negSucc 11), (343,
    Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (386, Int.ofNat 2), (392, Int.ofNat
    2), (408, Int.negSucc 1), (682, Int.ofNat 10), (697, Int.negSucc 5), (700, Int.negSucc 5),
    (703, Int.negSucc 5), (813, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(328, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(26, Int.negSucc 1), (315, Int.negSucc 1), (319,
    Int.negSucc 1), (332, Int.ofNat 2), (340, Int.ofNat 2), (348, Int.ofNat 2), (683, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(45, Int.negSucc 0), (341, Int.negSucc 1), (354,
    Int.negSucc 1), (369, Int.ofNat 2), (684, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(342, Int.ofNat 8), (366, Int.negSucc 4), (381,
    Int.negSucc 1), (401, Int.ofNat 1), (405, Int.ofNat 2), (698, Int.ofNat 6), (733, Int.ofNat
    6), (736, Int.ofNat 6), (814, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(324, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(326, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.negSucc 3), (316, Int.negSucc 7), (327,
    Int.ofNat 2), (359, Int.ofNat 1), (392, Int.ofNat 2), (682, Int.ofNat 10), (697, Int.negSucc
    5), (700, Int.negSucc 5), (703, Int.negSucc 5), (813, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(27, Int.negSucc 1), (325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(47, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (342, Int.ofNat 16), (366,
    Int.negSucc 5), (405, Int.ofNat 3), (438, Int.negSucc 3), (685, Int.ofNat 4), (698, Int.ofNat
    12), (733, Int.ofNat 12), (736, Int.ofNat 12), (814, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(59, Int.negSucc 0), (68, Int.ofNat 2), (323, Int.ofNat
    8), (346, Int.negSucc 5), (373, Int.negSucc 2), (459, Int.ofNat 2), (691, Int.negSucc 1),
    (704, Int.negSucc 5), (711, Int.ofNat 6), (714, Int.ofNat 6), (818, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(66, Int.negSucc 1), (69, Int.ofNat 4), (335, Int.ofNat
    16), (361, Int.negSucc 5), (397, Int.ofNat 3), (444, Int.negSucc 3), (688, Int.ofNat 4), (701,
    Int.ofNat 12), (722, Int.ofNat 12), (725, Int.ofNat 12), (815, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.negSucc 1), (324, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(52, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(400, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(325, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(326, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 1), (316, Int.negSucc 7), (327,
    Int.ofNat 2), (343, Int.negSucc 1), (408, Int.negSucc 1), (682, Int.ofNat 10), (697,
    Int.negSucc 5), (700, Int.negSucc 5), (703, Int.negSucc 5), (813, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(33, Int.negSucc 0), (324, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(55, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(78, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 2), (327, Int.ofNat 1), (343, Int.ofNat
    2), (365, Int.negSucc 0), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (323, Int.negSucc 7), (346,
    Int.ofNat 8), (373, Int.ofNat 4), (377, Int.negSucc 1), (388, Int.ofNat 2), (691, Int.ofNat
    2), (704, Int.ofNat 8), (711, Int.negSucc 5), (714, Int.negSucc 5), (818, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(420, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.ofNat 16), (379, Int.negSucc 19), (413,
    Int.negSucc 7), (423, Int.ofNat 8), (428, Int.ofNat 4), (694, Int.negSucc 11), (744, Int.ofNat
    12), (821, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(44, Int.ofNat 2), (316, Int.ofNat 2), (327, Int.ofNat
    2), (343, Int.ofNat 2), (359, Int.negSucc 0), (365, Int.negSucc 0), (408, Int.ofNat 2), (703,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (323, Int.negSucc 9), (346,
    Int.ofNat 8), (373, Int.ofNat 4), (377, Int.negSucc 1), (383, Int.negSucc 1), (388, Int.ofNat
    2), (394, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat 8), (711, Int.negSucc 5), (714,
    Int.negSucc 5), (818, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(347, Int.negSucc 1), (420, Int.ofNat 2), (432,
    Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.ofNat 16), (384, Int.negSucc 19), (416,
    Int.negSucc 7), (427, Int.ofNat 4), (435, Int.ofNat 8), (693, Int.negSucc 11), (751, Int.ofNat
    12), (819, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(46, Int.ofNat 2), (327, Int.ofNat 1), (343, Int.ofNat
    2), (359, Int.negSucc 0), (703, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.negSucc 0), (323, Int.negSucc 7), (346,
    Int.ofNat 8), (373, Int.ofNat 4), (383, Int.negSucc 1), (394, Int.ofNat 2), (691, Int.ofNat
    2), (704, Int.ofNat 8), (711, Int.negSucc 5), (714, Int.negSucc 5), (818, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (327, Int.negSucc 0), (359,
    Int.ofNat 1), (365, Int.ofNat 1), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(63, Int.negSucc 0), (335, Int.negSucc 3), (361,
    Int.ofNat 2), (376, Int.ofNat 1), (387, Int.negSucc 0), (397, Int.negSucc 0), (688,
    Int.negSucc 0), (701, Int.negSucc 3), (722, Int.negSucc 2), (725, Int.negSucc 2), (815,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(419, Int.negSucc 0), (702, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(363, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(364, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 1), (342, Int.negSucc 7), (366,
    Int.ofNat 2), (405, Int.negSucc 0), (438, Int.ofNat 2), (685, Int.negSucc 1), (698,
    Int.negSucc 5), (733, Int.negSucc 5), (736, Int.negSucc 5), (814, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(44, Int.negSucc 1), (316, Int.negSucc 1), (327,
    Int.negSucc 1), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat 1), (392, Int.ofNat
    2), (700, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (335, Int.negSucc 9), (361,
    Int.ofNat 4), (376, Int.ofNat 2), (387, Int.negSucc 1), (397, Int.negSucc 1), (402,
    Int.negSucc 0), (410, Int.ofNat 2), (688, Int.negSucc 1), (701, Int.negSucc 7), (722,
    Int.negSucc 5), (725, Int.negSucc 5), (815, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(362, Int.negSucc 0), (419, Int.negSucc 1), (453,
    Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(372, Int.ofNat 16), (403, Int.negSucc 9), (426,
    Int.negSucc 3), (449, Int.ofNat 4), (456, Int.ofNat 4), (692, Int.ofNat 12), (758, Int.ofNat
    12), (816, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(39, Int.negSucc 0), (344, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(36, Int.negSucc 0), (345, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(59, Int.ofNat 1), (68, Int.negSucc 3), (323,
    Int.negSucc 17), (346, Int.ofNat 12), (373, Int.ofNat 6), (377, Int.negSucc 1), (383,
    Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat 2), (459, Int.negSucc 1), (691, Int.ofNat
    4), (704, Int.ofNat 14), (711, Int.negSucc 11), (714, Int.negSucc 11), (818, Int.negSucc 7)]
    },
  { denominator := Int.ofNat 1, terms := [(347, Int.negSucc 0), (420, Int.ofNat 1), (432,
    Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(52, Int.ofNat 1), (358, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.negSucc 0), (360, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(66, Int.ofNat 1), (69, Int.negSucc 3), (335,
    Int.negSucc 17), (361, Int.ofNat 6), (376, Int.ofNat 2), (387, Int.negSucc 1), (397,
    Int.negSucc 2), (402, Int.negSucc 0), (410, Int.ofNat 2), (444, Int.ofNat 2), (688,
    Int.negSucc 3), (701, Int.negSucc 13), (722, Int.negSucc 11), (725, Int.negSucc 11), (815,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(362, Int.negSucc 0), (419, Int.negSucc 1), (453,
    Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 1), (44, Int.negSucc 1), (316,
    Int.negSucc 9), (327, Int.ofNat 1), (343, Int.negSucc 1), (359, Int.ofNat 1), (365, Int.ofNat
    1), (386, Int.ofNat 4), (682, Int.ofNat 10), (697, Int.negSucc 7), (700, Int.negSucc 5), (703,
    Int.negSucc 5), (813, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 0), (70, Int.negSucc 1), (342,
    Int.negSucc 17), (366, Int.ofNat 6), (381, Int.ofNat 2), (393, Int.negSucc 1), (401,
    Int.negSucc 0), (405, Int.negSucc 2), (409, Int.ofNat 2), (438, Int.ofNat 2), (685,
    Int.negSucc 3), (698, Int.negSucc 13), (733, Int.negSucc 11), (736, Int.negSucc 11), (814,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(367, Int.negSucc 0), (431, Int.negSucc 1), (452,
    Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(46, Int.negSucc 1), (327, Int.negSucc 0), (359,
    Int.ofNat 1), (365, Int.ofNat 1), (697, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(71, Int.negSucc 0), (342, Int.negSucc 3), (366,
    Int.ofNat 2), (381, Int.ofNat 1), (393, Int.negSucc 0), (405, Int.negSucc 0), (685,
    Int.negSucc 0), (698, Int.negSucc 3), (733, Int.negSucc 2), (736, Int.negSucc 2), (814,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(431, Int.negSucc 0), (699, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 0), (91, Int.ofNat 2), (347,
    Int.negSucc 1), (420, Int.ofNat 4), (432, Int.ofNat 2), (705, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (92, Int.ofNat 2), (362,
    Int.negSucc 0), (419, Int.negSucc 3), (453, Int.ofNat 1), (702, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 3), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 1), (327, Int.negSucc 1), (343,
    Int.negSucc 3), (359, Int.ofNat 2), (700, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(75, Int.negSucc 0), (335, Int.negSucc 15), (361,
    Int.ofNat 8), (397, Int.negSucc 3), (402, Int.negSucc 1), (410, Int.ofNat 4), (688,
    Int.negSucc 3), (701, Int.negSucc 15), (722, Int.negSucc 11), (725, Int.negSucc 11), (815,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(453, Int.ofNat 2), (702, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(105, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(54, Int.negSucc 0), (327, Int.negSucc 0), (343,
    Int.negSucc 1), (365, Int.ofNat 1), (697, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(77, Int.negSucc 0), (342, Int.negSucc 7), (366,
    Int.ofNat 4), (401, Int.negSucc 0), (405, Int.negSucc 1), (409, Int.ofNat 2), (685,
    Int.negSucc 1), (698, Int.negSucc 7), (733, Int.negSucc 5), (736, Int.negSucc 5), (814,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(452, Int.ofNat 1), (699, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (380, Int.negSucc 15), (390,
    Int.ofNat 16), (421, Int.negSucc 15), (464, Int.negSucc 7), (475, Int.ofNat 16), (708,
    Int.negSucc 3), (765, Int.ofNat 12), (822, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 2), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 2), (366, Int.ofNat 2), (381, Int.ofNat
    4), (405, Int.negSucc 0), (685, Int.ofNat 4), (698, Int.ofNat 4), (736, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (357, Int.negSucc 15), (384,
    Int.ofNat 16), (416, Int.ofNat 8), (427, Int.negSucc 3), (435, Int.negSucc 5), (440, Int.ofNat
    4), (693, Int.ofNat 12), (737, Int.ofNat 4), (751, Int.negSucc 11), (819, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(479, Int.ofNat 4), (707, Int.negSucc 3), (738,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 19), (390, Int.ofNat 16), (421,
    Int.negSucc 19), (464, Int.negSucc 7), (475, Int.ofNat 16), (487, Int.ofNat 4), (708,
    Int.negSucc 3), (765, Int.ofNat 12), (822, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.ofNat 32), (429, Int.negSucc 39), (468,
    Int.negSucc 15), (482, Int.ofNat 16), (490, Int.ofNat 16), (695, Int.ofNat 48), (745,
    Int.negSucc 23), (752, Int.negSucc 23), (759, Int.ofNat 24), (823, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(69, Int.ofNat 4), (335, Int.ofNat 4), (361, Int.ofNat
    4), (376, Int.ofNat 4), (387, Int.ofNat 4), (397, Int.negSucc 0), (410, Int.negSucc 3), (688,
    Int.ofNat 8), (701, Int.ofNat 8), (725, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (85, Int.negSucc 1), (352,
    Int.negSucc 31), (379, Int.ofNat 36), (413, Int.ofNat 16), (423, Int.negSucc 13), (428,
    Int.negSucc 7), (446, Int.ofNat 4), (694, Int.ofNat 24), (726, Int.ofNat 4), (744, Int.negSucc
    23), (821, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 9), (390, Int.ofNat 8), (421,
    Int.negSucc 9), (464, Int.negSucc 3), (475, Int.ofNat 8), (487, Int.ofNat 2), (494, Int.ofNat
    2), (708, Int.negSucc 3), (727, Int.ofNat 2), (765, Int.ofNat 6), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(385, Int.negSucc 9), (396, Int.ofNat 8), (433,
    Int.negSucc 9), (471, Int.negSucc 3), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    8), (707, Int.negSucc 3), (738, Int.ofNat 2), (773, Int.ofNat 6), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 15), (396, Int.ofNat 16), (433, Int.negSucc 15), (471,
    Int.negSucc 7), (497, Int.ofNat 16), (707, Int.negSucc 3), (773, Int.ofNat 12), (820,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(64, Int.negSucc 1), (328, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (366, Int.negSucc 1), (401,
    Int.ofNat 2), (405, Int.ofNat 1), (685, Int.negSucc 3), (698, Int.negSucc 3), (733,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 1), (372, Int.negSucc 15), (403,
    Int.ofNat 8), (426, Int.ofNat 4), (439, Int.negSucc 3), (449, Int.negSucc 3), (456,
    Int.negSucc 2), (692, Int.negSucc 11), (734, Int.negSucc 3), (758, Int.negSucc 11), (816,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(478, Int.negSucc 1), (706, Int.ofNat 2), (735,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(68, Int.negSucc 1), (323, Int.negSucc 1), (346,
    Int.negSucc 3), (373, Int.negSucc 0), (377, Int.ofNat 2), (388, Int.ofNat 2), (394, Int.ofNat
    2), (691, Int.ofNat 4), (704, Int.ofNat 4), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (95, Int.negSucc 1), (352,
    Int.negSucc 31), (379, Int.ofNat 36), (413, Int.ofNat 14), (423, Int.negSucc 15), (428,
    Int.negSucc 7), (461, Int.ofNat 4), (694, Int.ofNat 24), (715, Int.negSucc 3), (744,
    Int.negSucc 23), (821, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 9), (390, Int.ofNat 8), (421,
    Int.negSucc 9), (464, Int.negSucc 3), (475, Int.ofNat 8), (487, Int.ofNat 2), (509, Int.ofNat
    1), (708, Int.negSucc 3), (716, Int.negSucc 1), (765, Int.ofNat 6), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 4), (412, Int.ofNat 8), (454,
    Int.negSucc 4), (478, Int.negSucc 1), (485, Int.negSucc 1), (504, Int.ofNat 2), (512,
    Int.ofNat 4), (706, Int.ofNat 4), (735, Int.negSucc 1), (780, Int.ofNat 6), (817, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (323,
    Int.negSucc 9), (346, Int.ofNat 4), (373, Int.ofNat 3), (377, Int.negSucc 1), (383, Int.ofNat
    2), (388, Int.ofNat 4), (394, Int.ofNat 2), (691, Int.ofNat 6), (704, Int.ofNat 12), (711,
    Int.negSucc 7), (714, Int.negSucc 5), (818, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(81, Int.negSucc 0), (86, Int.ofNat 2), (98, Int.negSucc
    3), (357, Int.negSucc 47), (384, Int.ofNat 52), (416, Int.ofNat 22), (427, Int.negSucc 11),
    (435, Int.negSucc 21), (440, Int.ofNat 4), (460, Int.ofNat 4), (693, Int.ofNat 36), (712,
    Int.negSucc 3), (737, Int.ofNat 4), (751, Int.negSucc 35), (819, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 9), (396, Int.ofNat 8), (433,
    Int.negSucc 9), (471, Int.negSucc 3), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    8), (508, Int.ofNat 1), (707, Int.negSucc 5), (713, Int.negSucc 1), (738, Int.ofNat 2), (773,
    Int.ofNat 6), (820, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

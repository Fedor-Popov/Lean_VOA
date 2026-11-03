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
def actionData153 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(417, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(61, Int.negSucc 1), (323, Int.negSucc 3), (373,
    Int.ofNat 1), (377, Int.ofNat 2), (383, Int.negSucc 1), (394, Int.ofNat 2), (691, Int.ofNat
    2), (704, Int.ofNat 2), (711, Int.negSucc 1), (714, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(374, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(377, Int.negSucc 0), (388, Int.ofNat 1), (714,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 1), (389, Int.ofNat 2), (428, Int.negSucc
    1), (715, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (380, Int.negSucc 7), (390,
    Int.ofNat 8), (421, Int.negSucc 3), (464, Int.negSucc 1), (475, Int.ofNat 8), (716, Int.ofNat
    4), (765, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (342, Int.negSucc 7), (405,
    Int.negSucc 0), (438, Int.ofNat 4), (733, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (384, Int.ofNat 4), (435, Int.negSucc
    1), (693, Int.ofNat 4), (737, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(479, Int.ofNat 2), (707, Int.negSucc 1), (738,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(388, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (352, Int.negSucc 3), (379, Int.ofNat
    8), (389, Int.ofNat 4), (413, Int.ofNat 2), (423, Int.negSucc 3), (428, Int.negSucc 3), (694,
    Int.ofNat 4), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 3), (390, Int.ofNat 4), (421,
    Int.negSucc 3), (464, Int.negSucc 0), (475, Int.ofNat 4), (487, Int.ofNat 2), (708,
    Int.negSucc 1), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.ofNat 8), (429, Int.negSucc 7), (468,
    Int.negSucc 1), (482, Int.ofNat 4), (490, Int.ofNat 4), (695, Int.ofNat 8), (745, Int.negSucc
    3), (752, Int.negSucc 3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(84, Int.ofNat 1), (374, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(375, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(66, Int.ofNat 2), (69, Int.negSucc 3), (335,
    Int.negSucc 7), (397, Int.negSucc 0), (410, Int.negSucc 3), (444, Int.ofNat 4), (688,
    Int.ofNat 4), (701, Int.ofNat 4), (722, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(85, Int.ofNat 1), (352, Int.negSucc 1), (379, Int.ofNat
    6), (389, Int.ofNat 2), (413, Int.ofNat 1), (423, Int.negSucc 2), (428, Int.negSucc 1), (694,
    Int.ofNat 4), (726, Int.ofNat 2), (744, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(380, Int.negSucc 3), (390, Int.ofNat 4), (421,
    Int.negSucc 3), (464, Int.negSucc 0), (475, Int.ofNat 4), (487, Int.ofNat 2), (494, Int.ofNat
    2), (708, Int.negSucc 3), (727, Int.ofNat 2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(394, Int.ofNat 1), (691, Int.ofNat 1), (704, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(86, Int.ofNat 1), (357, Int.negSucc 1), (384, Int.ofNat
    6), (395, Int.ofNat 2), (416, Int.ofNat 1), (427, Int.negSucc 1), (435, Int.negSucc 2), (693,
    Int.ofNat 4), (737, Int.ofNat 2), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 3), (396, Int.ofNat 4), (433,
    Int.negSucc 3), (471, Int.negSucc 0), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (707, Int.negSucc 3), (738, Int.ofNat 2), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(383, Int.negSucc 0), (394, Int.ofNat 1), (711,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(87, Int.ofNat 1), (395, Int.ofNat 2), (427, Int.negSucc
    1), (712, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 7), (396, Int.ofNat 8), (433, Int.negSucc 3), (471,
    Int.negSucc 1), (497, Int.ofNat 8), (713, Int.ofNat 4), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(109, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 1), (110, Int.negSucc 0), (380,
    Int.negSucc 5), (390, Int.ofNat 6), (421, Int.negSucc 1), (464, Int.negSucc 0), (475,
    Int.ofNat 6), (494, Int.ofNat 2), (708, Int.negSucc 1), (716, Int.ofNat 2), (765, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 1), (385,
    Int.negSucc 3), (396, Int.ofNat 4), (479, Int.ofNat 12), (497, Int.ofNat 4), (707, Int.negSucc
    11), (738, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(377, Int.ofNat 4), (691, Int.ofNat 4), (704, Int.ofNat
    4), (714, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 7), (379, Int.ofNat 8), (413,
    Int.ofNat 2), (423, Int.negSucc 3), (428, Int.negSucc 3), (461, Int.ofNat 4), (694, Int.ofNat
    4), (715, Int.negSucc 3), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(509, Int.ofNat 2), (708, Int.negSucc 3), (716,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 3), (412, Int.ofNat 8), (454,
    Int.negSucc 3), (504, Int.ofNat 2), (512, Int.ofNat 4), (706, Int.ofNat 4), (780, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(383, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat
    2), (711, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 3), (384, Int.ofNat 4), (416,
    Int.ofNat 1), (427, Int.negSucc 1), (435, Int.negSucc 1), (460, Int.ofNat 2), (693, Int.ofNat
    2), (712, Int.negSucc 1), (751, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(508, Int.ofNat 1), (707, Int.negSucc 1), (713,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(465, Int.ofNat 1), (719, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 1), (347, Int.negSucc 3), (420,
    Int.ofNat 2), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(375, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 1), (357, Int.negSucc 7), (416,
    Int.ofNat 2), (427, Int.negSucc 3), (440, Int.ofNat 4), (751, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 2), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (85, Int.negSucc 3), (352,
    Int.negSucc 11), (389, Int.negSucc 3), (413, Int.ofNat 2), (428, Int.negSucc 3), (446,
    Int.ofNat 4), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 1), (465, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 1), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(472, Int.ofNat 1), (718, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(420, Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (380,
    Int.ofNat 8), (390, Int.negSucc 3), (421, Int.ofNat 12), (464, Int.ofNat 2), (475, Int.negSucc
    7), (487, Int.negSucc 3), (708, Int.ofNat 4), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(427, Int.negSucc 1), (440, Int.ofNat 2), (693,
    Int.negSucc 1), (712, Int.ofNat 2), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 1), (441, Int.ofNat 4), (490,
    Int.negSucc 1), (695, Int.negSucc 3), (752, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (430, Int.negSucc 15), (442,
    Int.ofNat 16), (480, Int.negSucc 7), (516, Int.negSucc 3), (528, Int.ofNat 16), (717,
    Int.negSucc 7), (753, Int.ofNat 8), (766, Int.negSucc 7), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.ofNat 3), (740, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(540, Int.ofNat 2), (719, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 0), (476, Int.negSucc 1), (544,
    Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (430, Int.negSucc 31), (442,
    Int.ofNat 16), (443, Int.ofNat 16), (480, Int.negSucc 23), (488, Int.negSucc 15), (516,
    Int.negSucc 3), (520, Int.negSucc 3), (528, Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat
    16), (696, Int.ofNat 16), (709, Int.ofNat 16), (717, Int.negSucc 7), (746, Int.negSucc 7),
    (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 8), (787,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(374, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(116, Int.ofNat 1), (417, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(539, Int.ofNat 1), (718, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    4), (389, Int.ofNat 8), (428, Int.negSucc 7), (446, Int.ofNat 4), (694, Int.negSucc 3), (715,
    Int.ofNat 8), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 1), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (391, Int.negSucc 7), (429, Int.ofNat 8), (441, Int.ofNat 4), (447, Int.ofNat
    4), (468, Int.ofNat 2), (482, Int.negSucc 5), (490, Int.negSucc 5), (695, Int.negSucc 15),
    (745, Int.ofNat 8), (752, Int.ofNat 8), (759, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 47), (442, Int.ofNat 16), (443,
    Int.ofNat 16), (448, Int.ofNat 16), (480, Int.negSucc 23), (488, Int.negSucc 15), (495,
    Int.negSucc 7), (516, Int.negSucc 3), (520, Int.negSucc 3), (524, Int.negSucc 3), (528,
    Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat 16), (550, Int.ofNat 16), (696, Int.ofNat
    16), (709, Int.ofNat 16), (717, Int.negSucc 15), (760, Int.ofNat 8), (766, Int.negSucc 15),
    (774, Int.negSucc 15), (781, Int.ofNat 8), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(432, Int.ofNat 2), (705, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(118, Int.ofNat 1), (385, Int.ofNat 10), (396,
    Int.negSucc 3), (433, Int.ofNat 14), (471, Int.ofNat 2), (479, Int.negSucc 1), (486,
    Int.negSucc 3), (497, Int.negSucc 9), (707, Int.ofNat 6), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 3), (434, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(137, Int.ofNat 1), (141, Int.negSucc 0), (415,
    Int.ofNat 1), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(142, Int.negSucc 0), (149, Int.ofNat 1), (418,
    Int.ofNat 1), (472, Int.ofNat 1), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 2), (150, Int.ofNat 4), (430, Int.negSucc 55), (442,
    Int.ofNat 40), (443, Int.ofNat 8), (448, Int.ofNat 8), (480, Int.negSucc 23), (488,
    Int.negSucc 7), (516, Int.negSucc 7), (520, Int.negSucc 3), (528, Int.ofNat 40), (535,
    Int.ofNat 4), (547, Int.ofNat 8), (550, Int.ofNat 8), (709, Int.ofNat 8), (717, Int.negSucc
    23), (753, Int.ofNat 16), (766, Int.negSucc 23), (774, Int.negSucc 7), (781, Int.ofNat 8),
    (787, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(430, Int.negSucc 7), (463, Int.ofNat 8), (510,
    Int.negSucc 3), (556, Int.ofNat 2), (560, Int.ofNat 4), (709, Int.ofNat 4), (717, Int.ofNat
    4), (781, Int.ofNat 4), (802, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(466, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(517, Int.ofNat 2), (720, Int.negSucc 3), (755,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 3), (390, Int.negSucc 3), (421, Int.ofNat 4), (464, Int.ofNat 2), (487,
    Int.negSucc 3), (494, Int.ofNat 4), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 0), (465, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 4), (118, Int.ofNat 1), (396,
    Int.negSucc 3), (433, Int.ofNat 4), (471, Int.ofNat 2), (479, Int.ofNat 4), (486, Int.negSucc
    3), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.negSucc 0), (472, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(470, Int.ofNat 2), (517, Int.ofNat 2), (521, Int.ofNat
    2), (720, Int.negSucc 3), (755, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(470, Int.ofNat 1), (517, Int.ofNat 1), (521, Int.ofNat
    1), (525, Int.ofNat 1), (720, Int.negSucc 3), (748, Int.ofNat 2), (755, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(473, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(137, Int.ofNat 1), (415, Int.ofNat 1), (465, Int.ofNat
    1), (540, Int.negSucc 1), (719, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (396,
    Int.ofNat 4), (433, Int.ofNat 4), (479, Int.ofNat 4), (486, Int.negSucc 3), (713, Int.ofNat
    4), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (148,
    Int.negSucc 0), (430, Int.ofNat 16), (442, Int.negSucc 7), (443, Int.negSucc 7), (480,
    Int.ofNat 24), (516, Int.ofNat 4), (528, Int.negSucc 15), (547, Int.negSucc 7), (696,
    Int.negSucc 7), (709, Int.negSucc 7), (717, Int.ofNat 8), (766, Int.ofNat 8), (774, Int.ofNat
    8), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 4), (172, Int.ofNat 3), (481,
    Int.negSucc 23), (489, Int.negSucc 15), (500, Int.ofNat 28), (564, Int.negSucc 3), (578,
    Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 12), (767, Int.negSucc 7), (782, Int.ofNat
    8)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 1), (492, Int.negSucc 11), (501,
    Int.ofNat 12), (567, Int.negSucc 2), (581, Int.ofNat 12), (754, Int.negSucc 11), (788,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.negSucc 0), (180, Int.negSucc 1), (192,
    Int.ofNat 1), (470, Int.negSucc 9), (502, Int.ofNat 8), (517, Int.negSucc 1), (521,
    Int.negSucc 3), (541, Int.negSucc 3), (585, Int.ofNat 4), (590, Int.ofNat 8), (755, Int.ofNat
    4), (803, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData407 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(377, Int.negSucc 0), (388, Int.ofNat 1), (714,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 1), (389, Int.ofNat 2), (428, Int.negSucc
    1), (715, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (380, Int.negSucc 15), (390,
    Int.ofNat 16), (421, Int.negSucc 11), (464, Int.negSucc 5), (475, Int.ofNat 16), (716,
    Int.ofNat 4), (765, Int.ofNat 12), (822, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 1), (342, Int.negSucc 15), (366,
    Int.ofNat 4), (405, Int.negSucc 2), (438, Int.ofNat 4), (698, Int.negSucc 7), (733,
    Int.negSucc 11), (736, Int.negSucc 7), (814, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (384, Int.ofNat 4), (435, Int.negSucc
    1), (693, Int.ofNat 4), (737, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(479, Int.ofNat 2), (707, Int.negSucc 1), (738,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(388, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (352, Int.negSucc 11), (379,
    Int.ofNat 16), (389, Int.ofNat 4), (413, Int.ofNat 6), (423, Int.negSucc 7), (428, Int.negSucc
    3), (694, Int.ofNat 12), (744, Int.negSucc 11), (821, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 7), (390, Int.ofNat 8), (421,
    Int.negSucc 7), (464, Int.negSucc 2), (475, Int.ofNat 8), (487, Int.ofNat 2), (708,
    Int.negSucc 1), (765, Int.ofNat 6), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(391, Int.ofNat 16), (429, Int.negSucc 15), (468,
    Int.negSucc 5), (482, Int.ofNat 8), (490, Int.ofNat 8), (695, Int.ofNat 24), (745, Int.negSucc
    11), (752, Int.negSucc 11), (759, Int.ofNat 12), (823, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(84, Int.ofNat 1), (374, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(375, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(66, Int.ofNat 2), (69, Int.negSucc 3), (335,
    Int.negSucc 15), (361, Int.ofNat 4), (397, Int.negSucc 2), (410, Int.negSucc 3), (444,
    Int.ofNat 4), (688, Int.ofNat 4), (701, Int.negSucc 3), (722, Int.negSucc 11), (725,
    Int.negSucc 7), (815, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(56, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(85, Int.ofNat 1), (352, Int.negSucc 5), (379, Int.ofNat
    10), (389, Int.ofNat 2), (413, Int.ofNat 3), (423, Int.negSucc 4), (428, Int.negSucc 1), (694,
    Int.ofNat 8), (726, Int.ofNat 2), (744, Int.negSucc 5), (821, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(380, Int.negSucc 7), (390, Int.ofNat 8), (421,
    Int.negSucc 7), (464, Int.negSucc 2), (475, Int.ofNat 8), (487, Int.ofNat 2), (494, Int.ofNat
    2), (708, Int.negSucc 3), (727, Int.ofNat 2), (765, Int.ofNat 6), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(394, Int.ofNat 1), (691, Int.ofNat 1), (704, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(86, Int.ofNat 1), (357, Int.negSucc 5), (384, Int.ofNat
    10), (395, Int.ofNat 2), (416, Int.ofNat 3), (427, Int.negSucc 1), (435, Int.negSucc 4), (693,
    Int.ofNat 8), (737, Int.ofNat 2), (751, Int.negSucc 5), (819, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 7), (396, Int.ofNat 8), (433,
    Int.negSucc 7), (471, Int.negSucc 2), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    8), (707, Int.negSucc 3), (738, Int.ofNat 2), (773, Int.ofNat 6), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(383, Int.negSucc 0), (394, Int.ofNat 1), (711,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(87, Int.ofNat 1), (395, Int.ofNat 2), (427, Int.negSucc
    1), (712, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 15), (396, Int.ofNat 16), (433, Int.negSucc 11), (471,
    Int.negSucc 5), (497, Int.ofNat 16), (713, Int.ofNat 4), (773, Int.ofNat 12), (820,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(109, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 1), (110, Int.negSucc 0), (380,
    Int.negSucc 9), (390, Int.ofNat 10), (421, Int.negSucc 5), (464, Int.negSucc 2), (475,
    Int.ofNat 10), (494, Int.ofNat 2), (708, Int.negSucc 1), (716, Int.ofNat 2), (765, Int.ofNat
    6), (822, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 1), (385,
    Int.negSucc 3), (396, Int.ofNat 4), (479, Int.ofNat 12), (497, Int.ofNat 4), (707, Int.negSucc
    11), (738, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(377, Int.ofNat 4), (691, Int.ofNat 4), (704, Int.ofNat
    4), (714, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(352, Int.negSucc 15), (379, Int.ofNat 16), (413,
    Int.ofNat 6), (423, Int.negSucc 7), (428, Int.negSucc 3), (461, Int.ofNat 4), (694, Int.ofNat
    12), (715, Int.negSucc 3), (744, Int.negSucc 11), (821, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(509, Int.ofNat 2), (708, Int.negSucc 3), (716,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 7), (412, Int.ofNat 16), (454,
    Int.negSucc 7), (504, Int.ofNat 4), (512, Int.ofNat 8), (706, Int.ofNat 4), (780, Int.ofNat
    12), (817, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(383, Int.ofNat 2), (691, Int.ofNat 2), (704, Int.ofNat
    2), (711, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(357, Int.negSucc 7), (384, Int.ofNat 8), (416,
    Int.ofNat 3), (427, Int.negSucc 1), (435, Int.negSucc 3), (460, Int.ofNat 2), (693, Int.ofNat
    6), (712, Int.negSucc 1), (751, Int.negSucc 5), (819, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(508, Int.ofNat 1), (707, Int.negSucc 1), (713,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(465, Int.ofNat 1), (719, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 1), (347, Int.negSucc 3), (420,
    Int.ofNat 2), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(375, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 1), (357, Int.negSucc 15), (384,
    Int.ofNat 8), (416, Int.ofNat 6), (427, Int.negSucc 3), (435, Int.negSucc 3), (440, Int.ofNat
    4), (693, Int.ofNat 8), (751, Int.negSucc 11), (819, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(417, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 2), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(82, Int.ofNat 1), (85, Int.negSucc 3), (352,
    Int.negSucc 19), (379, Int.ofNat 8), (389, Int.negSucc 3), (413, Int.ofNat 6), (423,
    Int.negSucc 3), (428, Int.negSucc 3), (446, Int.ofNat 4), (694, Int.ofNat 8), (744,
    Int.negSucc 11), (821, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 1), (465, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 1), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(472, Int.ofNat 1), (718, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(420, Int.ofNat 1), (705, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (380,
    Int.ofNat 16), (390, Int.negSucc 11), (421, Int.ofNat 20), (464, Int.ofNat 6), (475,
    Int.negSucc 15), (487, Int.negSucc 3), (708, Int.ofNat 4), (765, Int.negSucc 11), (822,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(427, Int.negSucc 1), (440, Int.ofNat 2), (693,
    Int.negSucc 1), (712, Int.ofNat 2), (751, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 1), (441, Int.ofNat 4), (490,
    Int.negSucc 1), (695, Int.negSucc 3), (752, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (430, Int.negSucc 31), (442,
    Int.ofNat 32), (480, Int.negSucc 23), (516, Int.negSucc 11), (528, Int.ofNat 32), (717,
    Int.negSucc 7), (753, Int.ofNat 8), (766, Int.negSucc 23), (787, Int.ofNat 24), (824,
    Int.ofNat 16), (826, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.ofNat 3), (740, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(113, Int.ofNat 1), (414, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(540, Int.ofNat 2), (719, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 0), (476, Int.negSucc 1), (544,
    Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (430, Int.negSucc 63), (442,
    Int.ofNat 32), (443, Int.ofNat 32), (480, Int.negSucc 55), (488, Int.negSucc 31), (516,
    Int.negSucc 11), (520, Int.negSucc 11), (528, Int.ofNat 32), (535, Int.ofNat 16), (547,
    Int.ofNat 32), (696, Int.ofNat 40), (709, Int.ofNat 32), (717, Int.negSucc 7), (746,
    Int.negSucc 23), (753, Int.negSucc 15), (760, Int.ofNat 24), (766, Int.negSucc 47), (774,
    Int.negSucc 23), (781, Int.ofNat 24), (787, Int.ofNat 24), (824, Int.ofNat 32), (826,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 2, terms := [(374, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(116, Int.ofNat 1), (417, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(539, Int.ofNat 1), (718, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.ofNat 2), (82, Int.ofNat 1), (352, Int.ofNat
    4), (389, Int.ofNat 8), (428, Int.negSucc 7), (446, Int.ofNat 4), (694, Int.negSucc 3), (715,
    Int.ofNat 8), (744, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.ofNat 1), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (391, Int.negSucc 15), (429, Int.ofNat 16), (441, Int.ofNat 4), (447, Int.ofNat
    4), (468, Int.ofNat 6), (482, Int.negSucc 9), (490, Int.negSucc 9), (695, Int.negSucc 31),
    (745, Int.ofNat 16), (752, Int.ofNat 16), (759, Int.negSucc 11), (823, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 95), (442, Int.ofNat 32), (443,
    Int.ofNat 32), (448, Int.ofNat 32), (480, Int.negSucc 55), (488, Int.negSucc 31), (495,
    Int.negSucc 23), (516, Int.negSucc 11), (520, Int.negSucc 11), (524, Int.negSucc 11), (528,
    Int.ofNat 32), (535, Int.ofNat 16), (547, Int.ofNat 32), (550, Int.ofNat 32), (696, Int.ofNat
    40), (709, Int.ofNat 32), (717, Int.negSucc 15), (746, Int.negSucc 15), (753, Int.negSucc 15),
    (760, Int.ofNat 24), (766, Int.negSucc 47), (774, Int.negSucc 47), (781, Int.ofNat 24), (787,
    Int.ofNat 24), (795, Int.ofNat 24), (824, Int.ofNat 48), (826, Int.negSucc 15), (829,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(432, Int.ofNat 2), (705, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(118, Int.ofNat 1), (385, Int.ofNat 18), (396,
    Int.negSucc 11), (433, Int.ofNat 22), (471, Int.ofNat 6), (479, Int.negSucc 1), (486,
    Int.negSucc 3), (497, Int.negSucc 17), (707, Int.ofNat 6), (773, Int.negSucc 11), (820,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 3), (434, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(137, Int.ofNat 1), (141, Int.negSucc 0), (415,
    Int.ofNat 1), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(142, Int.negSucc 0), (149, Int.ofNat 1), (418,
    Int.ofNat 1), (472, Int.ofNat 1), (718, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 3), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 2), (150, Int.ofNat 4), (430, Int.negSucc 103), (442,
    Int.ofNat 72), (443, Int.ofNat 24), (448, Int.ofNat 8), (480, Int.negSucc 71), (488,
    Int.negSucc 23), (516, Int.negSucc 23), (520, Int.negSucc 11), (528, Int.ofNat 72), (535,
    Int.ofNat 12), (547, Int.ofNat 24), (550, Int.ofNat 8), (696, Int.ofNat 16), (709, Int.ofNat
    24), (717, Int.negSucc 23), (746, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 71),
    (774, Int.negSucc 23), (781, Int.ofNat 24), (787, Int.ofNat 48), (824, Int.ofNat 64), (826,
    Int.negSucc 39), (829, Int.negSucc 7), (832, Int.negSucc 15), (840, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(430, Int.negSucc 15), (463, Int.ofNat 16), (510,
    Int.negSucc 7), (556, Int.ofNat 4), (560, Int.ofNat 8), (709, Int.ofNat 4), (717, Int.ofNat
    4), (781, Int.ofNat 12), (802, Int.ofNat 12), (824, Int.ofNat 8), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(466, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(517, Int.ofNat 2), (720, Int.negSucc 3), (755,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 3), (380, Int.ofNat 8), (390, Int.negSucc 11), (421, Int.ofNat 12), (464,
    Int.ofNat 6), (475, Int.negSucc 7), (487, Int.negSucc 3), (494, Int.ofNat 4), (765,
    Int.negSucc 11), (822, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 0), (465, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 4), (118, Int.ofNat 1), (385,
    Int.ofNat 8), (396, Int.negSucc 11), (433, Int.ofNat 12), (471, Int.ofNat 6), (479, Int.ofNat
    4), (486, Int.negSucc 3), (497, Int.negSucc 7), (773, Int.negSucc 11), (820, Int.ofNat 8)] },
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
    Int.negSucc 0), (430, Int.ofNat 32), (442, Int.negSucc 23), (443, Int.negSucc 7), (480,
    Int.ofNat 40), (516, Int.ofNat 12), (528, Int.negSucc 31), (547, Int.negSucc 7), (696,
    Int.negSucc 7), (709, Int.negSucc 7), (717, Int.ofNat 8), (766, Int.ofNat 24), (774, Int.ofNat
    8), (787, Int.negSucc 23), (824, Int.negSucc 15), (826, Int.ofNat 16)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData158 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 0), (476, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(451, Int.negSucc 0), (505, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (352,
    Int.negSucc 3), (389, Int.negSucc 7), (428, Int.ofNat 8), (461, Int.negSucc 3), (694,
    Int.ofNat 4), (726, Int.ofNat 8), (744, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (128,
    Int.negSucc 1), (391, Int.ofNat 8), (429, Int.negSucc 7), (441, Int.negSucc 3), (462,
    Int.negSucc 3), (468, Int.negSucc 5), (482, Int.ofNat 2), (490, Int.ofNat 6), (695, Int.ofNat
    16), (745, Int.negSucc 7), (752, Int.negSucc 3), (759, Int.ofNat 8)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 1), (148, Int.negSucc 0), (160,
    Int.ofNat 2), (164, Int.negSucc 0), (430, Int.ofNat 48), (442, Int.negSucc 15), (443,
    Int.negSucc 15), (463, Int.negSucc 15), (480, Int.ofNat 24), (488, Int.ofNat 16), (510,
    Int.ofNat 4), (516, Int.ofNat 8), (520, Int.ofNat 8), (528, Int.negSucc 7), (535, Int.negSucc
    3), (547, Int.negSucc 15), (556, Int.negSucc 1), (560, Int.negSucc 7), (696, Int.negSucc 15),
    (709, Int.negSucc 15), (729, Int.negSucc 15), (753, Int.ofNat 8), (766, Int.ofNat 16), (774,
    Int.ofNat 8), (781, Int.negSucc 15), (787, Int.negSucc 7), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(398, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(129, Int.negSucc 0), (450, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(543, Int.ofNat 1), (728, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(453, Int.negSucc 0), (702, Int.ofNat 3)] },
  { denominator := Int.ofNat 2, terms := [(130, Int.negSucc 0), (404, Int.negSucc 4), (412,
    Int.ofNat 4), (454, Int.negSucc 6), (478, Int.negSucc 1), (485, Int.negSucc 3), (504,
    Int.ofNat 1), (512, Int.ofNat 5), (706, Int.ofNat 6), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.negSucc 2), (455, Int.negSucc 2)] },
  { denominator := Int.ofNat 2, terms := [(138, Int.negSucc 0), (152, Int.ofNat 2), (425,
    Int.negSucc 0), (476, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 2), (139, Int.negSucc 5), (148,
    Int.ofNat 3), (153, Int.ofNat 8), (160, Int.negSucc 3), (430, Int.ofNat 56), (442, Int.negSucc
    39), (443, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 8),
    (516, Int.ofNat 20), (520, Int.ofNat 4), (528, Int.negSucc 15), (535, Int.negSucc 3), (547,
    Int.negSucc 7), (560, Int.negSucc 3), (709, Int.negSucc 7), (729, Int.negSucc 23), (760,
    Int.ofNat 16), (766, Int.ofNat 24), (774, Int.ofNat 8), (781, Int.negSucc 7), (787,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(154, Int.ofNat 4), (161, Int.negSucc 1), (451,
    Int.negSucc 0), (505, Int.negSucc 0), (728, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(505, Int.negSucc 0), (728, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(477, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(529, Int.negSucc 3), (731, Int.ofNat 4), (762,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (425, Int.negSucc 0), (476,
    Int.negSucc 1), (544, Int.ofNat 2), (730, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.negSucc 0), (477, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 1), (130, Int.ofNat 1), (412,
    Int.ofNat 4), (454, Int.ofNat 2), (478, Int.negSucc 3), (485, Int.ofNat 4), (724, Int.ofNat
    4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 3), (139, Int.negSucc 5), (148,
    Int.ofNat 1), (430, Int.negSucc 15), (442, Int.ofNat 8), (443, Int.ofNat 8), (480, Int.negSucc
    23), (516, Int.negSucc 7), (528, Int.ofNat 8), (547, Int.ofNat 8), (696, Int.ofNat 8), (709,
    Int.ofNat 8), (729, Int.ofNat 8), (766, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat
    8)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 5), (172, Int.negSucc 2), (481,
    Int.ofNat 24), (489, Int.ofNat 16), (500, Int.negSucc 27), (564, Int.ofNat 8), (578,
    Int.negSucc 7), (596, Int.negSucc 3), (710, Int.negSucc 11), (767, Int.ofNat 8), (775,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 0), (492, Int.ofNat 12), (501,
    Int.negSucc 11), (567, Int.ofNat 6), (581, Int.negSucc 5), (761, Int.negSucc 11), (788,
    Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(484, Int.negSucc 1), (529, Int.negSucc 3), (536,
    Int.negSucc 1), (731, Int.ofNat 4), (762, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (180, Int.ofNat 2), (192,
    Int.negSucc 0), (470, Int.ofNat 5), (502, Int.negSucc 3), (517, Int.ofNat 2), (521, Int.ofNat
    3), (585, Int.negSucc 0), (590, Int.negSucc 3), (748, Int.negSucc 1), (803, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 1), (181, Int.ofNat 2), (183,
    Int.negSucc 0), (484, Int.ofNat 10), (503, Int.negSucc 7), (529, Int.ofNat 4), (536, Int.ofNat
    4), (545, Int.ofNat 4), (573, Int.ofNat 4), (593, Int.negSucc 7), (762, Int.negSucc 3), (796,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 33), (172, Int.negSucc 14), (481,
    Int.ofNat 120), (489, Int.ofNat 48), (500, Int.negSucc 107), (564, Int.ofNat 24), (578,
    Int.negSucc 23), (596, Int.negSucc 19), (710, Int.negSucc 51), (767, Int.ofNat 24), (775,
    Int.ofNat 24), (782, Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (120,
    Int.negSucc 7), (390, Int.negSucc 3), (421, Int.ofNat 4), (475, Int.negSucc 3), (487,
    Int.negSucc 3), (509, Int.ofNat 2), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(425, Int.ofNat 1), (476, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 9), (130, Int.ofNat 1), (412,
    Int.negSucc 3), (454, Int.ofNat 2), (478, Int.negSucc 3), (485, Int.ofNat 4), (504,
    Int.negSucc 0), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(451, Int.ofNat 1), (505, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(484, Int.negSucc 1), (529, Int.negSucc 3), (536,
    Int.negSucc 1), (557, Int.negSucc 0), (731, Int.ofNat 8), (747, Int.ofNat 4), (762,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(506, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 3), (107, Int.negSucc 7), (390,
    Int.negSucc 15), (421, Int.negSucc 19), (487, Int.ofNat 8), (509, Int.negSucc 1), (708,
    Int.negSucc 3), (727, Int.ofNat 8), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(139, Int.negSucc 7), (148, Int.ofNat 5), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 63), (442, Int.ofNat 8), (443, Int.ofNat
    48), (463, Int.ofNat 8), (480, Int.negSucc 55), (488, Int.negSucc 31), (510, Int.negSucc 7),
    (516, Int.negSucc 7), (520, Int.negSucc 19), (528, Int.ofNat 8), (535, Int.ofNat 8), (547,
    Int.ofNat 40), (556, Int.ofNat 2), (560, Int.ofNat 8), (696, Int.ofNat 48), (709, Int.ofNat
    48), (729, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16),
    (766, Int.negSucc 31), (774, Int.negSucc 15), (781, Int.ofNat 32), (787, Int.ofNat 8), (802,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 41), (172, Int.negSucc 16), (185,
    Int.negSucc 7), (481, Int.ofNat 160), (489, Int.ofNat 64), (500, Int.negSucc 139), (511,
    Int.negSucc 3), (564, Int.ofNat 28), (578, Int.negSucc 31), (596, Int.negSucc 27), (710,
    Int.negSucc 63), (767, Int.ofNat 24), (775, Int.ofNat 32), (782, Int.negSucc 23)] },
  { denominator := Int.ofNat 4, terms := [(399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.negSucc 0), (451, Int.ofNat 1), (505,
    Int.ofNat 1), (543, Int.negSucc 1), (728, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(187, Int.negSucc 3), (506, Int.negSucc 2)] },
  { denominator := Int.ofNat 4, terms := [(171, Int.ofNat 1), (181, Int.ofNat 5), (183,
    Int.negSucc 0), (184, Int.ofNat 4), (193, Int.negSucc 1), (484, Int.ofNat 4), (503,
    Int.negSucc 3), (529, Int.negSucc 7), (536, Int.ofNat 4), (557, Int.negSucc 0), (573,
    Int.ofNat 2), (593, Int.negSucc 3), (731, Int.ofNat 8), (762, Int.negSucc 7), (796, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(530, Int.negSucc 1), (579, Int.negSucc 1), (732,
    Int.ofNat 1), (784, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(582, Int.negSucc 5), (763, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 1), (451, Int.ofNat 1), (505, Int.ofNat
    1), (543, Int.ofNat 2), (728, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 1), (181, Int.ofNat 1), (484,
    Int.negSucc 1), (503, Int.ofNat 4), (529, Int.negSucc 3), (593, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.negSucc 0), (203, Int.ofNat 1), (210,
    Int.negSucc 0), (530, Int.ofNat 8), (537, Int.ofNat 6), (546, Int.ofNat 4), (554, Int.negSucc
    7), (579, Int.ofNat 16), (605, Int.ofNat 4), (631, Int.negSucc 3), (732, Int.negSucc 3), (768,
    Int.negSucc 3), (797, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.negSucc 3), (205, Int.ofNat 1), (534,
    Int.ofNat 4), (549, Int.ofNat 16), (555, Int.negSucc 11), (597, Int.ofNat 4), (608, Int.ofNat
    8), (621, Int.negSucc 7), (743, Int.negSucc 7), (776, Int.negSucc 7), (789, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(519, Int.negSucc 0), (586, Int.negSucc 1), (749,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(214, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(530, Int.negSucc 3), (537, Int.negSucc 3), (579,
    Int.negSucc 11), (732, Int.ofNat 2), (784, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(201, Int.ofNat 1), (217, Int.negSucc 1), (518,
    Int.ofNat 4), (522, Int.ofNat 6), (553, Int.negSucc 3), (565, Int.ofNat 7), (618, Int.negSucc
    1), (628, Int.negSucc 3), (721, Int.negSucc 1), (777, Int.ofNat 2), (804, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.ofNat 1), (203, Int.negSucc 0), (210,
    Int.negSucc 0), (530, Int.ofNat 16), (537, Int.ofNat 6), (546, Int.ofNat 4), (554, Int.negSucc
    11), (579, Int.ofNat 16), (605, Int.ofNat 4), (631, Int.negSucc 7), (732, Int.negSucc 3),
    (768, Int.negSucc 3), (797, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (148,
    Int.negSucc 2), (153, Int.negSucc 15), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 16), (442, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 8), (488, Int.ofNat
    16), (520, Int.ofNat 4), (528, Int.negSucc 7), (547, Int.negSucc 7), (556, Int.negSucc 1),
    (696, Int.negSucc 7), (787, Int.negSucc 7), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(484, Int.ofNat 2), (529, Int.ofNat 4), (557, Int.ofNat
    1), (731, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(579, Int.negSucc 1), (732, Int.ofNat 1), (768,
    Int.ofNat 2), (784, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(530, Int.negSucc 3), (537, Int.negSucc 3), (558,
    Int.negSucc 0), (579, Int.negSucc 15), (732, Int.ofNat 4), (768, Int.ofNat 4), (784,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(138, Int.negSucc 3), (425, Int.negSucc 4), (476,
    Int.negSucc 11), (544, Int.ofNat 4), (730, Int.negSucc 5)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 0), (183, Int.ofNat 1), (193,
    Int.negSucc 0), (484, Int.negSucc 11), (503, Int.ofNat 12), (529, Int.negSucc 9), (536,
    Int.negSucc 3), (545, Int.negSucc 3), (573, Int.negSucc 4), (593, Int.ofNat 10), (731,
    Int.ofNat 4), (796, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(196, Int.ofNat 1), (203, Int.ofNat 2), (210,
    Int.negSucc 3), (218, Int.negSucc 3), (530, Int.ofNat 64), (537, Int.ofNat 36), (546,
    Int.ofNat 16), (554, Int.negSucc 39), (558, Int.negSucc 0), (579, Int.ofNat 100), (605,
    Int.ofNat 14), (631, Int.negSucc 27), (732, Int.negSucc 19), (768, Int.negSucc 11), (784,
    Int.ofNat 12), (797, Int.ofNat 16)] }
]

end VOA.DeligneAudit.D4Two.Certificate

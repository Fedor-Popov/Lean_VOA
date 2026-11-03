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
def actionData232 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (180, Int.negSucc 4), (192,
    Int.ofNat 2), (470, Int.negSucc 13), (502, Int.ofNat 4), (517, Int.negSucc 3), (521,
    Int.negSucc 7), (541, Int.negSucc 3), (585, Int.ofNat 4), (590, Int.ofNat 8), (803, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 1), (181, Int.negSucc 4), (183,
    Int.ofNat 2), (484, Int.negSucc 9), (503, Int.ofNat 4), (529, Int.negSucc 7), (536,
    Int.negSucc 3), (545, Int.negSucc 3), (573, Int.negSucc 3), (593, Int.ofNat 8), (796,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (180, Int.negSucc 4), (182,
    Int.ofNat 1), (192, Int.ofNat 2), (470, Int.negSucc 10), (502, Int.ofNat 4), (517, Int.negSucc
    3), (521, Int.negSucc 7), (525, Int.ofNat 1), (541, Int.negSucc 1), (585, Int.ofNat 3), (590,
    Int.ofNat 8), (803, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 8), (181, Int.negSucc 17), (183,
    Int.ofNat 8), (484, Int.negSucc 44), (503, Int.ofNat 24), (529, Int.negSucc 31), (536,
    Int.negSucc 23), (545, Int.negSucc 9), (573, Int.negSucc 15), (593, Int.ofNat 34), (796,
    Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [(184, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 6), (172, Int.ofNat 3), (481,
    Int.negSucc 27), (489, Int.negSucc 11), (500, Int.ofNat 20), (511, Int.negSucc 1), (564,
    Int.negSucc 3), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 8), (767, Int.negSucc
    3), (775, Int.negSucc 3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(186, Int.negSucc 1), (492, Int.negSucc 3), (533,
    Int.negSucc 1), (561, Int.negSucc 1), (567, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(506, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(188, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(514, Int.negSucc 0)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 18), (172, Int.ofNat 7), (177,
    Int.ofNat 4), (185, Int.negSucc 7), (190, Int.ofNat 8), (481, Int.negSucc 71), (489,
    Int.negSucc 23), (496, Int.ofNat 8), (500, Int.ofNat 52), (511, Int.negSucc 3), (564,
    Int.negSucc 11), (578, Int.ofNat 8), (596, Int.ofNat 12), (710, Int.ofNat 16), (767,
    Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(186, Int.negSucc 1), (191, Int.ofNat 1), (492,
    Int.negSucc 1), (533, Int.negSucc 1), (561, Int.negSucc 1), (567, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 4), (180, Int.negSucc 9), (192,
    Int.ofNat 4), (470, Int.negSucc 30), (502, Int.ofNat 8), (517, Int.negSucc 9), (521,
    Int.negSucc 15), (541, Int.negSucc 9), (585, Int.ofNat 8), (590, Int.ofNat 18), (803,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 3), (181, Int.negSucc 7), (183,
    Int.ofNat 4), (193, Int.negSucc 1), (484, Int.negSucc 23), (503, Int.ofNat 8), (529,
    Int.negSucc 15), (536, Int.negSucc 7), (545, Int.negSucc 15), (557, Int.ofNat 1), (573,
    Int.negSucc 9), (593, Int.ofNat 20), (796, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(515, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(518, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(530, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(197, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(534, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(200, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(201, Int.negSucc 0), (217, Int.ofNat 2), (518,
    Int.negSucc 4), (522, Int.negSucc 5), (542, Int.negSucc 1), (553, Int.ofNat 4), (565,
    Int.negSucc 7), (618, Int.ofNat 4), (628, Int.ofNat 4), (721, Int.ofNat 2), (769, Int.negSucc
    1), (777, Int.negSucc 1), (804, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.negSucc 0), (523, Int.negSucc 2), (591,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(203, Int.negSucc 0), (210, Int.ofNat 1), (530,
    Int.negSucc 5), (537, Int.negSucc 3), (546, Int.negSucc 1), (554, Int.ofNat 4), (579,
    Int.negSucc 11), (605, Int.negSucc 1), (631, Int.ofNat 4), (732, Int.ofNat 2), (768, Int.ofNat
    2), (784, Int.negSucc 1), (797, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.negSucc 0), (538, Int.negSucc 0), (582,
    Int.ofNat 4), (594, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.ofNat 3), (205, Int.negSucc 0), (534,
    Int.negSucc 7), (549, Int.negSucc 11), (555, Int.ofNat 4), (597, Int.negSucc 3), (608,
    Int.negSucc 3), (621, Int.ofNat 8), (743, Int.ofNat 4), (776, Int.ofNat 4), (783, Int.negSucc
    3), (789, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(201, Int.negSucc 1), (206, Int.ofNat 1), (208,
    Int.ofNat 1), (217, Int.ofNat 2), (518, Int.negSucc 5), (522, Int.negSucc 7), (526, Int.ofNat
    1), (542, Int.negSucc 1), (553, Int.ofNat 4), (565, Int.negSucc 11), (618, Int.ofNat 2), (628,
    Int.ofNat 6), (721, Int.ofNat 2), (769, Int.negSucc 1), (777, Int.negSucc 1), (804, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.negSucc 1), (207, Int.ofNat 1), (523,
    Int.negSucc 3), (591, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 1), (201, Int.negSucc 3), (208,
    Int.ofNat 2), (217, Int.ofNat 4), (518, Int.negSucc 5), (522, Int.negSucc 11), (526, Int.ofNat
    1), (553, Int.ofNat 4), (565, Int.negSucc 15), (618, Int.ofNat 4), (628, Int.ofNat 8), (721,
    Int.ofNat 4), (769, Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 2), (527, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(203, Int.negSucc 4), (210, Int.ofNat 5), (530,
    Int.negSucc 37), (537, Int.negSucc 25), (546, Int.negSucc 5), (554, Int.ofNat 20), (579,
    Int.negSucc 67), (605, Int.negSucc 9), (631, Int.ofNat 20), (732, Int.ofNat 10), (768,
    Int.ofNat 10), (784, Int.negSucc 9), (797, Int.negSucc 9)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.ofNat 15), (205, Int.negSucc 6), (211,
    Int.ofNat 4), (534, Int.ofNat 4), (549, Int.negSucc 27), (552, Int.ofNat 4), (555, Int.ofNat
    4), (597, Int.negSucc 11), (608, Int.negSucc 11), (621, Int.ofNat 16), (743, Int.ofNat 12),
    (776, Int.ofNat 12), (783, Int.negSucc 11), (789, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(213, Int.negSucc 0), (574, Int.negSucc 1), (586,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(214, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(196, Int.ofNat 2), (203, Int.negSucc 5), (210,
    Int.ofNat 2), (215, Int.negSucc 3), (218, Int.ofNat 4), (537, Int.negSucc 7), (546, Int.ofNat
    4), (558, Int.ofNat 1), (579, Int.negSucc 15), (605, Int.negSucc 1), (631, Int.ofNat 4), (732,
    Int.ofNat 4), (768, Int.ofNat 4), (784, Int.negSucc 3), (797, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(216, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(201, Int.negSucc 0), (217, Int.ofNat 2), (518,
    Int.negSucc 4), (522, Int.negSucc 3), (542, Int.negSucc 5), (553, Int.ofNat 4), (565,
    Int.negSucc 7), (618, Int.ofNat 4), (628, Int.ofNat 4), (721, Int.ofNat 2), (769, Int.negSucc
    1), (777, Int.negSucc 1), (804, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(203, Int.negSucc 1), (210, Int.ofNat 2), (530,
    Int.negSucc 11), (537, Int.negSucc 7), (546, Int.negSucc 3), (554, Int.ofNat 8), (558,
    Int.ofNat 1), (579, Int.negSucc 23), (605, Int.negSucc 3), (631, Int.ofNat 8), (732, Int.ofNat
    4), (768, Int.ofNat 4), (784, Int.negSucc 3), (797, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.ofNat 3), (205, Int.negSucc 0), (534,
    Int.negSucc 3), (549, Int.negSucc 11), (555, Int.ofNat 4), (562, Int.negSucc 1), (597,
    Int.negSucc 3), (608, Int.negSucc 3), (621, Int.ofNat 8), (743, Int.ofNat 4), (776, Int.ofNat
    4), (783, Int.negSucc 3), (789, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(559, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(198, Int.ofNat 11), (205, Int.negSucc 4), (211,
    Int.ofNat 4), (219, Int.negSucc 7), (221, Int.ofNat 8), (549, Int.negSucc 23), (552, Int.ofNat
    8), (555, Int.ofNat 4), (562, Int.negSucc 3), (597, Int.negSucc 11), (608, Int.negSucc 11),
    (621, Int.ofNat 8), (743, Int.ofNat 8), (776, Int.ofNat 8), (783, Int.negSucc 7), (789,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(563, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(223, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(569, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(225, Int.ofNat 1), (580, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(583, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(227, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(584, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(222, Int.ofNat 3), (229, Int.negSucc 9), (232,
    Int.negSucc 3), (236, Int.ofNat 4), (240, Int.ofNat 8), (563, Int.ofNat 2), (570, Int.negSucc
    2), (575, Int.negSucc 1), (587, Int.ofNat 2), (599, Int.negSucc 3), (606, Int.negSucc 7),
    (619, Int.negSucc 3), (654, Int.ofNat 4), (750, Int.ofNat 4), (770, Int.ofNat 4), (799,
    Int.negSucc 3), (806, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(230, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(572, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(222, Int.ofNat 2), (229, Int.negSucc 7), (232,
    Int.negSucc 3), (236, Int.ofNat 4), (240, Int.ofNat 8), (563, Int.negSucc 1), (570,
    Int.negSucc 0), (575, Int.negSucc 9), (587, Int.ofNat 2), (606, Int.negSucc 15), (654,
    Int.ofNat 8), (750, Int.ofNat 4), (770, Int.ofNat 4), (799, Int.negSucc 3), (806, Int.negSucc
    3)] },
  { denominator := Int.ofNat 2, terms := [(224, Int.ofNat 3), (233, Int.negSucc 5), (242,
    Int.ofNat 4), (569, Int.ofNat 4), (576, Int.negSucc 11), (592, Int.negSucc 3), (629,
    Int.negSucc 7), (648, Int.ofNat 8), (757, Int.ofNat 4), (778, Int.ofNat 4), (791, Int.negSucc
    3), (805, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(234, Int.negSucc 1), (588, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(226, Int.ofNat 3), (235, Int.negSucc 5), (239,
    Int.ofNat 2), (583, Int.ofNat 16), (589, Int.negSucc 7), (595, Int.negSucc 3), (622, Int.ofNat
    8), (632, Int.negSucc 7), (639, Int.negSucc 3), (764, Int.ofNat 4), (785, Int.ofNat 4), (790,
    Int.ofNat 4), (798, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(222, Int.ofNat 7), (229, Int.negSucc 25), (232,
    Int.negSucc 11), (236, Int.ofNat 12), (240, Int.ofNat 24), (563, Int.negSucc 5), (570,
    Int.negSucc 5), (575, Int.negSucc 19), (587, Int.ofNat 2), (599, Int.negSucc 3), (606,
    Int.negSucc 39), (619, Int.negSucc 11), (654, Int.ofNat 20), (750, Int.ofNat 12), (770,
    Int.ofNat 12), (799, Int.negSucc 11), (806, Int.negSucc 11)] },
  { denominator := Int.ofNat 4, terms := [(224, Int.ofNat 9), (233, Int.negSucc 19), (237,
    Int.ofNat 4), (238, Int.ofNat 4), (242, Int.ofNat 8), (569, Int.ofNat 18), (576, Int.negSucc
    31), (577, Int.ofNat 4), (592, Int.negSucc 7), (600, Int.negSucc 7), (629, Int.negSucc 23),
    (648, Int.ofNat 8), (757, Int.ofNat 8), (778, Int.ofNat 8), (791, Int.negSucc 7), (805,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(224, Int.ofNat 4), (233, Int.negSucc 7), (238,
    Int.ofNat 2), (242, Int.ofNat 4), (569, Int.ofNat 8), (576, Int.negSucc 11), (577, Int.ofNat
    1), (600, Int.negSucc 3), (629, Int.negSucc 7), (648, Int.ofNat 4), (757, Int.ofNat 4), (778,
    Int.ofNat 4), (791, Int.negSucc 3), (805, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(226, Int.ofNat 15), (235, Int.negSucc 29), (239,
    Int.ofNat 10), (583, Int.ofNat 64), (589, Int.negSucc 51), (595, Int.negSucc 11), (622,
    Int.ofNat 24), (632, Int.negSucc 39), (639, Int.negSucc 19), (764, Int.ofNat 20), (785,
    Int.ofNat 20), (790, Int.ofNat 20), (798, Int.ofNat 20)] },
  { denominator := Int.ofNat 4, terms := [(222, Int.ofNat 3), (229, Int.negSucc 9), (232,
    Int.negSucc 3), (236, Int.ofNat 4), (240, Int.ofNat 8), (563, Int.ofNat 2), (570, Int.negSucc
    3), (575, Int.negSucc 1), (587, Int.ofNat 4), (599, Int.negSucc 3), (606, Int.negSucc 7),
    (619, Int.negSucc 3), (654, Int.ofNat 4), (750, Int.ofNat 4), (770, Int.ofNat 4), (799,
    Int.negSucc 3), (806, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(226, Int.ofNat 7), (235, Int.negSucc 15), (239,
    Int.ofNat 4), (241, Int.negSucc 7), (243, Int.ofNat 8), (583, Int.ofNat 28), (589, Int.negSucc
    15), (595, Int.ofNat 8), (601, Int.negSucc 7), (602, Int.ofNat 2), (632, Int.negSucc 7), (639,
    Int.negSucc 3), (764, Int.ofNat 8), (785, Int.ofNat 8), (790, Int.ofNat 8), (798, Int.ofNat
    8)] },
  { denominator := Int.ofNat 4, terms := [(224, Int.ofNat 3), (233, Int.negSucc 5), (242,
    Int.ofNat 4), (569, Int.ofNat 4), (576, Int.negSucc 7), (592, Int.negSucc 11), (629,
    Int.negSucc 7), (648, Int.ofNat 8), (757, Int.ofNat 4), (778, Int.ofNat 4), (791, Int.negSucc
    3), (805, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(226, Int.ofNat 3), (235, Int.negSucc 5), (239,
    Int.ofNat 2), (583, Int.ofNat 16), (589, Int.negSucc 7), (595, Int.negSucc 3), (602, Int.ofNat
    1), (622, Int.ofNat 8), (632, Int.negSucc 7), (639, Int.negSucc 3), (764, Int.ofNat 4), (785,
    Int.ofNat 4), (790, Int.ofNat 4), (798, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(247, Int.ofNat 1), (607, Int.ofNat 2), (620, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(604, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(246, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(247, Int.ofNat 1), (620, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(248, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(611, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(250, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(251, Int.ofNat 1), (623, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(624, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(253, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(612, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(255, Int.negSucc 3), (613, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(245, Int.ofNat 9), (256, Int.negSucc 19), (258,
    Int.negSucc 11), (260, Int.ofNat 8), (262, Int.ofNat 16), (604, Int.ofNat 18), (614,
    Int.negSucc 5), (616, Int.negSucc 3), (625, Int.ofNat 4), (634, Int.negSucc 15), (649,
    Int.negSucc 7), (655, Int.negSucc 7), (772, Int.ofNat 16), (792, Int.ofNat 8), (800, Int.ofNat
    8), (807, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(615, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

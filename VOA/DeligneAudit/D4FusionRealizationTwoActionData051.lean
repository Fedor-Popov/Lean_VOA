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
def actionData051 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 1), (160, Int.negSucc 1), (164,
    Int.ofNat 1), (430, Int.negSucc 31), (442, Int.ofNat 8), (443, Int.ofNat 8), (463, Int.ofNat
    8), (480, Int.negSucc 15), (488, Int.negSucc 15), (510, Int.negSucc 3), (516, Int.negSucc 3),
    (520, Int.negSucc 3), (528, Int.ofNat 8), (535, Int.ofNat 4), (547, Int.ofNat 8), (556,
    Int.ofNat 2), (560, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(451, Int.negSucc 0), (505, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 3), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 2), (91, Int.negSucc 1), (347,
    Int.negSucc 5), (420, Int.ofNat 6), (432, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (131,
    Int.negSucc 1), (385, Int.ofNat 12), (396, Int.negSucc 3), (433, Int.ofNat 16), (471,
    Int.ofNat 3), (486, Int.negSucc 7), (497, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 5), (92, Int.negSucc 1), (362,
    Int.negSucc 2), (419, Int.negSucc 5), (453, Int.ofNat 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 7), (130, Int.ofNat 4), (132,
    Int.negSucc 3), (404, Int.ofNat 12), (412, Int.negSucc 7), (454, Int.ofNat 16), (485,
    Int.ofNat 16), (504, Int.negSucc 2), (512, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (139, Int.ofNat 6), (148,
    Int.negSucc 8), (150, Int.ofNat 12), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat
    4), (162, Int.negSucc 7), (430, Int.negSucc 31), (442, Int.ofNat 16), (443, Int.ofNat 8),
    (480, Int.negSucc 23), (495, Int.negSucc 7), (510, Int.negSucc 3), (516, Int.negSucc 11),
    (524, Int.negSucc 3), (528, Int.ofNat 24), (550, Int.ofNat 8), (556, Int.ofNat 2), (560,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 0), (172, Int.ofNat 1), (481,
    Int.negSucc 7), (489, Int.negSucc 3), (500, Int.ofNat 8), (564, Int.negSucc 1), (578,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 1), (492, Int.negSucc 11), (501,
    Int.ofNat 12), (533, Int.negSucc 11), (567, Int.negSucc 5), (581, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.ofNat 4), (130,
    Int.negSucc 0), (404, Int.ofNat 2), (412, Int.negSucc 3), (454, Int.negSucc 1), (478,
    Int.ofNat 4), (485, Int.negSucc 3), (493, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 3), (150, Int.ofNat 6), (151, Int.negSucc 1), (430,
    Int.ofNat 16), (443, Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 8), (495, Int.ofNat
    8), (516, Int.ofNat 4), (524, Int.ofNat 4), (535, Int.negSucc 3), (547, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.ofNat 2), (172, Int.negSucc 0), (177,
    Int.ofNat 2), (489, Int.negSucc 3), (496, Int.ofNat 4), (500, Int.ofNat 4), (564, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (180, Int.negSucc 1), (192,
    Int.ofNat 1), (470, Int.negSucc 5), (502, Int.ofNat 4), (517, Int.negSucc 1), (521,
    Int.negSucc 1), (541, Int.negSucc 3), (585, Int.ofNat 2), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (181, Int.negSucc 1), (183,
    Int.ofNat 1), (484, Int.negSucc 5), (503, Int.ofNat 4), (529, Int.negSucc 3), (536,
    Int.negSucc 1), (545, Int.negSucc 3), (573, Int.negSucc 1), (593, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 11), (172, Int.ofNat 6), (481,
    Int.negSucc 39), (489, Int.negSucc 19), (500, Int.ofNat 36), (564, Int.negSucc 5), (578,
    Int.ofNat 12), (596, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 1), (473, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 28), (172, Int.ofNat 13), (177,
    Int.ofNat 4), (481, Int.negSucc 103), (489, Int.negSucc 47), (500, Int.ofNat 92), (564,
    Int.negSucc 15), (578, Int.ofNat 24), (596, Int.ofNat 12)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 0), (118, Int.ofNat 1), (125,
    Int.negSucc 3), (385, Int.negSucc 3), (396, Int.ofNat 4), (433, Int.ofNat 4), (479, Int.ofNat
    4), (486, Int.negSucc 3), (508, Int.ofNat 2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 2), (139, Int.ofNat 6), (148,
    Int.negSucc 3), (153, Int.negSucc 7), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 16), (443, Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 8), (510, Int.ofNat
    4), (520, Int.ofNat 4), (528, Int.negSucc 7), (547, Int.negSucc 7), (556, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 2), (172, Int.negSucc 0), (185,
    Int.ofNat 4), (489, Int.negSucc 3), (500, Int.ofNat 4), (511, Int.ofNat 2), (578, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 1), (514, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 28), (172, Int.ofNat 13), (185,
    Int.ofNat 8), (481, Int.negSucc 103), (489, Int.negSucc 47), (500, Int.ofNat 92), (564,
    Int.negSucc 11), (578, Int.ofNat 32), (596, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(187, Int.ofNat 4), (506, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 2), (107, Int.ofNat 8), (110,
    Int.negSucc 5), (124, Int.negSucc 3), (380, Int.negSucc 11), (390, Int.ofNat 16), (421,
    Int.ofNat 8), (475, Int.ofNat 12), (487, Int.negSucc 7), (494, Int.ofNat 12), (509, Int.ofNat
    2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 8), (148,
    Int.negSucc 16), (150, Int.ofNat 24), (151, Int.negSucc 7), (160, Int.ofNat 6), (162,
    Int.negSucc 7), (164, Int.negSucc 0), (430, Int.ofNat 80), (443, Int.negSucc 31), (448,
    Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 48), (495, Int.ofNat 32), (510,
    Int.ofNat 4), (516, Int.ofNat 4), (520, Int.ofNat 12), (524, Int.ofNat 12), (535, Int.negSucc
    15), (547, Int.negSucc 23), (550, Int.negSucc 23), (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 4), (172, Int.negSucc 2), (177,
    Int.ofNat 16), (185, Int.ofNat 8), (481, Int.negSucc 63), (489, Int.negSucc 31), (496,
    Int.ofNat 16), (500, Int.ofNat 60), (511, Int.ofNat 4), (564, Int.negSucc 11), (596, Int.ofNat
    12)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 10), (172, Int.ofNat 6), (190,
    Int.ofNat 4), (481, Int.negSucc 47), (489, Int.negSucc 15), (496, Int.negSucc 3), (500,
    Int.ofNat 40), (511, Int.negSucc 1), (564, Int.negSucc 7), (578, Int.ofNat 16), (596,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.ofNat 1), (201, Int.negSucc 0), (217,
    Int.ofNat 2), (522, Int.negSucc 1), (553, Int.ofNat 4), (618, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.ofNat 1), (203, Int.negSucc 0), (210,
    Int.ofNat 1), (537, Int.negSucc 1), (554, Int.ofNat 4), (605, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(197, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.negSucc 2), (205, Int.ofNat 2), (534,
    Int.negSucc 15), (549, Int.negSucc 7), (555, Int.ofNat 16), (608, Int.negSucc 3), (621,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.ofNat 3), (205, Int.negSucc 1), (211,
    Int.ofNat 4), (534, Int.negSucc 3), (549, Int.negSucc 7), (552, Int.ofNat 8), (555, Int.ofNat
    8), (608, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (201, Int.ofNat 1), (217,
    Int.ofNat 2), (518, Int.negSucc 5), (522, Int.negSucc 3), (542, Int.negSucc 3), (553,
    Int.ofNat 8), (565, Int.negSucc 5), (618, Int.ofNat 4), (628, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 0), (203, Int.ofNat 1), (210,
    Int.ofNat 1), (530, Int.negSucc 11), (537, Int.negSucc 3), (546, Int.negSucc 3), (554,
    Int.ofNat 8), (579, Int.negSucc 11), (605, Int.negSucc 1), (631, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(201, Int.negSucc 0), (208, Int.ofNat 2), (217,
    Int.ofNat 2), (518, Int.negSucc 3), (522, Int.negSucc 5), (526, Int.ofNat 2), (553, Int.ofNat
    4), (565, Int.negSucc 5), (628, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.ofNat 3), (205, Int.negSucc 1), (219,
    Int.ofNat 8), (534, Int.negSucc 3), (549, Int.negSucc 7), (555, Int.ofNat 8), (562, Int.ofNat
    4), (621, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.negSucc 0), (203, Int.negSucc 1), (210,
    Int.ofNat 4), (218, Int.ofNat 4), (530, Int.negSucc 31), (537, Int.negSucc 15), (546,
    Int.negSucc 7), (554, Int.ofNat 24), (558, Int.ofNat 1), (579, Int.negSucc 35), (605,
    Int.negSucc 5), (631, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(223, Int.ofNat 1), (566, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(224, Int.ofNat 1), (233, Int.negSucc 1), (242,
    Int.ofNat 4), (569, Int.negSucc 1), (576, Int.negSucc 3), (600, Int.ofNat 8), (648, Int.ofNat
    8)] },
  { denominator := Int.ofNat 2, terms := [(225, Int.ofNat 1), (580, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(226, Int.ofNat 1), (235, Int.negSucc 1), (239,
    Int.ofNat 2), (583, Int.negSucc 3), (589, Int.negSucc 3), (601, Int.ofNat 8), (639,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(227, Int.ofNat 3), (598, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(229, Int.negSucc 3), (236, Int.ofNat 2), (240,
    Int.ofNat 4), (563, Int.negSucc 3), (570, Int.negSucc 0), (575, Int.negSucc 3), (599,
    Int.ofNat 4), (606, Int.negSucc 5), (654, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(247, Int.ofNat 1), (603, Int.negSucc 1), (607,
    Int.ofNat 2), (620, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

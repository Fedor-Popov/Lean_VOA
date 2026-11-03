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
def actionData161 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 6), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (160, Int.ofNat 4), (163, Int.negSucc 7), (430,
    Int.negSucc 15), (442, Int.ofNat 8), (443, Int.negSucc 7), (448, Int.ofNat 8), (463, Int.ofNat
    8), (480, Int.ofNat 8), (488, Int.negSucc 15), (495, Int.ofNat 8), (510, Int.ofNat 4), (520,
    Int.negSucc 3), (535, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 2), (418, Int.ofNat 2), (472, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (143, Int.ofNat 4), (148,
    Int.negSucc 5), (150, Int.ofNat 4), (153, Int.ofNat 8), (157, Int.negSucc 7), (160, Int.ofNat
    4), (430, Int.negSucc 23), (442, Int.ofNat 8), (448, Int.ofNat 8), (463, Int.ofNat 8), (480,
    Int.negSucc 15), (488, Int.negSucc 23), (495, Int.ofNat 16), (510, Int.ofNat 8), (516,
    Int.negSucc 3), (520, Int.negSucc 3), (528, Int.ofNat 8), (535, Int.ofNat 4), (547, Int.ofNat
    16), (550, Int.negSucc 7), (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 3), (158, Int.negSucc 3), (437,
    Int.ofNat 2), (498, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 2), (451, Int.ofNat 1), (505, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (159, Int.negSucc 3), (458,
    Int.ofNat 1), (513, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 6), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 11), (151, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.ofNat 8), (163, Int.negSucc 7), (430, Int.negSucc 23), (442, Int.ofNat 8), (443,
    Int.negSucc 7), (448, Int.ofNat 16), (463, Int.ofNat 8), (480, Int.ofNat 8), (488, Int.negSucc
    23), (495, Int.ofNat 8), (510, Int.ofNat 8), (520, Int.negSucc 3), (524, Int.negSucc 3), (535,
    Int.ofNat 8), (550, Int.ofNat 8), (556, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 1), (158, Int.negSucc 1), (437,
    Int.ofNat 2), (498, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.negSucc 0), (158, Int.ofNat 2), (532,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (458, Int.ofNat 3), (513, Int.ofNat
    6)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 6), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 3), (160, Int.negSucc 3), (162,
    Int.ofNat 8), (163, Int.negSucc 7), (164, Int.ofNat 2), (430, Int.negSucc 23), (442, Int.ofNat
    8), (443, Int.negSucc 7), (448, Int.ofNat 8), (463, Int.ofNat 16), (480, Int.ofNat 8), (488,
    Int.negSucc 23), (495, Int.ofNat 16), (510, Int.ofNat 4), (520, Int.negSucc 7), (524,
    Int.ofNat 4), (535, Int.ofNat 4), (556, Int.ofNat 2), (560, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 2), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.ofNat 3), (437, Int.ofNat 6), (498, Int.ofNat
    12)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 4), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 6), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 3), (172, Int.negSucc 1), (177,
    Int.ofNat 2), (185, Int.ofNat 4), (190, Int.negSucc 3), (489, Int.negSucc 7), (496, Int.ofNat
    4), (500, Int.ofNat 4), (511, Int.ofNat 2), (564, Int.negSucc 1), (578, Int.ofNat 4)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.ofNat 5), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (186, Int.ofNat 12), (191, Int.negSucc 11), (492, Int.negSucc 11), (501,
    Int.ofNat 12), (533, Int.ofNat 12), (548, Int.negSucc 23), (551, Int.ofNat 24), (561,
    Int.ofNat 12), (567, Int.negSucc 5), (581, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 4), (473, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.ofNat 1), (172, Int.negSucc 2), (177,
    Int.ofNat 4), (185, Int.ofNat 8), (481, Int.negSucc 23), (489, Int.negSucc 15), (496,
    Int.ofNat 8), (500, Int.ofNat 20), (511, Int.ofNat 4), (564, Int.negSucc 3), (578, Int.ofNat
    8), (596, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(187, Int.ofNat 8), (506, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 2), (514, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(170, Int.negSucc 1), (180, Int.negSucc 4), (182,
    Int.ofNat 2), (192, Int.ofNat 2), (470, Int.negSucc 5), (502, Int.ofNat 4), (517, Int.negSucc
    1), (521, Int.negSucc 5), (525, Int.ofNat 2), (585, Int.ofNat 2), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 3), (181, Int.negSucc 6), (183,
    Int.ofNat 2), (193, Int.ofNat 2), (484, Int.negSucc 5), (503, Int.ofNat 4), (529, Int.negSucc
    3), (536, Int.negSucc 5), (557, Int.ofNat 1), (573, Int.negSucc 1), (593, Int.ofNat 4)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 5), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (186, Int.ofNat 12), (191, Int.negSucc 11), (501, Int.ofNat 12), (551, Int.ofNat
    24), (561, Int.ofNat 12), (567, Int.negSucc 5), (581, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 19), (173, Int.negSucc 23), (178,
    Int.ofNat 18), (186, Int.ofNat 36), (191, Int.negSucc 23), (492, Int.negSucc 23), (501,
    Int.ofNat 24), (533, Int.ofNat 24), (548, Int.negSucc 71), (551, Int.ofNat 72), (561,
    Int.ofNat 36), (567, Int.negSucc 17), (581, Int.ofNat 36)] },
  { denominator := Int.ofNat 2, terms := [(188, Int.ofNat 4), (507, Int.ofNat 1)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 5), (173, Int.negSucc 5), (186,
    Int.ofNat 12), (501, Int.ofNat 12), (533, Int.negSucc 11), (551, Int.ofNat 24), (561,
    Int.ofNat 12), (567, Int.negSucc 5), (581, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.ofNat 1), (499, Int.ofNat 12)] },
  { denominator := Int.ofNat 24, terms := [(168, Int.ofNat 5), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (501, Int.ofNat 12), (533, Int.negSucc 11), (551, Int.ofNat 24), (561, Int.ofNat
    12), (567, Int.negSucc 11), (581, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(189, Int.ofNat 1), (514, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 1), (201, Int.negSucc 3), (208,
    Int.ofNat 2), (217, Int.ofNat 4), (518, Int.negSucc 3), (522, Int.negSucc 7), (526, Int.ofNat
    2), (553, Int.ofNat 4), (565, Int.negSucc 7), (618, Int.ofNat 4), (628, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.ofNat 1), (203, Int.negSucc 5), (210,
    Int.ofNat 2), (218, Int.ofNat 4), (530, Int.negSucc 7), (537, Int.negSucc 7), (554, Int.ofNat
    4), (558, Int.ofNat 1), (579, Int.negSucc 15), (605, Int.negSucc 1), (631, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.ofNat 3), (205, Int.negSucc 1), (211,
    Int.ofNat 2), (219, Int.ofNat 4), (221, Int.negSucc 3), (549, Int.negSucc 7), (552, Int.ofNat
    4), (555, Int.ofNat 4), (562, Int.ofNat 2), (608, Int.negSucc 1), (621, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(199, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 4), (527, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.ofNat 11), (205, Int.negSucc 6), (211,
    Int.ofNat 4), (219, Int.ofNat 8), (549, Int.negSucc 15), (552, Int.ofNat 8), (555, Int.ofNat
    4), (562, Int.ofNat 4), (597, Int.negSucc 3), (608, Int.negSucc 3), (621, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(220, Int.ofNat 8), (559, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(202, Int.negSucc 0), (207, Int.ofNat 1), (568,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(204, Int.negSucc 0), (216, Int.ofNat 2), (582,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.ofNat 1), (205, Int.negSucc 0), (211,
    Int.ofNat 2), (219, Int.ofNat 4), (221, Int.negSucc 3), (534, Int.negSucc 7), (552, Int.ofNat
    4), (555, Int.ofNat 8), (562, Int.ofNat 2), (597, Int.ofNat 4), (608, Int.negSucc 1), (621,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.negSucc 0), (219, Int.ofNat 8), (534,
    Int.negSucc 27), (552, Int.ofNat 8), (555, Int.ofNat 24), (562, Int.ofNat 4), (597, Int.ofNat
    8), (608, Int.negSucc 3), (621, Int.ofNat 16)] },
  { denominator := Int.ofNat 8, terms := [(198, Int.negSucc 0), (211, Int.ofNat 4), (534,
    Int.negSucc 27), (552, Int.ofNat 8), (555, Int.ofNat 24), (562, Int.ofNat 4), (597, Int.ofNat
    8), (608, Int.negSucc 7), (621, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(222, Int.ofNat 4), (229, Int.negSucc 15), (232,
    Int.negSucc 7), (236, Int.ofNat 8), (240, Int.ofNat 16), (563, Int.negSucc 3), (570,
    Int.negSucc 3), (575, Int.negSucc 7), (606, Int.negSucc 15), (619, Int.negSucc 7), (654,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(224, Int.ofNat 5), (233, Int.negSucc 11), (238,
    Int.ofNat 4), (242, Int.ofNat 8), (569, Int.ofNat 6), (576, Int.negSucc 15), (577, Int.ofNat
    4), (629, Int.negSucc 7), (648, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(226, Int.ofNat 5), (235, Int.negSucc 15), (239,
    Int.ofNat 4), (243, Int.ofNat 8), (583, Int.ofNat 12), (589, Int.negSucc 15), (602, Int.ofNat
    2), (632, Int.negSucc 7), (639, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(227, Int.ofNat 1), (598, Int.ofNat 8)] },
  { denominator := Int.ofNat 3, terms := [(228, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 3, terms := [(228, Int.negSucc 0), (584, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(224, Int.ofNat 1), (233, Int.negSucc 3), (237,
    Int.ofNat 4), (569, Int.negSucc 1), (609, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(226, Int.ofNat 1), (235, Int.negSucc 3), (241,
    Int.ofNat 8), (583, Int.negSucc 3), (622, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(245, Int.ofNat 7), (256, Int.negSucc 15), (258,
    Int.negSucc 11), (260, Int.ofNat 8), (262, Int.ofNat 16), (604, Int.ofNat 10), (614,
    Int.negSucc 3), (616, Int.negSucc 7), (634, Int.negSucc 7), (649, Int.negSucc 7), (655,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(248, Int.negSucc 2), (261, Int.ofNat 2), (610,
    Int.negSucc 5), (617, Int.ofNat 2)] },
  { denominator := Int.ofNat 3, terms := [(249, Int.negSucc 0), (611, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(251, Int.negSucc 2), (263, Int.ofNat 4), (623,
    Int.negSucc 11), (627, Int.ofNat 2)] },
  { denominator := Int.ofNat 3, terms := [(252, Int.negSucc 0), (624, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(253, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(266, Int.ofNat 5), (269, Int.negSucc 5), (275,
    Int.negSucc 21), (276, Int.ofNat 8), (277, Int.ofNat 16), (637, Int.ofNat 14), (645,
    Int.negSucc 12), (647, Int.ofNat 16), (650, Int.negSucc 7), (652, Int.ofNat 8), (656,
    Int.negSucc 7), (657, Int.negSucc 7)] },
  { denominator := Int.ofNat 3, terms := [(267, Int.negSucc 1), (638, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

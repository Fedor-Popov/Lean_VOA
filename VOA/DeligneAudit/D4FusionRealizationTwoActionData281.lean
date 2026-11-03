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
def actionData281 : List ActionCase := [
  { denominator := Int.ofNat 1, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 12), (429, Int.negSucc
    11), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 3), (482,
    Int.ofNat 2), (490, Int.ofNat 4), (695, Int.ofNat 4), (745, Int.negSucc 3), (752, Int.negSucc
    3), (759, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(110, Int.ofNat 1), (124, Int.negSucc 1), (421,
    Int.ofNat 2), (475, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 4), (385, Int.negSucc 7), (396, Int.ofNat 8), (433,
    Int.negSucc 7), (471, Int.negSucc 3), (479, Int.negSucc 3), (486, Int.ofNat 4), (497,
    Int.ofNat 8), (508, Int.negSucc 1), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.negSucc 3), (399, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 0), (132, Int.ofNat 4), (404, Int.ofNat 4), (412, Int.ofNat 4), (454, Int.ofNat
    8), (504, Int.negSucc 0), (512, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(113, Int.ofNat 2), (414, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(114, Int.ofNat 1), (424, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(399, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(450, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.ofNat 1), (120, Int.ofNat 12), (390, Int.ofNat
    12), (421, Int.ofNat 4), (475, Int.ofNat 8), (487, Int.ofNat 4), (509, Int.negSucc 1), (765,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(121, Int.ofNat 4), (399, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 14), (130, Int.negSucc 0), (134,
    Int.ofNat 1), (412, Int.ofNat 12), (454, Int.ofNat 2), (478, Int.ofNat 4), (485, Int.negSucc
    3), (504, Int.ofNat 2), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 10), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (404, Int.negSucc 1), (412, Int.ofNat 8), (454,
    Int.negSucc 1), (478, Int.ofNat 4), (485, Int.negSucc 7), (493, Int.ofNat 4), (504, Int.ofNat
    1), (512, Int.ofNat 2), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 1), (152, Int.ofNat 4), (425,
    Int.negSucc 1), (476, Int.negSucc 3), (544, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 3), (139, Int.negSucc 3), (153,
    Int.ofNat 8), (430, Int.negSucc 15), (442, Int.ofNat 16), (480, Int.negSucc 15), (488,
    Int.negSucc 7), (510, Int.ofNat 4), (516, Int.negSucc 7), (528, Int.ofNat 16), (547, Int.ofNat
    8), (560, Int.negSucc 3), (766, Int.negSucc 7), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 8), (451, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 4), (455, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 12), (458, Int.ofNat 6), (513, Int.ofNat
    12)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.ofNat 1), (476, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (415, Int.ofNat 2), (465, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 2), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(148, Int.negSucc 0), (153, Int.ofNat 4), (160,
    Int.ofNat 1), (430, Int.negSucc 13), (442, Int.ofNat 10), (443, Int.ofNat 2), (463, Int.ofNat
    2), (480, Int.negSucc 9), (488, Int.negSucc 9), (510, Int.ofNat 3), (516, Int.negSucc 3),
    (520, Int.negSucc 1), (528, Int.ofNat 8), (535, Int.ofNat 2), (547, Int.ofNat 8), (560,
    Int.negSucc 1), (696, Int.ofNat 2), (709, Int.ofNat 2), (746, Int.negSucc 1), (753,
    Int.negSucc 1), (760, Int.ofNat 2), (766, Int.negSucc 5), (774, Int.negSucc 1), (781,
    Int.ofNat 2), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(154, Int.ofNat 8), (161, Int.ofNat 2), (451, Int.ofNat
    3), (505, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.ofNat 1), (152, Int.negSucc 1), (425,
    Int.ofNat 1), (476, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (139, Int.ofNat 10), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (153, Int.ofNat 8), (160, Int.ofNat 4), (163, Int.negSucc
    7), (430, Int.negSucc 39), (442, Int.ofNat 24), (448, Int.ofNat 8), (463, Int.ofNat 8), (480,
    Int.negSucc 23), (488, Int.negSucc 31), (495, Int.ofNat 8), (510, Int.ofNat 8), (516,
    Int.negSucc 7), (520, Int.negSucc 7), (528, Int.ofNat 16), (535, Int.ofNat 4), (547, Int.ofNat
    24), (560, Int.negSucc 3), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753,
    Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 7), (150, Int.negSucc 13), (151,
    Int.ofNat 2), (157, Int.negSucc 7), (162, Int.ofNat 8), (430, Int.negSucc 15), (448, Int.ofNat
    16), (480, Int.ofNat 8), (488, Int.negSucc 7), (495, Int.negSucc 7), (510, Int.ofNat 4), (524,
    Int.negSucc 7), (528, Int.negSucc 7), (535, Int.ofNat 4), (550, Int.ofNat 16), (556,
    Int.negSucc 1), (774, Int.negSucc 7), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.ofNat 6), (451, Int.ofNat 3), (505, Int.ofNat
    3)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.ofNat 1), (425, Int.ofNat 1), (476, Int.ofNat
    1)] },
  { denominator := Int.ofNat 4, terms := [(154, Int.ofNat 4), (451, Int.ofNat 2), (505, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(148, Int.ofNat 1), (153, Int.ofNat 8), (160,
    Int.negSucc 2), (164, Int.ofNat 1), (430, Int.negSucc 21), (442, Int.ofNat 10), (443,
    Int.ofNat 2), (463, Int.ofNat 10), (480, Int.negSucc 5), (488, Int.negSucc 13), (510,
    Int.ofNat 1), (516, Int.negSucc 1), (520, Int.negSucc 3), (528, Int.ofNat 8), (535, Int.ofNat
    2), (547, Int.ofNat 8), (556, Int.ofNat 2), (560, Int.ofNat 2), (696, Int.ofNat 2), (709,
    Int.ofNat 2), (746, Int.negSucc 1), (753, Int.negSucc 1), (760, Int.ofNat 2), (766,
    Int.negSucc 5), (774, Int.negSucc 1), (781, Int.ofNat 6), (787, Int.ofNat 4), (802, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(154, Int.ofNat 6), (451, Int.ofNat 1), (543,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 3), (184, Int.ofNat 8), (484,
    Int.negSucc 3), (529, Int.negSucc 7), (545, Int.negSucc 7), (593, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.ofNat 2), (466, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (185,
    Int.ofNat 4), (481, Int.negSucc 19), (489, Int.negSucc 11), (500, Int.ofNat 20), (511,
    Int.ofNat 2), (564, Int.negSucc 3), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat
    8), (767, Int.negSucc 3), (775, Int.negSucc 3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 7), (173, Int.negSucc 5), (186,
    Int.ofNat 12), (492, Int.negSucc 23), (501, Int.ofNat 24), (533, Int.ofNat 12), (548,
    Int.negSucc 23), (561, Int.ofNat 12), (567, Int.negSucc 11), (581, Int.ofNat 24), (788,
    Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(187, Int.ofNat 4), (506, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(188, Int.ofNat 12), (507, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 8), (514, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (184, Int.ofNat 2), (529,
    Int.negSucc 1), (536, Int.ofNat 1), (545, Int.negSucc 1), (593, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (180, Int.negSucc 6), (192,
    Int.ofNat 3), (470, Int.negSucc 11), (502, Int.ofNat 8), (517, Int.negSucc 1), (521,
    Int.negSucc 9), (585, Int.ofNat 4), (590, Int.ofNat 8), (803, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 5), (181, Int.negSucc 7), (183,
    Int.ofNat 2), (184, Int.ofNat 8), (193, Int.ofNat 2), (484, Int.negSucc 13), (503, Int.ofNat
    4), (529, Int.negSucc 11), (536, Int.negSucc 7), (545, Int.negSucc 11), (557, Int.ofNat 1),
    (573, Int.negSucc 3), (593, Int.ofNat 16), (796, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(171, Int.negSucc 3), (181, Int.negSucc 6), (183,
    Int.ofNat 2), (193, Int.ofNat 2), (484, Int.negSucc 11), (503, Int.ofNat 8), (529, Int.negSucc
    7), (536, Int.negSucc 7), (545, Int.negSucc 3), (557, Int.ofNat 1), (573, Int.negSucc 3),
    (593, Int.ofNat 12), (796, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 6), (172, Int.ofNat 1), (177,
    Int.ofNat 4), (185, Int.ofNat 12), (190, Int.negSucc 7), (481, Int.negSucc 51), (489,
    Int.negSucc 35), (496, Int.ofNat 8), (500, Int.ofNat 52), (511, Int.ofNat 6), (564,
    Int.negSucc 11), (578, Int.ofNat 16), (596, Int.ofNat 12), (710, Int.ofNat 24), (767,
    Int.negSucc 11), (775, Int.negSucc 11), (782, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(181, Int.ofNat 1), (184, Int.ofNat 4), (193,
    Int.negSucc 0), (484, Int.negSucc 0), (529, Int.negSucc 1), (536, Int.ofNat 1), (545,
    Int.negSucc 3), (573, Int.negSucc 0), (593, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(187, Int.ofNat 4), (506, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(194, Int.ofNat 1), (515, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 0), (215, Int.ofNat 4), (530,
    Int.negSucc 7), (537, Int.negSucc 1), (546, Int.negSucc 3), (554, Int.ofNat 4), (579,
    Int.negSucc 11), (631, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.negSucc 5), (216, Int.ofNat 12), (538,
    Int.negSucc 5), (582, Int.ofNat 12), (594, Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 4), (201, Int.negSucc 9), (217,
    Int.ofNat 12), (518, Int.negSucc 11), (522, Int.negSucc 27), (553, Int.ofNat 16), (565,
    Int.negSucc 31), (618, Int.ofNat 16), (628, Int.ofNat 16), (721, Int.ofNat 8), (769,
    Int.negSucc 7), (777, Int.negSucc 7), (804, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.ofNat 2), (203, Int.negSucc 5), (210,
    Int.ofNat 2), (218, Int.ofNat 4), (530, Int.negSucc 11), (537, Int.negSucc 11), (546,
    Int.negSucc 3), (554, Int.ofNat 8), (558, Int.ofNat 1), (579, Int.negSucc 31), (605,
    Int.negSucc 3), (631, Int.ofNat 8), (732, Int.ofNat 4), (768, Int.ofNat 4), (784, Int.negSucc
    3), (797, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.ofNat 13), (205, Int.negSucc 5), (219,
    Int.ofNat 8), (534, Int.ofNat 4), (549, Int.negSucc 23), (555, Int.ofNat 8), (562, Int.ofNat
    4), (597, Int.negSucc 7), (608, Int.negSucc 7), (621, Int.ofNat 16), (743, Int.ofNat 8), (776,
    Int.ofNat 8), (783, Int.negSucc 7), (789, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(220, Int.ofNat 8), (559, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.ofNat 2), (213, Int.negSucc 0), (519,
    Int.negSucc 0), (574, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(214, Int.negSucc 0)] }
]

end VOA.DeligneAudit.D4Two.Certificate

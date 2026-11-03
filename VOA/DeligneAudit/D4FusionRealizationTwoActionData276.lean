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
def actionData276 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 5), (126, Int.ofNat 4), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.ofNat 4), (412, Int.negSucc 7), (454, Int.ofNat
    4), (478, Int.negSucc 3), (485, Int.ofNat 4), (493, Int.negSucc 3), (504, Int.negSucc 1),
    (512, Int.negSucc 3), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 4), (118, Int.ofNat 3), (125,
    Int.ofNat 4), (131, Int.negSucc 3), (385, Int.ofNat 4), (396, Int.negSucc 7), (433, Int.ofNat
    4), (471, Int.ofNat 2), (479, Int.ofNat 4), (486, Int.negSucc 7), (497, Int.negSucc 3), (508,
    Int.ofNat 2), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.ofNat 2), (141, Int.negSucc 1), (415,
    Int.ofNat 2), (465, Int.ofNat 2), (540, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(142, Int.negSucc 3), (418, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.negSucc 0), (422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (139, Int.ofNat 4), (143,
    Int.negSucc 3), (430, Int.ofNat 16), (442, Int.negSucc 15), (480, Int.ofNat 16), (488,
    Int.ofNat 8), (495, Int.negSucc 7), (516, Int.ofNat 8), (528, Int.negSucc 15), (547,
    Int.negSucc 7), (550, Int.ofNat 8), (766, Int.ofNat 8), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.negSucc 1), (434, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 5), (437, Int.negSucc 11), (498,
    Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 0), (465, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(141, Int.negSucc 0), (540, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.negSucc 1), (149, Int.negSucc 0), (418,
    Int.negSucc 2), (472, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 1), (425, Int.negSucc 1), (476,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 1), (148, Int.ofNat 1), (150,
    Int.negSucc 0), (430, Int.ofNat 14), (442, Int.negSucc 9), (443, Int.negSucc 1), (448,
    Int.negSucc 1), (480, Int.ofNat 10), (488, Int.ofNat 10), (495, Int.negSucc 5), (516,
    Int.ofNat 4), (520, Int.ofNat 2), (528, Int.negSucc 7), (535, Int.negSucc 1), (547,
    Int.negSucc 7), (550, Int.ofNat 4), (696, Int.negSucc 1), (709, Int.negSucc 1), (746,
    Int.ofNat 2), (753, Int.ofNat 2), (760, Int.negSucc 1), (766, Int.ofNat 6), (774, Int.ofNat
    2), (781, Int.negSucc 1), (787, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(141, Int.negSucc 0), (415, Int.negSucc 1), (465,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.negSucc 0), (149, Int.ofNat 1), (418,
    Int.ofNat 1), (472, Int.ofNat 1), (539, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(143, Int.negSucc 3), (148, Int.negSucc 0), (150,
    Int.ofNat 3), (151, Int.negSucc 1), (430, Int.ofNat 22), (442, Int.negSucc 9), (443,
    Int.negSucc 1), (448, Int.negSucc 9), (480, Int.ofNat 6), (488, Int.ofNat 14), (495,
    Int.negSucc 1), (516, Int.ofNat 4), (520, Int.ofNat 2), (524, Int.ofNat 4), (528, Int.negSucc
    3), (535, Int.negSucc 3), (547, Int.negSucc 7), (550, Int.negSucc 3), (696, Int.negSucc 1),
    (709, Int.negSucc 1), (746, Int.ofNat 2), (753, Int.ofNat 2), (760, Int.negSucc 1), (766,
    Int.ofNat 6), (774, Int.ofNat 6), (781, Int.negSucc 1), (787, Int.negSucc 3), (795,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(137, Int.negSucc 0), (141, Int.ofNat 1), (415,
    Int.negSucc 0), (465, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 6), (139, Int.negSucc 9), (143,
    Int.negSucc 3), (148, Int.ofNat 5), (150, Int.negSucc 3), (160, Int.negSucc 3), (163,
    Int.ofNat 8), (430, Int.ofNat 40), (442, Int.negSucc 23), (448, Int.negSucc 7), (463,
    Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 32), (495, Int.negSucc 15), (510,
    Int.negSucc 3), (516, Int.ofNat 8), (520, Int.ofNat 4), (528, Int.negSucc 15), (535,
    Int.negSucc 7), (547, Int.negSucc 23), (550, Int.ofNat 8), (696, Int.negSucc 7), (709,
    Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat
    16), (774, Int.ofNat 8), (781, Int.negSucc 7), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(149, Int.negSucc 2), (418, Int.negSucc 2), (472,
    Int.negSucc 2)] },
  { denominator := Int.ofNat 8, terms := [(143, Int.negSucc 3), (148, Int.negSucc 2), (150,
    Int.ofNat 4), (153, Int.negSucc 7), (157, Int.ofNat 8), (160, Int.ofNat 6), (162, Int.negSucc
    7), (164, Int.negSucc 0), (430, Int.ofNat 72), (442, Int.negSucc 39), (443, Int.negSucc 7),
    (448, Int.negSucc 7), (463, Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 48), (495,
    Int.negSucc 31), (510, Int.ofNat 4), (516, Int.ofNat 12), (520, Int.ofNat 12), (524,
    Int.negSucc 3), (528, Int.negSucc 31), (535, Int.negSucc 7), (547, Int.negSucc 31), (550,
    Int.ofNat 16), (556, Int.negSucc 3), (560, Int.negSucc 7), (696, Int.negSucc 7), (709,
    Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat
    24), (774, Int.ofNat 8), (781, Int.negSucc 15), (787, Int.negSucc 15), (802, Int.negSucc 7)]
    },
  { denominator := Int.ofNat 1, terms := [(466, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 4), (174, Int.negSucc 3), (470,
    Int.ofNat 4), (517, Int.ofNat 4), (541, Int.ofNat 8), (590, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0), (466, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.negSucc 1), (473, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.negSucc 5), (474, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.negSucc 1), (477, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 3), (172, Int.negSucc 0), (177,
    Int.negSucc 1), (481, Int.ofNat 20), (489, Int.ofNat 12), (496, Int.negSucc 3), (500,
    Int.negSucc 19), (564, Int.ofNat 4), (578, Int.negSucc 7), (596, Int.negSucc 3), (710,
    Int.negSucc 7), (767, Int.ofNat 4), (775, Int.ofNat 4), (782, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 6), (173, Int.ofNat 6), (178,
    Int.negSucc 5), (492, Int.ofNat 24), (501, Int.negSucc 23), (533, Int.negSucc 11), (548,
    Int.ofNat 24), (551, Int.negSucc 23), (567, Int.ofNat 12), (581, Int.negSucc 23), (788,
    Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.negSucc 3), (499, Int.negSucc 15)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(169, Int.negSucc 1), (467, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (174, Int.negSucc 0), (517,
    Int.ofNat 1), (521, Int.negSucc 0), (541, Int.ofNat 2), (590, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (174, Int.negSucc 1), (180,
    Int.ofNat 3), (182, Int.negSucc 0), (192, Int.negSucc 0), (470, Int.ofNat 7), (502,
    Int.negSucc 1), (517, Int.ofNat 3), (521, Int.ofNat 4), (525, Int.negSucc 0), (541, Int.ofNat
    6), (585, Int.negSucc 1), (590, Int.negSucc 7), (803, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 1), (181, Int.ofNat 7), (183,
    Int.negSucc 2), (484, Int.ofNat 12), (503, Int.negSucc 7), (529, Int.ofNat 4), (536, Int.ofNat
    10), (573, Int.ofNat 4), (593, Int.negSucc 7), (796, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (174, Int.negSucc 1), (182,
    Int.ofNat 1), (470, Int.ofNat 1), (517, Int.ofNat 1), (521, Int.negSucc 0), (541, Int.ofNat
    4), (585, Int.negSucc 0), (590, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.negSucc 0), (473, Int.negSucc 2)] },
  { denominator := Int.ofNat 4, terms := [(170, Int.ofNat 2), (180, Int.ofNat 5), (182,
    Int.negSucc 1), (192, Int.negSucc 1), (470, Int.ofNat 12), (502, Int.negSucc 7), (517,
    Int.ofNat 4), (521, Int.ofNat 8), (525, Int.negSucc 1), (541, Int.ofNat 4), (585, Int.negSucc
    3), (590, Int.negSucc 11), (803, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 7), (172, Int.negSucc 0), (177,
    Int.negSucc 5), (185, Int.negSucc 7), (190, Int.ofNat 8), (481, Int.ofNat 52), (489, Int.ofNat
    36), (496, Int.negSucc 11), (500, Int.negSucc 51), (511, Int.negSucc 3), (564, Int.ofNat 8),
    (578, Int.negSucc 23), (596, Int.negSucc 11), (710, Int.negSucc 23), (767, Int.ofNat 12),
    (775, Int.ofNat 12), (782, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(194, Int.negSucc 0), (515, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.ofNat 1), (206, Int.negSucc 1), (518,
    Int.ofNat 4), (522, Int.ofNat 2), (542, Int.ofNat 4), (553, Int.negSucc 3), (565, Int.ofNat
    6), (628, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.ofNat 6), (207, Int.negSucc 5), (523,
    Int.ofNat 6), (568, Int.negSucc 5), (591, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 1), (201, Int.ofNat 4), (208,
    Int.negSucc 1), (217, Int.negSucc 3), (518, Int.ofNat 6), (522, Int.ofNat 12), (526,
    Int.negSucc 1), (542, Int.ofNat 4), (553, Int.negSucc 7), (565, Int.ofNat 16), (618,
    Int.negSucc 7), (628, Int.negSucc 7), (721, Int.negSucc 3), (769, Int.ofNat 4), (777,
    Int.ofNat 4), (804, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.negSucc 3), (527, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 3), (203, Int.ofNat 10), (210,
    Int.negSucc 5), (530, Int.ofNat 24), (537, Int.ofNat 28), (554, Int.negSucc 15), (579,
    Int.ofNat 64), (605, Int.ofNat 8), (631, Int.negSucc 15), (732, Int.negSucc 7), (768,
    Int.negSucc 7), (784, Int.ofNat 8), (797, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.negSucc 12), (205, Int.ofNat 6), (211,
    Int.negSucc 3), (534, Int.negSucc 3), (549, Int.ofNat 24), (552, Int.negSucc 7), (555,
    Int.negSucc 7), (597, Int.ofNat 8), (608, Int.ofNat 8), (621, Int.negSucc 15), (743,
    Int.negSucc 7), (776, Int.negSucc 7), (783, Int.ofNat 8), (789, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(212, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.negSucc 1), (213, Int.ofNat 1), (519,
    Int.ofNat 1), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.ofNat 1), (206, Int.negSucc 1), (518,
    Int.ofNat 4), (522, Int.negSucc 1), (542, Int.ofNat 4), (553, Int.negSucc 3), (565, Int.ofNat
    2), (628, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.ofNat 1), (206, Int.negSucc 3), (208,
    Int.ofNat 2), (518, Int.ofNat 6), (522, Int.negSucc 3), (542, Int.ofNat 8), (553, Int.negSucc
    7), (565, Int.ofNat 2), (618, Int.negSucc 3), (628, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

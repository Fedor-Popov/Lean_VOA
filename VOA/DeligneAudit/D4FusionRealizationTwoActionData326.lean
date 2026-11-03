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
def actionData326 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(385, Int.negSucc 3), (396, Int.ofNat 2), (433,
    Int.negSucc 3), (471, Int.negSucc 0), (479, Int.ofNat 2), (486, Int.ofNat 2), (497, Int.ofNat
    4), (773, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 2), (385, Int.negSucc 3), (396, Int.ofNat 4), (433, Int.negSucc 3), (471,
    Int.negSucc 1), (497, Int.ofNat 8), (773, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(109, Int.negSucc 0), (375, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(107, Int.ofNat 1), (110, Int.negSucc 0), (380,
    Int.negSucc 3), (390, Int.ofNat 4), (421, Int.negSucc 1), (464, Int.negSucc 0), (475,
    Int.ofNat 6), (494, Int.ofNat 2), (765, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 1), (385,
    Int.negSucc 3), (396, Int.ofNat 4), (479, Int.ofNat 12), (497, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(380, Int.negSucc 3), (509, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(404, Int.negSucc 3), (412, Int.ofNat 4), (454,
    Int.negSucc 3), (504, Int.ofNat 2), (512, Int.ofNat 4), (780, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(385, Int.negSucc 1), (508, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 1), (465, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 2), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(469, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(415, Int.ofNat 2), (465, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 2), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(418, Int.ofNat 1), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (430, Int.negSucc 7), (442,
    Int.ofNat 8), (480, Int.negSucc 7), (516, Int.negSucc 3), (528, Int.ofNat 16), (766,
    Int.negSucc 7), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(135, Int.ofNat 1), (422, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(532, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(415, Int.negSucc 0), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(425, Int.negSucc 0), (476, Int.negSucc 1), (544,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (430, Int.negSucc 23), (442,
    Int.ofNat 8), (443, Int.ofNat 8), (480, Int.negSucc 23), (488, Int.negSucc 15), (516,
    Int.negSucc 3), (520, Int.negSucc 3), (528, Int.ofNat 16), (535, Int.ofNat 8), (547, Int.ofNat
    16), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760,
    Int.ofNat 8), (766, Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat
    8)] },
  { denominator := Int.ofNat 1, terms := [(539, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (148, Int.ofNat 1), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (430, Int.negSucc 31), (442, Int.ofNat 8), (443, Int.ofNat
    8), (448, Int.ofNat 8), (480, Int.negSucc 23), (488, Int.negSucc 15), (495, Int.negSucc 7),
    (516, Int.negSucc 3), (520, Int.negSucc 3), (524, Int.negSucc 3), (528, Int.ofNat 16), (535,
    Int.ofNat 8), (547, Int.ofNat 16), (550, Int.ofNat 16), (696, Int.ofNat 8), (709, Int.ofNat
    8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 15),
    (774, Int.negSucc 15), (781, Int.ofNat 8), (787, Int.ofNat 8), (795, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(144, Int.ofNat 3), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(137, Int.ofNat 1), (141, Int.negSucc 0), (415,
    Int.ofNat 2), (465, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(142, Int.negSucc 0), (149, Int.ofNat 1), (418,
    Int.ofNat 3), (472, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 6), (143,
    Int.negSucc 3), (148, Int.negSucc 2), (150, Int.ofNat 4), (430, Int.negSucc 31), (442,
    Int.ofNat 24), (448, Int.ofNat 8), (480, Int.negSucc 23), (488, Int.negSucc 7), (516,
    Int.negSucc 7), (520, Int.negSucc 3), (528, Int.ofNat 40), (535, Int.ofNat 4), (547, Int.ofNat
    8), (550, Int.ofNat 8), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc 7), (753,
    Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 23), (774, Int.negSucc 7), (781,
    Int.ofNat 8), (787, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(430, Int.negSucc 7), (463, Int.ofNat 4), (510,
    Int.negSucc 3), (556, Int.ofNat 2), (560, Int.ofNat 4), (781, Int.ofNat 4), (802, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(455, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(466, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(466, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(470, Int.ofNat 2), (517, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(466, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(473, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(474, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(467, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(470, Int.ofNat 4), (517, Int.ofNat 2), (521, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(470, Int.ofNat 3), (517, Int.ofNat 1), (521, Int.ofNat
    1), (525, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(473, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(473, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(165, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(166, Int.ofNat 1), (477, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 4), (172, Int.ofNat 3), (481,
    Int.negSucc 23), (489, Int.negSucc 7), (500, Int.ofNat 20), (564, Int.negSucc 3), (578,
    Int.ofNat 16), (596, Int.ofNat 4), (710, Int.ofNat 16), (767, Int.negSucc 7), (775,
    Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(168, Int.ofNat 1), (492, Int.negSucc 5), (501,
    Int.ofNat 6), (567, Int.negSucc 2), (581, Int.ofNat 12), (788, Int.negSucc 11)] },
  { denominator := Int.ofNat 4, terms := [(165, Int.ofNat 1), (466, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(175, Int.ofNat 1), (473, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 1), (172, Int.negSucc 0), (177,
    Int.ofNat 4), (481, Int.negSucc 7), (489, Int.negSucc 7), (496, Int.ofNat 8), (500, Int.ofNat
    12), (564, Int.negSucc 3), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 16), (767,
    Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.ofNat 1), (499, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.negSucc 0), (180, Int.negSucc 1), (192,
    Int.ofNat 1), (470, Int.negSucc 7), (502, Int.ofNat 4), (517, Int.negSucc 1), (521,
    Int.negSucc 3), (541, Int.negSucc 3), (585, Int.ofNat 4), (590, Int.ofNat 8), (803, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (181, Int.negSucc 1), (183,
    Int.ofNat 1), (484, Int.negSucc 3), (503, Int.ofNat 2), (529, Int.negSucc 3), (536,
    Int.negSucc 2), (573, Int.negSucc 0), (593, Int.ofNat 4), (796, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.negSucc 32), (172, Int.ofNat 15), (481,
    Int.negSucc 103), (489, Int.negSucc 39), (500, Int.ofNat 84), (564, Int.negSucc 11), (578,
    Int.ofNat 48), (596, Int.ofNat 20), (710, Int.ofNat 48), (767, Int.negSucc 23), (775,
    Int.negSucc 23), (782, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(175, Int.ofNat 1), (473, Int.ofNat 3)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.negSucc 40), (172, Int.ofNat 17), (177,
    Int.ofNat 4), (481, Int.negSucc 135), (489, Int.negSucc 47), (500, Int.ofNat 108), (564,
    Int.negSucc 15), (578, Int.ofNat 56), (596, Int.ofNat 28), (710, Int.ofNat 64), (767,
    Int.negSucc 31), (775, Int.negSucc 31), (782, Int.ofNat 32)] },
  { denominator := Int.ofNat 4, terms := [(170, Int.ofNat 1), (174, Int.negSucc 1), (180,
    Int.negSucc 2), (182, Int.ofNat 2), (192, Int.ofNat 1), (470, Int.ofNat 2), (517, Int.ofNat
    4), (521, Int.negSucc 3), (525, Int.ofNat 2), (585, Int.ofNat 2), (590, Int.ofNat 4), (803,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 6), (172, Int.ofNat 3), (481,
    Int.negSucc 19), (489, Int.negSucc 7), (500, Int.ofNat 16), (511, Int.negSucc 1), (564,
    Int.negSucc 1), (578, Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 8), (767, Int.negSucc
    3), (775, Int.negSucc 3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(518, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(515, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(518, Int.ofNat 3), (522, Int.ofNat 1), (565, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [(523, Int.ofNat 3), (568, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(518, Int.ofNat 1), (526, Int.ofNat 1), (565, Int.ofNat
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(527, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(212, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(519, Int.ofNat 2), (574, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(518, Int.ofNat 2), (522, Int.ofNat 6), (565, Int.ofNat
    6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(518, Int.ofNat 1), (522, Int.ofNat 4), (526, Int.ofNat
    1), (565, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(522, Int.ofNat 1), (526, Int.ofNat 3), (565, Int.ofNat
    1)] },
  { denominator := Int.ofNat 4, terms := [(194, Int.ofNat 1), (515, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(195, Int.ofNat 1), (201, Int.negSucc 0), (217,
    Int.ofNat 2), (518, Int.negSucc 3), (522, Int.negSucc 5), (553, Int.ofNat 4), (565,
    Int.negSucc 7), (618, Int.ofNat 8), (628, Int.ofNat 4), (721, Int.ofNat 4), (769, Int.negSucc
    3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.ofNat 1), (203, Int.negSucc 1), (210,
    Int.ofNat 1), (537, Int.negSucc 3), (546, Int.ofNat 2), (579, Int.negSucc 7), (605,
    Int.negSucc 0), (631, Int.ofNat 2), (732, Int.ofNat 2), (768, Int.ofNat 2), (784, Int.negSucc
    1), (797, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(197, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.ofNat 4), (205, Int.negSucc 0), (549,
    Int.negSucc 7), (555, Int.ofNat 4), (597, Int.negSucc 3), (608, Int.negSucc 3), (621,
    Int.ofNat 16), (743, Int.ofNat 8), (776, Int.ofNat 8), (783, Int.negSucc 7), (789, Int.negSucc
    7)] },
  { denominator := Int.ofNat 4, terms := [(195, Int.ofNat 2), (201, Int.negSucc 2), (208,
    Int.ofNat 2), (217, Int.ofNat 2), (522, Int.negSucc 5), (526, Int.ofNat 2), (565, Int.negSucc
    7), (618, Int.ofNat 4), (628, Int.ofNat 4), (721, Int.ofNat 4), (769, Int.negSucc 3), (777,
    Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.ofNat 1), (527, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.ofNat 10), (205, Int.negSucc 4), (211,
    Int.ofNat 4), (534, Int.ofNat 12), (549, Int.negSucc 7), (552, Int.ofNat 8), (555, Int.negSucc
    3), (597, Int.negSucc 3), (608, Int.negSucc 3), (621, Int.ofNat 8), (743, Int.ofNat 8), (776,
    Int.ofNat 8), (783, Int.negSucc 7), (789, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.negSucc 0), (201, Int.ofNat 1), (217,
    Int.ofNat 2), (518, Int.negSucc 5), (522, Int.negSucc 3), (542, Int.negSucc 3), (553,
    Int.ofNat 8), (565, Int.negSucc 7), (618, Int.ofNat 8), (628, Int.ofNat 8), (721, Int.ofNat
    4), (769, Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(203, Int.negSucc 0), (210, Int.ofNat 1), (530,
    Int.negSucc 5), (537, Int.negSucc 4), (554, Int.ofNat 2), (579, Int.negSucc 13), (605,
    Int.negSucc 0), (631, Int.ofNat 4), (732, Int.ofNat 2), (768, Int.ofNat 2), (784, Int.negSucc
    1), (797, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(201, Int.negSucc 0), (208, Int.ofNat 2), (217,
    Int.ofNat 2), (518, Int.negSucc 3), (522, Int.negSucc 5), (526, Int.ofNat 6), (553, Int.ofNat
    4), (565, Int.negSucc 7), (618, Int.ofNat 4), (628, Int.ofNat 8), (721, Int.ofNat 4), (769,
    Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(195, Int.ofNat 1), (201, Int.negSucc 0), (206,
    Int.negSucc 1), (208, Int.ofNat 2), (217, Int.ofNat 2), (518, Int.ofNat 4), (522, Int.ofNat
    2), (526, Int.ofNat 2), (618, Int.ofNat 4), (628, Int.ofNat 4), (721, Int.ofNat 4), (769,
    Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 0), (201, Int.ofNat 1), (217,
    Int.ofNat 2), (518, Int.negSucc 7), (522, Int.negSucc 5), (542, Int.negSucc 11), (553,
    Int.ofNat 8), (565, Int.negSucc 13), (618, Int.ofNat 8), (628, Int.ofNat 8), (721, Int.ofNat
    4), (769, Int.negSucc 3), (777, Int.negSucc 3), (804, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(566, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(569, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(231, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(563, Int.ofNat 2), (570, Int.negSucc 0), (575,
    Int.ofNat 2), (606, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(566, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(569, Int.ofNat 4), (576, Int.ofNat 2), (609, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(231, Int.negSucc 0), (572, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(566, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(569, Int.ofNat 1), (577, Int.ofNat 2), (609, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(231, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(575, Int.ofNat 2), (606, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(231, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(563, Int.ofNat 2), (570, Int.negSucc 2), (575,
    Int.ofNat 14), (606, Int.ofNat 10)] }
]

end VOA.DeligneAudit.D4Two.Certificate

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
def actionData292 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 4), (118, Int.ofNat 3), (125,
    Int.ofNat 8), (131, Int.negSucc 3), (385, Int.ofNat 12), (396, Int.negSucc 7), (433, Int.ofNat
    8), (471, Int.ofNat 4), (479, Int.ofNat 4), (486, Int.negSucc 7), (497, Int.negSucc 3), (508,
    Int.ofNat 2), (773, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (119,
    Int.negSucc 0), (125, Int.ofNat 2), (131, Int.negSucc 1), (385, Int.ofNat 4), (396,
    Int.negSucc 3), (433, Int.ofNat 4), (471, Int.ofNat 2), (479, Int.ofNat 2), (486, Int.negSucc
    1), (497, Int.negSucc 3), (508, Int.ofNat 1), (773, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 5), (126, Int.ofNat 20), (130,
    Int.ofNat 3), (132, Int.negSucc 7), (404, Int.ofNat 2), (412, Int.negSucc 3), (454,
    Int.negSucc 9), (504, Int.ofNat 2), (512, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 1), (120, Int.negSucc 7), (124, Int.ofNat 8), (380, Int.ofNat 12), (390,
    Int.negSucc 7), (421, Int.ofNat 8), (464, Int.ofNat 2), (475, Int.negSucc 7), (487,
    Int.negSucc 7), (494, Int.ofNat 4), (509, Int.ofNat 2), (765, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 9), (126, Int.ofNat 8), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.ofNat 6), (412, Int.negSucc 7), (454, Int.ofNat
    4), (478, Int.negSucc 3), (485, Int.ofNat 8), (493, Int.negSucc 3), (504, Int.negSucc 1),
    (512, Int.negSucc 1), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 3), (125,
    Int.ofNat 20), (131, Int.negSucc 7), (385, Int.ofNat 4), (396, Int.negSucc 3), (433,
    Int.negSucc 19), (471, Int.negSucc 3), (497, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 13), (126, Int.ofNat 16), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (134, Int.negSucc 0), (404, Int.ofNat 6), (412,
    Int.negSucc 11), (454, Int.negSucc 1), (478, Int.negSucc 3), (485, Int.ofNat 4), (493,
    Int.negSucc 3), (504, Int.negSucc 1), (780, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (139, Int.ofNat 4), (143,
    Int.negSucc 3), (153, Int.negSucc 7), (157, Int.ofNat 8), (430, Int.ofNat 16), (442,
    Int.negSucc 15), (480, Int.ofNat 16), (488, Int.ofNat 8), (495, Int.negSucc 7), (510,
    Int.negSucc 3), (516, Int.ofNat 8), (528, Int.negSucc 15), (547, Int.negSucc 7), (550,
    Int.ofNat 8), (560, Int.ofNat 4), (766, Int.ofNat 8), (787, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(135, Int.negSucc 0), (422, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.negSucc 0), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.negSucc 5), (158, Int.ofNat 12), (498,
    Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(155, Int.negSucc 1), (455, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 11), (159, Int.ofNat 12), (513,
    Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 0), (141, Int.ofNat 1), (465,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(138, Int.negSucc 0), (152, Int.ofNat 2), (476,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 6), (139, Int.negSucc 9), (143,
    Int.negSucc 3), (148, Int.ofNat 5), (150, Int.negSucc 3), (153, Int.negSucc 7), (157,
    Int.ofNat 8), (160, Int.negSucc 3), (163, Int.ofNat 8), (430, Int.ofNat 48), (442, Int.negSucc
    23), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 24), (488, Int.ofNat 40),
    (495, Int.negSucc 15), (510, Int.negSucc 7), (516, Int.ofNat 8), (520, Int.ofNat 8), (528,
    Int.negSucc 15), (535, Int.negSucc 7), (547, Int.negSucc 23), (550, Int.ofNat 8), (560,
    Int.ofNat 4), (696, Int.negSucc 7), (709, Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat
    8), (760, Int.negSucc 7), (766, Int.ofNat 16), (774, Int.ofNat 8), (781, Int.negSucc 7), (787,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 2), (149, Int.negSucc 1), (472,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(143, Int.negSucc 3), (148, Int.ofNat 3), (150,
    Int.negSucc 1), (153, Int.negSucc 7), (157, Int.ofNat 12), (160, Int.negSucc 1), (430,
    Int.ofNat 32), (442, Int.negSucc 19), (443, Int.negSucc 3), (448, Int.negSucc 3), (463,
    Int.negSucc 3), (480, Int.ofNat 20), (488, Int.ofNat 20), (495, Int.negSucc 11), (510,
    Int.negSucc 5), (516, Int.ofNat 8), (520, Int.ofNat 4), (528, Int.negSucc 15), (535,
    Int.negSucc 3), (547, Int.negSucc 15), (550, Int.ofNat 8), (560, Int.ofNat 4), (696,
    Int.negSucc 3), (709, Int.negSucc 3), (746, Int.ofNat 4), (753, Int.ofNat 4), (760,
    Int.negSucc 3), (766, Int.ofNat 12), (774, Int.ofNat 4), (781, Int.negSucc 3), (787,
    Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 4), (161, Int.negSucc 1), (505,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 6), (139, Int.negSucc 9), (143,
    Int.negSucc 3), (148, Int.negSucc 2), (150, Int.ofNat 12), (151, Int.negSucc 3), (153,
    Int.negSucc 7), (157, Int.ofNat 16), (160, Int.negSucc 3), (162, Int.negSucc 7), (163,
    Int.ofNat 8), (430, Int.ofNat 64), (442, Int.negSucc 23), (448, Int.negSucc 23), (463,
    Int.negSucc 7), (480, Int.ofNat 16), (488, Int.ofNat 48), (495, Int.negSucc 7), (510,
    Int.negSucc 11), (516, Int.ofNat 8), (520, Int.ofNat 8), (524, Int.ofNat 8), (528, Int.negSucc
    7), (535, Int.negSucc 11), (547, Int.negSucc 23), (550, Int.negSucc 7), (556, Int.ofNat 2),
    (560, Int.ofNat 4), (696, Int.negSucc 7), (709, Int.negSucc 7), (746, Int.ofNat 8), (753,
    Int.ofNat 8), (760, Int.negSucc 7), (766, Int.ofNat 16), (774, Int.ofNat 16), (781,
    Int.negSucc 7), (787, Int.negSucc 7), (795, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.negSucc 2), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 6), (139, Int.negSucc 9), (148,
    Int.negSucc 2), (150, Int.ofNat 4), (153, Int.negSucc 15), (157, Int.ofNat 16), (160,
    Int.ofNat 4), (162, Int.negSucc 7), (163, Int.ofNat 8), (164, Int.negSucc 1), (430, Int.ofNat
    64), (442, Int.negSucc 23), (448, Int.negSucc 7), (463, Int.negSucc 23), (480, Int.ofNat 16),
    (488, Int.ofNat 48), (495, Int.negSucc 23), (510, Int.negSucc 3), (516, Int.ofNat 4), (520,
    Int.ofNat 12), (524, Int.negSucc 3), (528, Int.negSucc 15), (535, Int.negSucc 7), (547,
    Int.negSucc 23), (550, Int.ofNat 8), (556, Int.negSucc 3), (560, Int.negSucc 3), (696,
    Int.negSucc 7), (709, Int.negSucc 7), (746, Int.ofNat 8), (753, Int.ofNat 8), (760,
    Int.negSucc 7), (766, Int.ofNat 16), (774, Int.ofNat 8), (781, Int.negSucc 15), (787,
    Int.negSucc 7), (802, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.negSucc 2), (455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0), (466, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.negSucc 0), (477, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 0), (172, Int.ofNat 1), (177,
    Int.negSucc 3), (185, Int.negSucc 7), (190, Int.ofNat 8), (481, Int.ofNat 24), (489, Int.ofNat
    24), (496, Int.negSucc 7), (500, Int.negSucc 27), (511, Int.negSucc 3), (564, Int.ofNat 8),
    (578, Int.negSucc 15), (596, Int.negSucc 3), (710, Int.negSucc 15), (767, Int.ofNat 8), (775,
    Int.ofNat 8), (782, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 6), (173, Int.ofNat 6), (178,
    Int.negSucc 5), (186, Int.negSucc 11), (191, Int.ofNat 12), (492, Int.ofNat 24), (501,
    Int.negSucc 23), (533, Int.negSucc 11), (548, Int.ofNat 24), (551, Int.negSucc 23), (561,
    Int.negSucc 11), (567, Int.ofNat 12), (581, Int.negSucc 23), (788, Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.negSucc 3), (473, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 2), (177, Int.negSucc 1), (185,
    Int.negSucc 3), (481, Int.ofNat 20), (489, Int.ofNat 12), (496, Int.negSucc 3), (500,
    Int.negSucc 19), (511, Int.negSucc 1), (564, Int.ofNat 4), (578, Int.negSucc 7), (596,
    Int.negSucc 3), (710, Int.negSucc 7), (767, Int.ofNat 4), (775, Int.ofNat 4), (782,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.negSucc 1), (499, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(187, Int.negSucc 7), (506, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.negSucc 3), (514, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 1), (174, Int.ofNat 2), (180, Int.ofNat
    7), (182, Int.negSucc 1), (192, Int.negSucc 2), (470, Int.ofNat 12), (502, Int.negSucc 7),
    (517, Int.ofNat 2), (521, Int.ofNat 10), (525, Int.negSucc 1), (585, Int.negSucc 3), (590,
    Int.negSucc 7), (803, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

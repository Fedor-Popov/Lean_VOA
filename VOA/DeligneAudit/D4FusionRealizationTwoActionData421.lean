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
def actionData421 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 3), (120, Int.negSucc 3), (124, Int.ofNat 8), (380, Int.ofNat 16), (390,
    Int.negSucc 11), (421, Int.ofNat 12), (464, Int.ofNat 6), (475, Int.negSucc 7), (487,
    Int.negSucc 7), (494, Int.ofNat 4), (509, Int.ofNat 2), (765, Int.negSucc 7), (822, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 4), (118, Int.ofNat 3), (125,
    Int.ofNat 8), (131, Int.negSucc 3), (385, Int.ofNat 16), (396, Int.negSucc 11), (433,
    Int.ofNat 12), (471, Int.ofNat 6), (479, Int.ofNat 4), (486, Int.negSucc 7), (497, Int.negSucc
    7), (508, Int.ofNat 2), (773, Int.negSucc 7), (820, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.negSucc 1), (118, Int.ofNat 2), (119,
    Int.negSucc 0), (125, Int.ofNat 2), (131, Int.negSucc 1), (385, Int.ofNat 6), (396,
    Int.negSucc 5), (433, Int.ofNat 6), (471, Int.ofNat 3), (479, Int.ofNat 2), (486, Int.negSucc
    1), (497, Int.negSucc 5), (508, Int.ofNat 1), (773, Int.negSucc 3), (820, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.negSucc 5), (126, Int.ofNat 20), (130,
    Int.ofNat 3), (132, Int.negSucc 7), (404, Int.ofNat 2), (412, Int.negSucc 3), (454,
    Int.negSucc 9), (504, Int.ofNat 2), (512, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(106, Int.negSucc 0), (107, Int.ofNat 2), (110,
    Int.negSucc 1), (120, Int.negSucc 7), (124, Int.ofNat 8), (380, Int.ofNat 16), (390,
    Int.negSucc 11), (421, Int.ofNat 12), (464, Int.ofNat 4), (475, Int.negSucc 11), (487,
    Int.negSucc 7), (494, Int.ofNat 4), (509, Int.ofNat 2), (765, Int.negSucc 7), (822, Int.ofNat
    4)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 9), (126, Int.ofNat 8), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (404, Int.ofNat 8), (412, Int.negSucc 11), (454, Int.ofNat
    6), (478, Int.negSucc 3), (485, Int.ofNat 8), (493, Int.negSucc 3), (504, Int.negSucc 2),
    (512, Int.negSucc 3), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.negSucc 2), (118, Int.ofNat 3), (125,
    Int.ofNat 20), (131, Int.negSucc 7), (385, Int.ofNat 4), (396, Int.negSucc 3), (433,
    Int.negSucc 19), (471, Int.negSucc 3), (497, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 13), (126, Int.ofNat 16), (130,
    Int.ofNat 3), (132, Int.negSucc 3), (134, Int.negSucc 0), (404, Int.ofNat 8), (412,
    Int.negSucc 15), (478, Int.negSucc 3), (485, Int.ofNat 4), (493, Int.negSucc 3), (504,
    Int.negSucc 2), (512, Int.negSucc 1), (780, Int.negSucc 7), (817, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(135, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 2), (139, Int.ofNat 4), (143,
    Int.negSucc 3), (153, Int.negSucc 7), (157, Int.ofNat 8), (430, Int.ofNat 24), (442,
    Int.negSucc 23), (480, Int.ofNat 24), (488, Int.ofNat 8), (495, Int.negSucc 7), (510,
    Int.negSucc 3), (516, Int.ofNat 12), (528, Int.negSucc 23), (547, Int.negSucc 7), (550,
    Int.ofNat 8), (560, Int.ofNat 4), (766, Int.ofNat 16), (787, Int.negSucc 15), (824,
    Int.negSucc 7), (826, Int.ofNat 8)] },
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
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 7), (139, Int.negSucc 9), (143,
    Int.negSucc 3), (148, Int.ofNat 5), (150, Int.negSucc 3), (153, Int.negSucc 7), (157,
    Int.ofNat 8), (160, Int.negSucc 3), (163, Int.ofNat 8), (430, Int.ofNat 64), (442, Int.negSucc
    31), (443, Int.negSucc 7), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 40),
    (488, Int.ofNat 48), (495, Int.negSucc 15), (510, Int.negSucc 7), (516, Int.ofNat 12), (520,
    Int.ofNat 12), (528, Int.negSucc 23), (535, Int.negSucc 11), (547, Int.negSucc 31), (550,
    Int.ofNat 8), (560, Int.ofNat 4), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 32), (774,
    Int.ofNat 16), (781, Int.negSucc 15), (787, Int.negSucc 15), (824, Int.negSucc 15), (826,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 2), (149, Int.negSucc 1), (472,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 1), (143, Int.negSucc 7), (148,
    Int.ofNat 6), (150, Int.negSucc 3), (153, Int.negSucc 15), (157, Int.ofNat 24), (160,
    Int.negSucc 3), (430, Int.ofNat 88), (442, Int.negSucc 55), (443, Int.negSucc 15), (448,
    Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 64), (488, Int.ofNat 48), (495,
    Int.negSucc 23), (510, Int.negSucc 11), (516, Int.ofNat 24), (520, Int.ofNat 12), (528,
    Int.negSucc 47), (535, Int.negSucc 11), (547, Int.negSucc 39), (550, Int.ofNat 16), (560,
    Int.ofNat 8), (696, Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753,
    Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 48), (774, Int.ofNat 16), (781,
    Int.negSucc 15), (787, Int.negSucc 31), (824, Int.negSucc 23), (826, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.ofNat 4), (161, Int.negSucc 1), (505,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 7), (139, Int.negSucc 9), (143,
    Int.negSucc 3), (148, Int.negSucc 2), (150, Int.ofNat 12), (151, Int.negSucc 3), (153,
    Int.negSucc 7), (157, Int.ofNat 16), (160, Int.negSucc 3), (162, Int.negSucc 7), (163,
    Int.ofNat 8), (430, Int.ofNat 88), (442, Int.negSucc 31), (443, Int.negSucc 7), (448,
    Int.negSucc 31), (463, Int.negSucc 7), (480, Int.ofNat 32), (488, Int.ofNat 56), (510,
    Int.negSucc 11), (516, Int.ofNat 12), (520, Int.ofNat 12), (524, Int.ofNat 12), (528,
    Int.negSucc 15), (535, Int.negSucc 15), (547, Int.negSucc 31), (550, Int.negSucc 15), (556,
    Int.ofNat 2), (560, Int.ofNat 4), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 32), (774,
    Int.ofNat 32), (781, Int.negSucc 15), (787, Int.negSucc 15), (795, Int.negSucc 15), (824,
    Int.negSucc 23), (826, Int.ofNat 8), (829, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.negSucc 2), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 7), (139, Int.negSucc 9), (148,
    Int.negSucc 2), (150, Int.ofNat 4), (153, Int.negSucc 15), (157, Int.ofNat 16), (160,
    Int.ofNat 4), (162, Int.negSucc 7), (163, Int.ofNat 8), (164, Int.negSucc 1), (430, Int.ofNat
    88), (442, Int.negSucc 31), (443, Int.negSucc 7), (448, Int.negSucc 7), (463, Int.negSucc 31),
    (480, Int.ofNat 32), (488, Int.ofNat 56), (495, Int.negSucc 23), (516, Int.ofNat 8), (520,
    Int.ofNat 16), (524, Int.negSucc 3), (528, Int.negSucc 23), (535, Int.negSucc 11), (547,
    Int.negSucc 31), (550, Int.ofNat 8), (556, Int.negSucc 5), (560, Int.negSucc 7), (696,
    Int.negSucc 19), (709, Int.negSucc 15), (746, Int.ofNat 16), (753, Int.ofNat 16), (760,
    Int.negSucc 15), (766, Int.ofNat 32), (774, Int.ofNat 16), (781, Int.negSucc 31), (787,
    Int.negSucc 15), (802, Int.negSucc 15), (824, Int.negSucc 23), (826, Int.ofNat 8), (832,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(155, Int.negSucc 2), (455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0), (466, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.negSucc 0), (477, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 3), (172, Int.negSucc 0), (177,
    Int.negSucc 1), (185, Int.negSucc 3), (190, Int.ofNat 4), (481, Int.ofNat 24), (489, Int.ofNat
    16), (496, Int.negSucc 3), (500, Int.negSucc 23), (511, Int.negSucc 1), (564, Int.ofNat 6),
    (578, Int.negSucc 11), (596, Int.negSucc 3), (710, Int.negSucc 15), (767, Int.ofNat 8), (775,
    Int.ofNat 8), (782, Int.negSucc 7), (825, Int.negSucc 1)] }
]

end VOA.DeligneAudit.D4Two.Certificate

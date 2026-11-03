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
def actionData415 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(108, Int.ofNat 2), (115, Int.negSucc 0), (117,
    Int.ofNat 2), (128, Int.ofNat 2), (133, Int.negSucc 3), (391, Int.ofNat 16), (429, Int.negSucc
    15), (441, Int.ofNat 4), (447, Int.ofNat 4), (462, Int.ofNat 4), (468, Int.negSucc 5), (482,
    Int.ofNat 6), (490, Int.ofNat 4), (695, Int.ofNat 12), (745, Int.negSucc 7), (752, Int.negSucc
    7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.ofNat 1), (125,
    Int.negSucc 3), (396, Int.ofNat 4), (433, Int.ofNat 8), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(112, Int.ofNat 1), (436, Int.ofNat 6)] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.negSucc 3), (130,
    Int.ofNat 1), (412, Int.ofNat 4), (454, Int.ofNat 4), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 3, terms := [(123, Int.ofNat 2), (457, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(127, Int.negSucc 7), (407, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 3), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 4), (385, Int.negSucc 11), (396, Int.ofNat 12), (433,
    Int.negSucc 11), (471, Int.negSucc 5), (479, Int.negSucc 3), (486, Int.ofNat 8), (497,
    Int.ofNat 8), (508, Int.negSucc 1), (773, Int.ofNat 8), (820, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(436, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(111, Int.ofNat 1), (118, Int.negSucc 1), (119,
    Int.ofNat 1), (131, Int.ofNat 2), (385, Int.negSucc 5), (396, Int.ofNat 6), (433, Int.negSucc
    5), (471, Int.negSucc 2), (486, Int.ofNat 2), (497, Int.ofNat 6), (508, Int.negSucc 0), (773,
    Int.ofNat 4), (820, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(122, Int.ofNat 2), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 8), (404, Int.ofNat 4), (412, Int.ofNat 4), (454, Int.ofNat
    8), (504, Int.negSucc 1), (512, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(116, Int.ofNat 4), (417, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(115, Int.negSucc 1), (117, Int.ofNat 2), (128,
    Int.ofNat 2), (391, Int.ofNat 16), (429, Int.negSucc 15), (447, Int.ofNat 4), (462, Int.ofNat
    4), (468, Int.negSucc 5), (482, Int.ofNat 6), (490, Int.ofNat 6), (695, Int.ofNat 12), (745,
    Int.negSucc 7), (752, Int.negSucc 7), (759, Int.ofNat 8), (823, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(129, Int.ofNat 4), (450, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (404, Int.negSucc 5), (412, Int.ofNat 12), (454,
    Int.negSucc 5), (478, Int.ofNat 4), (485, Int.negSucc 7), (493, Int.ofNat 4), (504, Int.ofNat
    3), (512, Int.ofNat 4), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(457, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(111, Int.ofNat 1), (118, Int.negSucc 2), (125,
    Int.negSucc 3), (131, Int.ofNat 8), (385, Int.ofNat 8), (396, Int.ofNat 4), (433, Int.ofNat
    16), (471, Int.ofNat 4), (497, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.ofNat 6), (126, Int.negSucc 3), (130,
    Int.negSucc 2), (132, Int.ofNat 4), (134, Int.ofNat 1), (404, Int.negSucc 5), (412, Int.ofNat
    16), (454, Int.negSucc 1), (485, Int.negSucc 3), (493, Int.ofNat 4), (504, Int.ofNat 3), (512,
    Int.ofNat 4), (780, Int.ofNat 8), (817, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(127, Int.negSucc 1), (407, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(127, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 2), (153, Int.ofNat 4), (157, Int.negSucc 3), (430, Int.negSucc 11), (442, Int.ofNat
    12), (480, Int.negSucc 11), (488, Int.negSucc 3), (495, Int.ofNat 4), (510, Int.ofNat 2),
    (516, Int.negSucc 5), (528, Int.ofNat 12), (547, Int.ofNat 4), (550, Int.negSucc 3), (560,
    Int.negSucc 1), (766, Int.negSucc 7), (787, Int.ofNat 8), (824, Int.ofNat 4), (826,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 1), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 2), (158, Int.negSucc 3), (498,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 2), (455, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 4), (159, Int.negSucc 3), (513,
    Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 8), (139, Int.ofNat 14), (148,
    Int.negSucc 4), (150, Int.ofNat 4), (160, Int.ofNat 4), (163, Int.negSucc 7), (430,
    Int.negSucc 31), (442, Int.ofNat 8), (443, Int.ofNat 8), (448, Int.ofNat 8), (463, Int.ofNat
    8), (480, Int.negSucc 7), (488, Int.negSucc 31), (495, Int.ofNat 8), (510, Int.ofNat 4), (520,
    Int.negSucc 11), (535, Int.ofNat 12), (547, Int.ofNat 16), (696, Int.ofNat 20), (709,
    Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766,
    Int.negSucc 15), (774, Int.negSucc 15), (781, Int.ofNat 16), (824, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(491, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 2), (418, Int.ofNat 2), (472, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 2), (143, Int.ofNat 4), (148,
    Int.negSucc 5), (150, Int.ofNat 4), (153, Int.ofNat 8), (157, Int.negSucc 7), (160, Int.ofNat
    4), (430, Int.negSucc 55), (442, Int.ofNat 24), (443, Int.ofNat 16), (448, Int.ofNat 8), (463,
    Int.ofNat 8), (480, Int.negSucc 47), (488, Int.negSucc 39), (495, Int.ofNat 16), (510,
    Int.ofNat 8), (516, Int.negSucc 11), (520, Int.negSucc 11), (528, Int.ofNat 24), (535,
    Int.ofNat 12), (547, Int.ofNat 32), (550, Int.negSucc 7), (560, Int.negSucc 3), (696,
    Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760,
    Int.ofNat 16), (766, Int.negSucc 31), (774, Int.negSucc 15), (781, Int.ofNat 16), (787,
    Int.ofNat 16), (824, Int.ofNat 16), (826, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 3), (158, Int.negSucc 3), (437,
    Int.ofNat 2), (498, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 2), (451, Int.ofNat 1), (505, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (159, Int.negSucc 3), (458,
    Int.ofNat 1), (513, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 8), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 11), (151, Int.ofNat 4), (160, Int.ofNat
    4), (162, Int.ofNat 8), (163, Int.negSucc 7), (430, Int.negSucc 55), (442, Int.ofNat 8), (443,
    Int.ofNat 8), (448, Int.ofNat 32), (463, Int.ofNat 8), (480, Int.negSucc 7), (488, Int.negSucc
    39), (495, Int.negSucc 7), (510, Int.ofNat 8), (520, Int.negSucc 11), (524, Int.negSucc 11),
    (535, Int.ofNat 16), (547, Int.ofNat 16), (550, Int.ofNat 24), (556, Int.negSucc 1), (696,
    Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760,
    Int.ofNat 16), (766, Int.negSucc 15), (774, Int.negSucc 31), (781, Int.ofNat 16), (795,
    Int.ofNat 16), (824, Int.ofNat 16), (829, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 1), (158, Int.negSucc 1), (437,
    Int.ofNat 2), (498, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.negSucc 0), (158, Int.ofNat 2), (532,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(156, Int.ofNat 6), (458, Int.ofNat 3), (513, Int.ofNat
    6)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 8), (139, Int.ofNat 14), (143,
    Int.negSucc 3), (148, Int.ofNat 3), (150, Int.negSucc 3), (160, Int.negSucc 3), (162,
    Int.ofNat 8), (163, Int.negSucc 7), (164, Int.ofNat 2), (430, Int.negSucc 55), (442, Int.ofNat
    8), (443, Int.ofNat 8), (448, Int.ofNat 8), (463, Int.ofNat 32), (480, Int.negSucc 7), (488,
    Int.negSucc 39), (495, Int.ofNat 16), (510, Int.negSucc 3), (520, Int.negSucc 15), (524,
    Int.ofNat 4), (535, Int.ofNat 12), (547, Int.ofNat 16), (556, Int.ofNat 6), (560, Int.ofNat
    12), (696, Int.ofNat 20), (709, Int.ofNat 16), (746, Int.negSucc 15), (753, Int.negSucc 15),
    (760, Int.ofNat 16), (766, Int.negSucc 15), (774, Int.negSucc 15), (781, Int.ofNat 32), (802,
    Int.ofNat 16), (824, Int.ofNat 16), (832, Int.negSucc 7)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 2), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.ofNat 3), (437, Int.ofNat 6), (498, Int.ofNat
    12)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 4), (159, Int.negSucc 1), (458,
    Int.ofNat 1), (513, Int.ofNat 6), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 3), (172, Int.ofNat 1), (177,
    Int.ofNat 2), (185, Int.ofNat 4), (190, Int.negSucc 3), (481, Int.negSucc 23), (489,
    Int.negSucc 15), (496, Int.ofNat 4), (500, Int.ofNat 24), (511, Int.ofNat 2), (564,
    Int.negSucc 5), (578, Int.ofNat 12), (596, Int.ofNat 4), (710, Int.ofNat 16), (767,
    Int.negSucc 7), (775, Int.negSucc 7), (782, Int.ofNat 8), (825, Int.ofNat 2)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.ofNat 7), (173, Int.negSucc 5), (178,
    Int.ofNat 6), (186, Int.ofNat 12), (191, Int.negSucc 11), (492, Int.negSucc 35), (501,
    Int.ofNat 36), (533, Int.ofNat 12), (548, Int.negSucc 23), (551, Int.ofNat 24), (561,
    Int.ofNat 12), (567, Int.negSucc 17), (581, Int.ofNat 36), (788, Int.negSucc 47), (827,
    Int.ofNat 24)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 4), (473, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

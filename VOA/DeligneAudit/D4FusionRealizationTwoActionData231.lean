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
def actionData231 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (430,
    Int.negSucc 11), (442, Int.ofNat 4), (480, Int.negSucc 11), (488, Int.negSucc 3), (516,
    Int.negSucc 3), (528, Int.ofNat 8), (547, Int.ofNat 4), (766, Int.negSucc 3), (787, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(140, Int.negSucc 0), (491, Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(137, Int.negSucc 1), (141, Int.ofNat 1), (415,
    Int.negSucc 3), (465, Int.negSucc 3), (540, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(142, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (143,
    Int.ofNat 1), (430, Int.negSucc 7), (442, Int.ofNat 4), (480, Int.negSucc 9), (488,
    Int.negSucc 3), (495, Int.ofNat 2), (516, Int.negSucc 3), (528, Int.ofNat 6), (547, Int.ofNat
    4), (550, Int.negSucc 1), (766, Int.negSucc 3), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(144, Int.ofNat 2), (434, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(145, Int.ofNat 1), (498, Int.ofNat 4), (532, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(146, Int.negSucc 0), (469, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(147, Int.negSucc 0), (483, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(136, Int.negSucc 1), (148, Int.negSucc 0), (430,
    Int.negSucc 35), (442, Int.ofNat 4), (443, Int.ofNat 8), (480, Int.negSucc 27), (488,
    Int.negSucc 27), (516, Int.negSucc 3), (520, Int.negSucc 7), (528, Int.ofNat 8), (535,
    Int.ofNat 8), (547, Int.ofNat 20), (696, Int.ofNat 8), (709, Int.ofNat 8), (746, Int.negSucc
    7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766, Int.negSucc 11), (774, Int.negSucc 7),
    (781, Int.ofNat 8), (787, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.negSucc 0), (539,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 9), (139, Int.ofNat 4), (148,
    Int.negSucc 4), (150, Int.ofNat 2), (151, Int.ofNat 2), (430, Int.negSucc 127), (442,
    Int.ofNat 8), (443, Int.ofNat 32), (448, Int.ofNat 24), (480, Int.negSucc 87), (488,
    Int.negSucc 95), (516, Int.negSucc 7), (520, Int.negSucc 31), (524, Int.negSucc 7), (528,
    Int.ofNat 16), (535, Int.ofNat 28), (547, Int.ofNat 72), (550, Int.ofNat 16), (696, Int.ofNat
    32), (709, Int.ofNat 32), (746, Int.negSucc 31), (753, Int.negSucc 31), (760, Int.ofNat 32),
    (766, Int.negSucc 39), (774, Int.negSucc 39), (781, Int.ofNat 32), (787, Int.ofNat 8), (795,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 5), (139, Int.ofNat 4), (148,
    Int.ofNat 1), (150, Int.negSucc 5), (151, Int.ofNat 10), (430, Int.negSucc 119), (443,
    Int.ofNat 16), (448, Int.ofNat 88), (480, Int.negSucc 31), (488, Int.negSucc 39), (495,
    Int.negSucc 31), (520, Int.negSucc 15), (524, Int.negSucc 39), (535, Int.ofNat 12), (547,
    Int.ofNat 32), (550, Int.ofNat 80), (696, Int.ofNat 16), (709, Int.ofNat 16), (746,
    Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 15), (774,
    Int.negSucc 55), (781, Int.ofNat 16), (795, Int.ofNat 40)] },
  { denominator := Int.ofNat 1, terms := [(152, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(153, Int.negSucc 1), (430, Int.negSucc 3), (480,
    Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(154, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(455, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 0), (458, Int.negSucc 0), (513,
    Int.negSucc 0), (531, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(153, Int.negSucc 1), (157, Int.ofNat 1), (430,
    Int.negSucc 1), (480, Int.negSucc 1), (510, Int.negSucc 0), (516, Int.negSucc 0), (560,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(158, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.negSucc 1), (159, Int.ofNat 1), (458,
    Int.negSucc 0), (513, Int.negSucc 1), (531, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 3), (148, Int.ofNat 1), (160,
    Int.negSucc 5), (164, Int.ofNat 1), (430, Int.negSucc 95), (442, Int.ofNat 8), (443, Int.ofNat
    16), (463, Int.ofNat 8), (480, Int.negSucc 55), (488, Int.negSucc 63), (510, Int.negSucc 7),
    (516, Int.negSucc 7), (520, Int.negSucc 19), (528, Int.ofNat 16), (535, Int.ofNat 16), (547,
    Int.ofNat 40), (556, Int.ofNat 4), (560, Int.ofNat 8), (696, Int.ofNat 16), (709, Int.ofNat
    16), (746, Int.negSucc 15), (753, Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23),
    (774, Int.negSucc 15), (781, Int.ofNat 24), (787, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.negSucc 1), (451, Int.negSucc 0), (543,
    Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 3), (148, Int.ofNat 2), (150,
    Int.negSucc 1), (151, Int.ofNat 2), (160, Int.negSucc 5), (162, Int.ofNat 4), (164, Int.ofNat
    1), (430, Int.negSucc 87), (442, Int.ofNat 8), (443, Int.ofNat 16), (448, Int.ofNat 24), (463,
    Int.ofNat 8), (480, Int.negSucc 51), (488, Int.negSucc 55), (495, Int.ofNat 8), (510,
    Int.negSucc 5), (516, Int.negSucc 7), (520, Int.negSucc 19), (524, Int.negSucc 5), (528,
    Int.ofNat 12), (535, Int.ofNat 12), (547, Int.ofNat 40), (550, Int.ofNat 12), (556, Int.ofNat
    3), (560, Int.ofNat 8), (696, Int.ofNat 16), (709, Int.ofNat 16), (746, Int.negSucc 15), (753,
    Int.negSucc 15), (760, Int.ofNat 16), (766, Int.negSucc 23), (774, Int.negSucc 23), (781,
    Int.ofNat 24), (787, Int.ofNat 8), (795, Int.ofNat 8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.negSucc 0), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (150, Int.ofNat 8), (153, Int.negSucc 3), (157, Int.ofNat 4), (162,
    Int.negSucc 3), (430, Int.negSucc 55), (442, Int.ofNat 8), (443, Int.ofNat 8), (448, Int.ofNat
    8), (480, Int.negSucc 47), (488, Int.negSucc 23), (510, Int.negSucc 3), (516, Int.negSucc 9),
    (520, Int.negSucc 7), (524, Int.negSucc 1), (528, Int.ofNat 20), (535, Int.ofNat 4), (547,
    Int.ofNat 24), (550, Int.ofNat 4), (556, Int.ofNat 1), (560, Int.ofNat 2), (696, Int.ofNat 8),
    (709, Int.ofNat 8), (746, Int.negSucc 7), (753, Int.negSucc 7), (760, Int.ofNat 8), (766,
    Int.negSucc 15), (774, Int.negSucc 7), (781, Int.ofNat 8), (787, Int.ofNat 8)] },
  { denominator := Int.ofNat 2, terms := [(148, Int.ofNat 3), (160, Int.negSucc 5), (164,
    Int.ofNat 1), (430, Int.negSucc 23), (463, Int.ofNat 8), (488, Int.negSucc 7), (510,
    Int.negSucc 7), (520, Int.negSucc 3), (556, Int.ofNat 4), (560, Int.ofNat 8), (781, Int.ofNat
    8), (802, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(466, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(477, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(481, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(169, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 0), (470, Int.negSucc 2), (517,
    Int.negSucc 1), (541, Int.negSucc 1), (590, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.negSucc 0), (484, Int.negSucc 0), (545,
    Int.negSucc 1), (593, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 6), (172, Int.ofNat 3), (481,
    Int.negSucc 31), (489, Int.negSucc 11), (500, Int.ofNat 20), (564, Int.negSucc 3), (578,
    Int.ofNat 8), (596, Int.ofNat 4), (710, Int.ofNat 8), (767, Int.negSucc 3), (775, Int.negSucc
    3), (782, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 1), (173, Int.negSucc 0), (492,
    Int.negSucc 5), (501, Int.ofNat 2), (548, Int.negSucc 3), (567, Int.negSucc 1), (581,
    Int.ofNat 4), (788, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.negSucc 1), (174, Int.ofNat 1), (470,
    Int.negSucc 3), (517, Int.negSucc 3), (541, Int.negSucc 3), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.ofNat 2), (473, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 14), (172, Int.ofNat 5), (177,
    Int.ofNat 4), (481, Int.negSucc 67), (489, Int.negSucc 27), (496, Int.ofNat 4), (500,
    Int.ofNat 52), (564, Int.negSucc 11), (578, Int.ofNat 16), (596, Int.ofNat 12), (710,
    Int.ofNat 24), (767, Int.negSucc 11), (775, Int.negSucc 11), (782, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.ofNat 2), (173, Int.negSucc 1), (178,
    Int.ofNat 1), (492, Int.negSucc 7), (501, Int.ofNat 4), (533, Int.ofNat 2), (548, Int.negSucc
    7), (551, Int.ofNat 4), (567, Int.negSucc 3), (581, Int.ofNat 6), (788, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.ofNat 2), (499, Int.ofNat 4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

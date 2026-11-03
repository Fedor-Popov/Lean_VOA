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
def actionData354 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 17), (139, Int.negSucc 5), (148,
    Int.ofNat 5), (430, Int.ofNat 216), (442, Int.negSucc 39), (443, Int.negSucc 79), (480,
    Int.ofNat 168), (488, Int.ofNat 168), (516, Int.ofNat 24), (520, Int.ofNat 60), (528,
    Int.negSucc 47), (535, Int.negSucc 59), (547, Int.negSucc 127), (696, Int.negSucc 99), (709,
    Int.negSucc 79), (746, Int.ofNat 80), (753, Int.ofNat 80), (760, Int.negSucc 79), (766,
    Int.ofNat 112), (774, Int.ofNat 80), (781, Int.negSucc 79), (787, Int.negSucc 31), (824,
    Int.negSucc 55), (826, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(149, Int.ofNat 1), (418, Int.ofNat 4), (472, Int.ofNat
    2), (539, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 21), (139, Int.negSucc 7), (148,
    Int.ofNat 2), (150, Int.ofNat 8), (151, Int.negSucc 3), (430, Int.ofNat 304), (442,
    Int.negSucc 39), (443, Int.negSucc 95), (448, Int.negSucc 39), (480, Int.ofNat 192), (488,
    Int.ofNat 208), (495, Int.ofNat 40), (516, Int.ofNat 24), (520, Int.ofNat 72), (524, Int.ofNat
    24), (528, Int.negSucc 47), (535, Int.negSucc 75), (547, Int.negSucc 151), (550, Int.negSucc
    47), (696, Int.negSucc 119), (709, Int.negSucc 95), (746, Int.ofNat 96), (753, Int.ofNat 96),
    (760, Int.negSucc 95), (766, Int.ofNat 128), (774, Int.ofNat 128), (781, Int.negSucc 95),
    (787, Int.negSucc 31), (795, Int.negSucc 31), (824, Int.negSucc 79), (826, Int.ofNat 16),
    (829, Int.ofNat 16)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 4), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (150, Int.ofNat 12), (151, Int.negSucc 7), (430, Int.ofNat 136), (443,
    Int.negSucc 15), (448, Int.negSucc 87), (480, Int.ofNat 24), (488, Int.ofNat 40), (495,
    Int.ofNat 72), (520, Int.ofNat 12), (524, Int.ofNat 48), (535, Int.negSucc 15), (547,
    Int.negSucc 23), (550, Int.negSucc 95), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 16), (774,
    Int.ofNat 80), (781, Int.negSucc 15), (795, Int.negSucc 63), (824, Int.negSucc 39), (829,
    Int.ofNat 32)] },
  { denominator := Int.ofNat 2, terms := [(138, Int.ofNat 1), (425, Int.ofNat 3), (476, Int.ofNat
    4), (544, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 1), (139, Int.ofNat 4), (148,
    Int.negSucc 2), (160, Int.ofNat 6), (164, Int.negSucc 0), (430, Int.ofNat 64), (442,
    Int.negSucc 15), (463, Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 16), (510,
    Int.ofNat 12), (516, Int.ofNat 12), (520, Int.ofNat 4), (528, Int.negSucc 23), (547,
    Int.negSucc 7), (556, Int.negSucc 5), (560, Int.negSucc 11), (766, Int.ofNat 16), (781,
    Int.negSucc 15), (787, Int.negSucc 15), (802, Int.negSucc 15), (824, Int.negSucc 15), (826,
    Int.ofNat 8), (832, Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(161, Int.ofNat 2), (451, Int.ofNat 3), (505, Int.ofNat
    2), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.negSucc 0), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 1), (458, Int.ofNat 1), (531, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(148, Int.ofNat 2), (150, Int.negSucc 3), (153,
    Int.ofNat 4), (157, Int.negSucc 3), (162, Int.ofNat 4), (430, Int.ofNat 16), (480, Int.ofNat
    8), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 2), (524, Int.ofNat 2), (528,
    Int.negSucc 3), (550, Int.negSucc 3), (556, Int.negSucc 0), (560, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(145, Int.ofNat 1), (437, Int.ofNat 4), (498, Int.ofNat
    4), (532, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(156, Int.ofNat 1), (458, Int.ofNat 1), (513, Int.ofNat
    1), (531, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 21), (139, Int.negSucc 7), (148,
    Int.ofNat 2), (160, Int.ofNat 8), (164, Int.negSucc 1), (430, Int.ofNat 304), (442,
    Int.negSucc 39), (443, Int.negSucc 95), (463, Int.negSucc 39), (480, Int.ofNat 192), (488,
    Int.ofNat 208), (510, Int.ofNat 20), (516, Int.ofNat 24), (520, Int.ofNat 76), (528,
    Int.negSucc 47), (535, Int.negSucc 71), (547, Int.negSucc 151), (556, Int.negSucc 11), (560,
    Int.negSucc 23), (696, Int.negSucc 119), (709, Int.negSucc 95), (746, Int.ofNat 96), (753,
    Int.ofNat 96), (760, Int.negSucc 95), (766, Int.ofNat 128), (774, Int.ofNat 96), (781,
    Int.negSucc 127), (787, Int.negSucc 31), (802, Int.negSucc 31), (824, Int.negSucc 79), (826,
    Int.ofNat 16), (832, Int.ofNat 16)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 1), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 6), (148, Int.negSucc 14), (150,
    Int.ofNat 28), (151, Int.negSucc 11), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 304), (442, Int.negSucc 15), (443, Int.negSucc 31), (448, Int.negSucc 111), (463,
    Int.negSucc 15), (480, Int.ofNat 80), (488, Int.ofNat 112), (495, Int.ofNat 128), (510,
    Int.ofNat 12), (516, Int.ofNat 12), (520, Int.ofNat 28), (524, Int.ofNat 72), (528,
    Int.negSucc 23), (535, Int.negSucc 39), (547, Int.negSucc 55), (550, Int.negSucc 143), (556,
    Int.negSucc 5), (560, Int.negSucc 11), (696, Int.negSucc 39), (709, Int.negSucc 31), (746,
    Int.ofNat 32), (753, Int.ofNat 32), (760, Int.negSucc 31), (766, Int.ofNat 48), (774,
    Int.ofNat 128), (781, Int.negSucc 47), (787, Int.negSucc 15), (795, Int.negSucc 95), (802,
    Int.negSucc 15), (824, Int.negSucc 79), (826, Int.ofNat 8), (829, Int.ofNat 48), (832,
    Int.ofNat 8)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 12), (139, Int.negSucc 9), (148,
    Int.ofNat 11), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 4), (430, Int.ofNat 168), (442,
    Int.negSucc 47), (443, Int.negSucc 39), (448, Int.negSucc 7), (463, Int.negSucc 7), (480,
    Int.ofNat 120), (488, Int.ofNat 88), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat
    28), (520, Int.ofNat 32), (524, Int.ofNat 4), (528, Int.negSucc 55), (535, Int.negSucc 31),
    (547, Int.negSucc 71), (550, Int.negSucc 7), (556, Int.negSucc 1), (560, Int.negSucc 3), (696,
    Int.negSucc 59), (709, Int.negSucc 47), (746, Int.ofNat 48), (753, Int.ofNat 48), (760,
    Int.negSucc 47), (766, Int.ofNat 80), (774, Int.ofNat 48), (781, Int.negSucc 47), (787,
    Int.negSucc 31), (824, Int.negSucc 39), (826, Int.ofNat 16)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 4), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (160, Int.ofNat 12), (164, Int.negSucc 3), (430, Int.ofNat 136), (443,
    Int.negSucc 15), (463, Int.negSucc 87), (480, Int.ofNat 24), (488, Int.ofNat 40), (510,
    Int.ofNat 36), (520, Int.ofNat 16), (535, Int.negSucc 11), (547, Int.negSucc 23), (556,
    Int.negSucc 23), (560, Int.negSucc 47), (696, Int.negSucc 19), (709, Int.negSucc 15), (746,
    Int.ofNat 16), (753, Int.ofNat 16), (760, Int.negSucc 15), (766, Int.ofNat 16), (774,
    Int.ofNat 16), (781, Int.negSucc 79), (802, Int.negSucc 63), (824, Int.negSucc 39), (832,
    Int.ofNat 32)] },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0)] }
]

end VOA.DeligneAudit.D4Two.Certificate

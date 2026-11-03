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
def actionData165 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(492, Int.negSucc 0), (561, Int.ofNat 1), (742,
    Int.negSucc 3), (754, Int.negSucc 3), (761, Int.ofNat 2), (827, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(562, Int.ofNat 1), (783, Int.negSucc 1), (828,
    Int.ofNat 1)] },
  { denominator := Int.ofNat 3, terms := [(584, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(576, Int.negSucc 0), (592, Int.ofNat 2), (805,
    Int.negSucc 1), (836, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(589, Int.negSucc 0), (595, Int.ofNat 2), (798,
    Int.ofNat 2), (835, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(301, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(678, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(679, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(681, Int.negSucc 1), (683, Int.negSucc 0), (689,
    Int.ofNat 2), (812, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(682, Int.negSucc 0), (813, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(684, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(685, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(685, Int.negSucc 1), (814, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(814, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(692, Int.ofNat 1), (816, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(817, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(814, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(693, Int.ofNat 1), (819, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(820, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(696, Int.negSucc 0), (824, Int.ofNat 4), (829,
    Int.negSucc 1), (832, Int.negSucc 3), (840, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(827, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(828, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(685, Int.negSucc 0), (814, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(0, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(1, Int.ofNat 1), (300, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(1, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(1, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(1, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(1, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(2, Int.ofNat 2), (303, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(4, Int.ofNat 2), (302, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(5, Int.ofNat 2), (301, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(5, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(2, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(4, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(3, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 2), (311, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(7, Int.ofNat 4), (306, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 2), (311, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(8, Int.ofNat 4), (305, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 2), (311, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(9, Int.ofNat 1), (310, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1), (310, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(11, Int.ofNat 4), (304, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 2), (311, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1), (310, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1), (309, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(10, Int.ofNat 1), (309, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(6, Int.ofNat 2), (311, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 1), (310, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(10, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(9, Int.ofNat 2), (310, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(10, Int.ofNat 1), (309, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(15, Int.ofNat 2), (314, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 4), (313, Int.negSucc 3), (337, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(15, Int.ofNat 4), (314, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(16, Int.ofNat 8), (307, Int.ofNat 8)] },
  { denominator := Int.ofNat 1, terms := [(12, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 2), (15, Int.ofNat 2), (314, Int.negSucc
    3), (330, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 2), (17, Int.ofNat 2), (313, Int.negSucc
    3), (337, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(17, Int.ofNat 2), (313, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1), (312, Int.ofNat 2), (336, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(20, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 2), (15, Int.ofNat 2), (314, Int.negSucc
    3), (318, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(18, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1), (21, Int.ofNat 2), (312, Int.ofNat
    4), (336, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 2), (17, Int.ofNat 1), (313, Int.negSucc
    2), (317, Int.negSucc 0), (337, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(19, Int.ofNat 1), (21, Int.ofNat 1), (312, Int.ofNat
    3), (329, Int.negSucc 0), (336, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(13, Int.ofNat 1), (15, Int.ofNat 1), (314, Int.negSucc
    1)] },
  { denominator := Int.ofNat 1, terms := [(14, Int.ofNat 3), (313, Int.negSucc 2), (337, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(19, Int.ofNat 3), (312, Int.ofNat 6), (336, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(21, Int.ofNat 4), (312, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(24, Int.ofNat 4), (326, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(24, Int.ofNat 4), (326, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(29, Int.ofNat 4), (315, Int.ofNat 4), (340, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(24, Int.ofNat 2), (326, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(27, Int.ofNat 2), (325, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(28, Int.ofNat 6), (339, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(22, Int.ofNat 2), (321, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(25, Int.ofNat 2), (333, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(29, Int.ofNat 4), (30, Int.ofNat 4), (308, Int.ofNat
    4), (315, Int.ofNat 8), (340, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(23, Int.ofNat 1), (320, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(29, Int.ofNat 2), (30, Int.ofNat 2), (31, Int.ofNat 2),
    (308, Int.ofNat 2), (315, Int.ofNat 6), (332, Int.negSucc 1), (340, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(27, Int.ofNat 6), (325, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(27, Int.ofNat 4), (325, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(24, Int.ofNat 2), (326, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(33, Int.ofNat 1), (324, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(34, Int.ofNat 3), (338, Int.ofNat 12)] },
  { denominator := Int.ofNat 2, terms := [(326, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(325, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(324, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(29, Int.ofNat 2), (30, Int.ofNat 2), (35, Int.ofNat 2),
    (308, Int.ofNat 2), (315, Int.ofNat 6), (319, Int.ofNat 2), (340, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(32, Int.ofNat 1), (331, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 3), (324, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(27, Int.ofNat 4), (325, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 2), (324, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(29, Int.ofNat 2), (30, Int.ofNat 1), (308, Int.negSucc
    0), (315, Int.ofNat 3), (340, Int.negSucc 1), (348, Int.ofNat 1), (353, Int.ofNat 1), (368,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(33, Int.ofNat 4), (324, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 8), (327, Int.ofNat 4), (365, Int.negSucc
    3)] },
  { denominator := Int.ofNat 1, terms := [(36, Int.ofNat 1), (345, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(41, Int.ofNat 2), (360, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.ofNat 4), (48, Int.ofNat 2), (316, Int.ofNat
    2), (327, Int.ofNat 4), (365, Int.negSucc 2)] },
  { denominator := Int.ofNat 1, terms := [(49, Int.ofNat 6), (341, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [(345, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(344, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(44, Int.negSucc 1), (46, Int.ofNat 2), (48, Int.ofNat
    2), (327, Int.ofNat 1), (408, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(47, Int.ofNat 4), (364, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(50, Int.ofNat 4), (322, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(51, Int.ofNat 4), (334, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 7), (48, Int.ofNat 12), (316, Int.ofNat
    12), (327, Int.ofNat 8), (365, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(39, Int.ofNat 1), (344, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 5), (46, Int.ofNat 2), (48, Int.ofNat
    8), (316, Int.ofNat 8), (327, Int.ofNat 6), (359, Int.negSucc 0), (365, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 1), (46, Int.ofNat 6), (48, Int.ofNat
    2), (316, Int.ofNat 2), (327, Int.ofNat 4), (359, Int.negSucc 2)] },
  { denominator := Int.ofNat 2, terms := [(360, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(44, Int.negSucc 1), (48, Int.ofNat 2), (54, Int.ofNat
    1), (327, Int.ofNat 1), (392, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(358, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(55, Int.ofNat 1), (363, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 0), (44, Int.negSucc 0), (48, Int.ofNat
    1), (316, Int.negSucc 1), (386, Int.ofNat 1), (392, Int.ofNat 1), (408, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(364, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(363, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 5), (48, Int.ofNat 8), (54, Int.ofNat
    1), (316, Int.ofNat 8), (327, Int.ofNat 6), (343, Int.ofNat 2), (365, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(52, Int.ofNat 1), (358, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(42, Int.negSucc 5), (44, Int.negSucc 3), (46, Int.ofNat
    8), (48, Int.ofNat 8), (54, Int.ofNat 1), (316, Int.ofNat 4), (327, Int.ofNat 6), (359,
    Int.negSucc 1), (386, Int.ofNat 2), (408, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 1), (48, Int.ofNat 4), (316, Int.ofNat
    2), (327, Int.ofNat 3), (365, Int.negSucc 0), (386, Int.ofNat 1), (392, Int.ofNat 1), (408,
    Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(42, Int.negSucc 3), (48, Int.ofNat 4), (54, Int.ofNat
    6), (316, Int.ofNat 4), (327, Int.ofNat 8), (343, Int.ofNat 12)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 4), (328, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 12), (366, Int.ofNat 12), (405,
    Int.negSucc 5)] },
  { denominator := Int.ofNat 1, terms := [(378, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(59, Int.negSucc 0), (72, Int.ofNat 2), (346, Int.ofNat
    2), (383, Int.negSucc 1), (394, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(66, Int.negSucc 0), (73, Int.ofNat 2), (361, Int.ofNat
    1), (402, Int.negSucc 0), (410, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 12), (328, Int.ofNat 6)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.ofNat 4), (74, Int.ofNat 4), (342, Int.ofNat
    4), (366, Int.ofNat 10), (405, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (68, Int.negSucc 1), (72, Int.ofNat
    2), (323, Int.negSucc 3), (346, Int.ofNat 2), (373, Int.ofNat 1), (377, Int.negSucc 1), (383,
    Int.negSucc 1), (388, Int.ofNat 2), (394, Int.ofNat 2), (459, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(382, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 6), (328, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 1), (70, Int.negSucc 3), (71, Int.ofNat
    4), (74, Int.ofNat 4), (366, Int.ofNat 2), (401, Int.negSucc 1), (409, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 1), (72, Int.ofNat 4), (323, Int.ofNat
    4), (346, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(63, Int.negSucc 3), (73, Int.ofNat 4), (335, Int.ofNat
    4), (361, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 0), (59, Int.negSucc 0), (61, Int.ofNat
    1), (72, Int.ofNat 2), (346, Int.ofNat 2), (377, Int.negSucc 1), (388, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(63, Int.negSucc 7), (66, Int.negSucc 2), (69, Int.ofNat
    4), (73, Int.ofNat 10), (335, Int.ofNat 8), (361, Int.ofNat 7), (397, Int.negSucc 0), (402,
    Int.negSucc 0), (410, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.negSucc 3), (69, Int.negSucc 3), (73, Int.ofNat
    4), (335, Int.negSucc 7), (361, Int.ofNat 2), (376, Int.ofNat 4), (387, Int.negSucc 3), (397,
    Int.negSucc 0), (402, Int.negSucc 1), (410, Int.ofNat 4), (444, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(64, Int.ofNat 6), (328, Int.ofNat 3)] },
  { denominator := Int.ofNat 1, terms := [(65, Int.negSucc 0), (70, Int.negSucc 1), (74, Int.ofNat
    2), (77, Int.ofNat 1), (366, Int.ofNat 1), (381, Int.ofNat 2), (393, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(400, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(64, Int.ofNat 1), (328, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.negSucc 3), (70, Int.negSucc 3), (74, Int.ofNat
    4), (342, Int.negSucc 7), (366, Int.ofNat 2), (381, Int.ofNat 4), (393, Int.negSucc 3), (401,
    Int.negSucc 1), (405, Int.negSucc 0), (409, Int.ofNat 4), (438, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(57, Int.negSucc 3), (59, Int.negSucc 2), (68, Int.ofNat
    4), (72, Int.ofNat 10), (323, Int.ofNat 8), (346, Int.ofNat 14), (373, Int.ofNat 2), (383,
    Int.negSucc 1), (394, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(63, Int.negSucc 11), (66, Int.negSucc 3), (73,
    Int.ofNat 16), (75, Int.ofNat 1), (335, Int.ofNat 8), (361, Int.ofNat 8), (376, Int.ofNat 4),
    (387, Int.negSucc 3), (402, Int.negSucc 1), (410, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(78, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 1), (91, Int.ofNat 4), (432, Int.ofNat
    4)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 3), (92, Int.ofNat 4), (453, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 8), (367, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(94, Int.ofNat 16), (406, Int.ofNat 24)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.negSucc 1), (82, Int.ofNat 1), (85, Int.negSucc
    1), (95, Int.negSucc 1), (101, Int.ofNat 4), (352, Int.negSucc 7), (379, Int.ofNat 8), (389,
    Int.negSucc 3), (413, Int.ofNat 2), (423, Int.negSucc 1), (428, Int.negSucc 7), (446,
    Int.ofNat 4), (461, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (91, Int.ofNat 4), (347, Int.ofNat
    2), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 0), (86, Int.negSucc 1), (102,
    Int.ofNat 4), (384, Int.ofNat 4), (395, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 1), (92, Int.ofNat 4), (362, Int.ofNat
    1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(90, Int.negSucc 1), (97, Int.negSucc 1), (103,
    Int.ofNat 4), (403, Int.ofNat 2), (411, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 20), (367, Int.ofNat 10)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (91, Int.ofNat 2), (347, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(81, Int.negSucc 1), (98, Int.negSucc 3), (102,
    Int.ofNat 4), (357, Int.negSucc 7), (384, Int.ofNat 8), (395, Int.negSucc 3), (416, Int.ofNat
    2), (427, Int.negSucc 7), (435, Int.negSucc 1), (440, Int.ofNat 4), (460, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(80, Int.negSucc 0), (91, Int.ofNat 2), (420, Int.ofNat
    2)] },
  { denominator := Int.ofNat 2, terms := [(88, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(89, Int.negSucc 1), (92, Int.ofNat 8), (362, Int.ofNat
    3), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(93, Int.ofNat 9), (100, Int.negSucc 0), (367, Int.ofNat
    3), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(84, Int.ofNat 4), (374, Int.ofNat 4)] },
  { denominator := Int.ofNat 1, terms := [(79, Int.negSucc 1), (82, Int.negSucc 0), (101,
    Int.ofNat 4), (379, Int.ofNat 4), (389, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(96, Int.ofNat 4), (398, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (92, Int.ofNat 2), (362, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(90, Int.negSucc 3), (99, Int.negSucc 3), (103,
    Int.ofNat 4), (372, Int.negSucc 7), (403, Int.ofNat 4), (411, Int.negSucc 3), (426, Int.ofNat
    8), (439, Int.negSucc 3), (445, Int.negSucc 3), (449, Int.negSucc 0), (456, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.negSucc 0), (91, Int.ofNat 8), (347, Int.ofNat
    6), (432, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 3), (92, Int.ofNat 6), (362, Int.ofNat
    1), (419, Int.negSucc 1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 9), (100, Int.negSucc 0), (367, Int.ofNat
    3), (431, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(105, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 5), (100, Int.negSucc 0), (367, Int.ofNat
    2)] }
]

end VOA.DeligneAudit.D4Two.Certificate

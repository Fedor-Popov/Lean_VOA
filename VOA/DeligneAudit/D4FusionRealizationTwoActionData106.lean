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
def actionData106 : List ActionCase := [
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 9), (139, Int.negSucc 7), (148,
    Int.ofNat 2), (160, Int.ofNat 8), (164, Int.negSucc 1), (430, Int.ofNat 144), (442,
    Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 64), (488, Int.ofNat 112), (510,
    Int.ofNat 4), (516, Int.ofNat 8), (520, Int.ofNat 28), (528, Int.negSucc 15), (535,
    Int.negSucc 23), (547, Int.negSucc 55), (556, Int.negSucc 3), (560, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(161, Int.ofNat 1), (451, Int.ofNat 2), (505, Int.ofNat
    1), (543, Int.ofNat 4)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 2), (148, Int.negSucc 14), (150,
    Int.ofNat 28), (151, Int.negSucc 11), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.ofNat 144), (448, Int.negSucc 15), (480, Int.ofNat 32), (488, Int.ofNat 80), (495,
    Int.ofNat 32), (510, Int.ofNat 4), (516, Int.ofNat 4), (520, Int.ofNat 12), (524, Int.ofNat
    24), (528, Int.negSucc 7), (535, Int.negSucc 23), (547, Int.negSucc 23), (550, Int.negSucc
    47), (556, Int.negSucc 1), (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 4, terms := [(136, Int.ofNat 6), (139, Int.negSucc 9), (148,
    Int.ofNat 11), (150, Int.negSucc 11), (153, Int.ofNat 8), (157, Int.negSucc 7), (160,
    Int.negSucc 3), (162, Int.ofNat 8), (163, Int.ofNat 4), (430, Int.ofNat 88), (442, Int.negSucc
    15), (443, Int.ofNat 8), (448, Int.negSucc 7), (463, Int.negSucc 7), (480, Int.ofNat 40),
    (488, Int.ofNat 40), (495, Int.ofNat 8), (510, Int.ofNat 4), (516, Int.ofNat 12), (520,
    Int.ofNat 8), (524, Int.ofNat 4), (528, Int.negSucc 23), (535, Int.negSucc 7), (547,
    Int.negSucc 23), (550, Int.negSucc 7), (556, Int.negSucc 1), (560, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(136, Int.ofNat 2), (139, Int.negSucc 1), (148,
    Int.negSucc 4), (160, Int.ofNat 12), (164, Int.negSucc 3), (430, Int.ofNat 56), (463,
    Int.negSucc 23), (480, Int.ofNat 8), (488, Int.ofNat 24), (510, Int.ofNat 4), (520, Int.ofNat
    8), (535, Int.negSucc 3), (547, Int.negSucc 7), (556, Int.negSucc 7), (560, Int.negSucc 15)]
    },
  { denominator := Int.ofNat 1, terms := [(165, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(166, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.negSucc 0), (481, Int.ofNat 8), (489,
    Int.ofNat 4), (500, Int.negSucc 3), (564, Int.ofNat 2), (578, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(168, Int.negSucc 0), (492, Int.ofNat 12), (501,
    Int.negSucc 11), (567, Int.ofNat 6), (581, Int.negSucc 11)] },
  { denominator := Int.ofNat 2, terms := [(169, Int.ofNat 2), (467, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 3), (180, Int.ofNat 3), (192,
    Int.negSucc 0), (470, Int.ofNat 12), (517, Int.ofNat 4), (521, Int.ofNat 4), (541, Int.ofNat
    8), (585, Int.negSucc 1), (590, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 3), (181, Int.ofNat 3), (183,
    Int.negSucc 0), (484, Int.ofNat 12), (529, Int.ofNat 8), (536, Int.ofNat 4), (545, Int.ofNat
    8), (573, Int.ofNat 2), (593, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(167, Int.ofNat 5), (172, Int.negSucc 2), (481,
    Int.ofNat 40), (489, Int.ofNat 24), (500, Int.negSucc 27), (564, Int.ofNat 8), (578,
    Int.negSucc 15), (596, Int.negSucc 3)] },
  { denominator := Int.ofNat 3, terms := [(168, Int.negSucc 6), (173, Int.ofNat 6), (492,
    Int.ofNat 42), (501, Int.negSucc 23), (533, Int.ofNat 6), (548, Int.ofNat 12), (567, Int.ofNat
    18), (581, Int.negSucc 35)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 1), (182, Int.ofNat 1), (470, Int.ofNat
    5), (517, Int.ofNat 2), (525, Int.ofNat 1), (541, Int.ofNat 4), (585, Int.negSucc 0), (590,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(175, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(176, Int.ofNat 1), (474, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 13), (172, Int.negSucc 4), (177,
    Int.negSucc 3), (481, Int.ofNat 80), (489, Int.ofNat 48), (496, Int.ofNat 8), (500,
    Int.negSucc 59), (564, Int.ofNat 16), (578, Int.negSucc 23), (596, Int.negSucc 11)] },
  { denominator := Int.ofNat 6, terms := [(168, Int.negSucc 4), (173, Int.ofNat 6), (178,
    Int.ofNat 6), (492, Int.ofNat 36), (533, Int.ofNat 12), (548, Int.ofNat 24), (567, Int.ofNat
    6), (581, Int.negSucc 23)] },
  { denominator := Int.ofNat 1, terms := [(179, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [(170, Int.ofNat 2), (180, Int.ofNat 6), (192,
    Int.negSucc 1), (470, Int.ofNat 14), (517, Int.ofNat 4), (521, Int.ofNat 6), (541, Int.ofNat
    8), (585, Int.negSucc 3), (590, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 2), (181, Int.ofNat 6), (183,
    Int.negSucc 1), (484, Int.ofNat 14), (529, Int.ofNat 8), (536, Int.ofNat 6), (545, Int.ofNat
    8), (573, Int.ofNat 4), (593, Int.negSucc 7)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 1), (180, Int.ofNat 3), (182, Int.ofNat
    2), (192, Int.negSucc 0), (470, Int.ofNat 12), (517, Int.ofNat 2), (521, Int.ofNat 4), (541,
    Int.ofNat 8), (585, Int.negSucc 3), (590, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(171, Int.ofNat 13), (181, Int.ofNat 31), (183,
    Int.negSucc 10), (484, Int.ofNat 80), (503, Int.negSucc 7), (529, Int.ofNat 48), (536,
    Int.ofNat 36), (545, Int.ofNat 40), (573, Int.ofNat 22), (593, Int.negSucc 47)] },
  { denominator := Int.ofNat 4, terms := [(181, Int.negSucc 1), (193, Int.ofNat 2), (484,
    Int.ofNat 10), (529, Int.ofNat 8), (545, Int.ofNat 8), (557, Int.ofNat 1), (573, Int.ofNat 2),
    (593, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(167, Int.ofNat 13), (172, Int.negSucc 4), (185,
    Int.negSucc 7), (481, Int.ofNat 80), (489, Int.ofNat 48), (500, Int.negSucc 59), (511,
    Int.ofNat 4), (564, Int.ofNat 12), (578, Int.negSucc 31), (596, Int.negSucc 11)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 4), (173, Int.ofNat 6), (186,
    Int.ofNat 12), (492, Int.ofNat 36), (533, Int.ofNat 12), (548, Int.ofNat 24), (567, Int.ofNat
    12), (581, Int.negSucc 11)] },
  { denominator := Int.ofNat 1, terms := [(187, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(188, Int.ofNat 4), (507, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 5), (172, Int.negSucc 1), (190,
    Int.negSucc 3), (481, Int.ofNat 24), (489, Int.ofNat 16), (500, Int.negSucc 19), (564,
    Int.ofNat 4), (578, Int.negSucc 7), (596, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(178, Int.ofNat 1), (186, Int.ofNat 2), (492, Int.ofNat
    6), (533, Int.ofNat 4), (551, Int.ofNat 4), (561, Int.ofNat 2), (567, Int.ofNat 1), (581,
    Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(170, Int.ofNat 13), (180, Int.ofNat 31), (192,
    Int.negSucc 10), (470, Int.ofNat 80), (502, Int.negSucc 7), (517, Int.ofNat 24), (521,
    Int.ofNat 36), (541, Int.ofNat 40), (585, Int.negSucc 21), (590, Int.negSucc 47)] },
  { denominator := Int.ofNat 1, terms := [(171, Int.ofNat 3), (181, Int.ofNat 8), (183,
    Int.negSucc 2), (193, Int.ofNat 1), (484, Int.ofNat 26), (529, Int.ofNat 14), (536, Int.ofNat
    10), (545, Int.ofNat 16), (573, Int.ofNat 7), (593, Int.negSucc 13)] },
  { denominator := Int.ofNat 1, terms := [(194, Int.negSucc 0), (515, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(195, Int.negSucc 1), (201, Int.ofNat 3), (217,
    Int.negSucc 1), (522, Int.ofNat 2), (565, Int.ofNat 2), (618, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(196, Int.negSucc 1), (203, Int.ofNat 3), (210,
    Int.negSucc 0), (537, Int.ofNat 2), (579, Int.ofNat 4), (605, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(197, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(198, Int.negSucc 0), (534, Int.ofNat 12), (549,
    Int.ofNat 8), (555, Int.negSucc 7), (608, Int.ofNat 4), (621, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(199, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(200, Int.ofNat 2), (213, Int.ofNat 1), (519, Int.ofNat
    4), (574, Int.ofNat 2), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.negSucc 1), (201, Int.ofNat 5), (217,
    Int.negSucc 5), (518, Int.ofNat 8), (522, Int.ofNat 12), (542, Int.ofNat 8), (553, Int.negSucc
    7), (565, Int.ofNat 16), (618, Int.negSucc 11), (628, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.ofNat 2), (523, Int.ofNat 3), (591, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.negSucc 1), (203, Int.ofNat 5), (210,
    Int.negSucc 2), (530, Int.ofNat 16), (537, Int.ofNat 12), (546, Int.ofNat 8), (554,
    Int.negSucc 7), (579, Int.ofNat 32), (605, Int.ofNat 6), (631, Int.negSucc 7)] },
  { denominator := Int.ofNat 1, terms := [(204, Int.ofNat 2), (538, Int.ofNat 3), (594, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.negSucc 7), (205, Int.ofNat 1), (534,
    Int.ofNat 56), (549, Int.ofNat 56), (555, Int.negSucc 43), (597, Int.ofNat 4), (608, Int.ofNat
    24), (621, Int.negSucc 47)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.negSucc 2), (201, Int.ofNat 6), (208,
    Int.negSucc 1), (217, Int.negSucc 3), (522, Int.ofNat 10), (526, Int.negSucc 1), (565,
    Int.ofNat 10), (618, Int.negSucc 3), (628, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(202, Int.ofNat 1), (207, Int.ofNat 1), (523, Int.ofNat
    3), (591, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(195, Int.negSucc 0), (201, Int.ofNat 3), (208,
    Int.negSucc 1), (217, Int.negSucc 1), (518, Int.ofNat 2), (522, Int.ofNat 6), (565, Int.ofNat
    8), (628, Int.negSucc 3)] },
  { denominator := Int.ofNat 1, terms := [(209, Int.negSucc 0), (527, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.negSucc 1), (203, Int.ofNat 7), (210,
    Int.negSucc 4), (530, Int.ofNat 32), (537, Int.ofNat 16), (546, Int.ofNat 24), (554,
    Int.negSucc 15), (579, Int.ofNat 56), (605, Int.ofNat 10), (631, Int.negSucc 15)] },
  { denominator := Int.ofNat 4, terms := [(198, Int.negSucc 14), (205, Int.ofNat 6), (211,
    Int.negSucc 3), (534, Int.ofNat 24), (549, Int.ofNat 48), (555, Int.negSucc 23), (597,
    Int.ofNat 8), (608, Int.ofNat 20), (621, Int.negSucc 31)] },
  { denominator := Int.ofNat 1, terms := [(212, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(213, Int.ofNat 2), (519, Int.ofNat 4), (574, Int.ofNat
    2), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 1, terms := [(214, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(196, Int.negSucc 2), (203, Int.ofNat 8), (210,
    Int.negSucc 1), (218, Int.negSucc 3), (537, Int.ofNat 10), (558, Int.negSucc 0), (579,
    Int.ofNat 20), (605, Int.ofNat 2), (631, Int.negSucc 3)] }
]

end VOA.DeligneAudit.D4Two.Certificate

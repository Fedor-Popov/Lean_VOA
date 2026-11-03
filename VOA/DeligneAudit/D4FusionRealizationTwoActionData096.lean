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
def actionData096 : List ActionCase := [
  { denominator := Int.ofNat 2, terms := [(298, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(298, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(298, Int.negSucc 0)] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 4, terms := [(298, Int.negSucc 0)] },
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
  { denominator := Int.ofNat 2, terms := [(299, Int.negSucc 0)] },
  { denominator := Int.ofNat 2, terms := [(299, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(299, Int.negSucc 0)] },
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
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 1, terms := [] },
  { denominator := Int.ofNat 2, terms := [(42, Int.ofNat 2), (44, Int.negSucc 3), (46, Int.ofNat
    2), (54, Int.ofNat 1), (316, Int.negSucc 3), (327, Int.negSucc 1), (343, Int.negSucc 1), (359,
    Int.ofNat 1), (365, Int.ofNat 1), (386, Int.ofNat 2), (392, Int.ofNat 2), (408, Int.negSucc
    1)] },
  { denominator := Int.ofNat 2, terms := [(65, Int.ofNat 2), (70, Int.negSucc 3), (71, Int.ofNat
    2), (77, Int.ofNat 1), (342, Int.negSucc 3), (366, Int.negSucc 0), (393, Int.negSucc 1), (409,
    Int.ofNat 2), (438, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(63, Int.ofNat 4), (66, Int.negSucc 3), (75, Int.ofNat
    1), (335, Int.negSucc 7), (361, Int.negSucc 1), (387, Int.negSucc 3), (410, Int.ofNat 4),
    (444, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(57, Int.negSucc 0), (59, Int.ofNat 2), (61, Int.negSucc
    0), (323, Int.ofNat 4), (346, Int.ofNat 2), (388, Int.negSucc 1), (394, Int.negSucc 1), (459,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(90, Int.negSucc 3), (97, Int.ofNat 4), (104,
    Int.negSucc 0), (372, Int.ofNat 8), (411, Int.ofNat 4), (426, Int.negSucc 3), (439, Int.ofNat
    4), (445, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(81, Int.ofNat 1), (86, Int.negSucc 1), (87, Int.ofNat
    1), (357, Int.negSucc 3), (395, Int.negSucc 1), (427, Int.negSucc 1), (440, Int.ofNat 2),
    (460, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(79, Int.ofNat 1), (82, Int.negSucc 0), (352,
    Int.negSucc 3), (389, Int.negSucc 1), (428, Int.negSucc 1), (446, Int.ofNat 2), (461,
    Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(108, Int.negSucc 0), (115, Int.ofNat 1), (391,
    Int.ofNat 4), (429, Int.negSucc 1), (441, Int.ofNat 2), (447, Int.ofNat 2), (462, Int.ofNat
    2)] },
  { denominator := Int.ofNat 1, terms := [(430, Int.negSucc 0), (442, Int.ofNat 1), (443,
    Int.negSucc 1), (448, Int.ofNat 1), (463, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(93, Int.ofNat 1), (100, Int.negSucc 0), (367,
    Int.negSucc 0), (431, Int.negSucc 1), (452, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(89, Int.negSucc 1), (362, Int.negSucc 0), (419,
    Int.negSucc 1), (453, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(80, Int.ofNat 1), (347, Int.ofNat 2), (420, Int.negSucc
    1), (432, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 3), (130, Int.ofNat 2), (134,
    Int.negSucc 0), (412, Int.ofNat 4), (478, Int.ofNat 4), (485, Int.negSucc 3), (493, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 1), (118, Int.negSucc 0), (119,
    Int.ofNat 1), (396, Int.negSucc 1), (479, Int.ofNat 2), (486, Int.negSucc 1), (508, Int.ofNat
    1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 0), (390,
    Int.negSucc 1), (487, Int.negSucc 1), (494, Int.ofNat 2), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (148,
    Int.ofNat 1), (443, Int.ofNat 8), (480, Int.ofNat 8), (488, Int.negSucc 7), (495, Int.ofNat
    8), (510, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(481, Int.ofNat 4), (489, Int.negSucc 1), (496,
    Int.ofNat 2), (500, Int.negSucc 1), (511, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.negSucc 0), (118, Int.ofNat 2), (119,
    Int.negSucc 0), (131, Int.negSucc 1), (385, Int.negSucc 1), (396, Int.ofNat 2), (433,
    Int.negSucc 1), (471, Int.negSucc 0), (479, Int.negSucc 1), (486, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.negSucc 0), (107, Int.ofNat 1), (120,
    Int.negSucc 1), (380, Int.negSucc 1), (390, Int.ofNat 2), (421, Int.negSucc 1), (464,
    Int.negSucc 0), (487, Int.ofNat 2), (494, Int.negSucc 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (139, Int.ofNat 2), (148,
    Int.negSucc 3), (160, Int.ofNat 6), (164, Int.negSucc 0), (443, Int.negSucc 7), (463,
    Int.ofNat 8), (516, Int.ofNat 4), (520, Int.negSucc 3), (524, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(149, Int.negSucc 0), (418, Int.negSucc 1), (472,
    Int.negSucc 1), (539, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(137, Int.negSucc 0), (415, Int.negSucc 1), (465,
    Int.negSucc 1), (540, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(180, Int.ofNat 1), (502, Int.ofNat 4), (517, Int.ofNat
    2), (521, Int.negSucc 3), (525, Int.ofNat 2), (541, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(518, Int.ofNat 2), (522, Int.negSucc 1), (526,
    Int.ofNat 1), (542, Int.ofNat 2), (553, Int.negSucc 1)] },
  { denominator := Int.ofNat 1, terms := [(155, Int.ofNat 1), (455, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(144, Int.negSucc 0), (434, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(135, Int.negSucc 0), (422, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 1), (172, Int.ofNat 1), (481,
    Int.negSucc 3), (500, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(197, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 3), (130, Int.ofNat 4), (132,
    Int.negSucc 3), (134, Int.negSucc 0), (404, Int.negSucc 1), (412, Int.ofNat 4), (454,
    Int.negSucc 1), (478, Int.ofNat 4), (485, Int.negSucc 3), (504, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(106, Int.ofNat 1), (107, Int.negSucc 0), (110,
    Int.ofNat 1), (380, Int.ofNat 2), (390, Int.negSucc 1), (421, Int.ofNat 2), (475, Int.negSucc
    1), (487, Int.negSucc 1), (509, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(161, Int.ofNat 1), (451, Int.ofNat 1), (505, Int.ofNat
    1), (543, Int.ofNat 2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 1), (139, Int.negSucc 1), (148,
    Int.ofNat 4), (150, Int.negSucc 5), (151, Int.ofNat 2), (443, Int.ofNat 8), (448, Int.negSucc
    7), (528, Int.ofNat 8), (535, Int.negSucc 3), (556, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(138, Int.negSucc 0), (425, Int.negSucc 1), (476,
    Int.negSucc 3), (544, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(181, Int.ofNat 1), (503, Int.ofNat 4), (529, Int.ofNat
    4), (536, Int.negSucc 3), (545, Int.ofNat 4), (557, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(530, Int.ofNat 8), (537, Int.negSucc 3), (546,
    Int.ofNat 4), (554, Int.negSucc 3), (558, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(122, Int.negSucc 7), (130, Int.ofNat 2), (134,
    Int.negSucc 0), (404, Int.negSucc 1), (412, Int.ofNat 4), (454, Int.negSucc 1), (485,
    Int.negSucc 3), (493, Int.ofNat 4), (512, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(111, Int.ofNat 2), (118, Int.negSucc 0), (119,
    Int.ofNat 1), (385, Int.ofNat 2), (396, Int.negSucc 1), (433, Int.ofNat 2), (486, Int.negSucc
    1), (497, Int.negSucc 1), (508, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(156, Int.ofNat 2), (458, Int.ofNat 1), (513, Int.ofNat
    2), (531, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(145, Int.negSucc 0), (437, Int.negSucc 1), (498,
    Int.negSucc 3), (532, Int.ofNat 2)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 5), (139, Int.negSucc 5), (148,
    Int.ofNat 1), (442, Int.negSucc 7), (443, Int.ofNat 8), (480, Int.ofNat 8), (547, Int.negSucc
    7), (550, Int.ofNat 8), (560, Int.ofNat 4)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 1), (173, Int.ofNat 3), (501,
    Int.ofNat 6), (533, Int.ofNat 12), (548, Int.negSucc 11), (551, Int.ofNat 12), (561, Int.ofNat
    6)] },
  { denominator := Int.ofNat 2, terms := [(534, Int.ofNat 4), (549, Int.negSucc 1), (552,
    Int.ofNat 2), (555, Int.negSucc 1), (562, Int.ofNat 1)] },
  { denominator := Int.ofNat 4, terms := [(167, Int.ofNat 3), (172, Int.negSucc 1), (185,
    Int.ofNat 4), (481, Int.ofNat 4), (500, Int.negSucc 3), (511, Int.ofNat 2)] },
  { denominator := Int.ofNat 2, terms := [(175, Int.negSucc 0), (473, Int.negSucc 0)] },
  { denominator := Int.ofNat 4, terms := [(165, Int.negSucc 0), (466, Int.negSucc 1)] },
  { denominator := Int.ofNat 4, terms := [(195, Int.negSucc 0), (201, Int.ofNat 2), (518,
    Int.negSucc 1), (553, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(223, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 0), (139, Int.ofNat 2), (143,
    Int.ofNat 4), (148, Int.negSucc 10), (150, Int.ofNat 14), (151, Int.negSucc 1), (160,
    Int.ofNat 6), (162, Int.negSucc 7), (164, Int.negSucc 0), (430, Int.negSucc 7), (443,
    Int.negSucc 7), (448, Int.ofNat 8), (463, Int.ofNat 8), (480, Int.ofNat 8), (488, Int.negSucc
    7), (516, Int.ofNat 4), (520, Int.negSucc 3), (528, Int.negSucc 7), (535, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(171, Int.negSucc 1), (181, Int.negSucc 2), (193,
    Int.ofNat 2), (484, Int.ofNat 4), (503, Int.negSucc 3), (529, Int.negSucc 3), (536, Int.ofNat
    4), (573, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(180, Int.ofNat 1), (182, Int.negSucc 1), (470,
    Int.negSucc 3), (502, Int.ofNat 4), (517, Int.ofNat 2), (521, Int.negSucc 3), (585, Int.ofNat
    2)] },
  { denominator := Int.ofNat 4, terms := [(213, Int.ofNat 1), (519, Int.ofNat 3), (574, Int.ofNat
    2), (586, Int.ofNat 2)] },
  { denominator := Int.ofNat 4, terms := [(563, Int.ofNat 4), (570, Int.negSucc 2), (575,
    Int.ofNat 2), (587, Int.ofNat 2), (599, Int.negSucc 3)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.negSucc 4), (139, Int.ofNat 6), (148,
    Int.negSucc 3), (153, Int.negSucc 7), (160, Int.ofNat 6), (164, Int.negSucc 0), (430,
    Int.negSucc 7), (442, Int.ofNat 8), (443, Int.negSucc 7), (463, Int.ofNat 8), (480,
    Int.negSucc 7), (488, Int.negSucc 7), (495, Int.ofNat 8), (520, Int.negSucc 3), (524,
    Int.ofNat 4), (547, Int.ofNat 8), (550, Int.negSucc 7)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.ofNat 2), (173, Int.negSucc 2), (186,
    Int.ofNat 6), (492, Int.ofNat 6), (501, Int.negSucc 5), (533, Int.negSucc 5), (548, Int.ofNat
    12), (551, Int.negSucc 11), (567, Int.ofNat 3)] },
  { denominator := Int.ofNat 4, terms := [(170, Int.negSucc 1), (180, Int.ofNat 1), (470,
    Int.negSucc 3), (502, Int.ofNat 4), (517, Int.negSucc 1), (521, Int.negSucc 3), (525,
    Int.ofNat 2), (590, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(202, Int.ofNat 1), (523, Int.ofNat 2), (591, Int.ofNat
    4)] },
  { denominator := Int.ofNat 2, terms := [(569, Int.ofNat 2), (576, Int.negSucc 1), (577,
    Int.ofNat 1), (592, Int.ofNat 2), (600, Int.negSucc 1)] },
  { denominator := Int.ofNat 2, terms := [(187, Int.ofNat 4), (506, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 2), (172, Int.ofNat 2), (177,
    Int.negSucc 1), (481, Int.negSucc 3), (496, Int.negSucc 3), (500, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(166, Int.negSucc 0), (477, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(196, Int.negSucc 0), (203, Int.ofNat 2), (530,
    Int.negSucc 3), (554, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(225, Int.ofNat 1)] },
  { denominator := Int.ofNat 1, terms := [(189, Int.ofNat 1), (514, Int.ofNat 1)] },
  { denominator := Int.ofNat 2, terms := [(179, Int.negSucc 0), (499, Int.negSucc 3)] },
  { denominator := Int.ofNat 2, terms := [(167, Int.negSucc 2), (172, Int.ofNat 1), (481,
    Int.negSucc 7), (500, Int.ofNat 4)] },
  { denominator := Int.ofNat 2, terms := [(198, Int.negSucc 1), (205, Int.ofNat 1), (534,
    Int.negSucc 3), (555, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(227, Int.ofNat 1)] },
  { denominator := Int.ofNat 8, terms := [(136, Int.ofNat 5), (139, Int.negSucc 5), (143,
    Int.ofNat 4), (148, Int.ofNat 4), (150, Int.negSucc 5), (151, Int.ofNat 2), (430, Int.ofNat
    8), (442, Int.negSucc 7), (443, Int.ofNat 8), (448, Int.negSucc 7), (480, Int.ofNat 8), (488,
    Int.ofNat 8), (510, Int.negSucc 3), (535, Int.negSucc 3), (547, Int.negSucc 7), (556,
    Int.ofNat 2), (560, Int.ofNat 4)] },
  { denominator := Int.ofNat 12, terms := [(168, Int.negSucc 1), (173, Int.ofNat 3), (178,
    Int.negSucc 2), (492, Int.negSucc 5), (501, Int.ofNat 6), (533, Int.ofNat 6), (548,
    Int.negSucc 11), (561, Int.ofNat 6), (581, Int.ofNat 6)] },
  { denominator := Int.ofNat 4, terms := [(171, Int.negSucc 1), (181, Int.ofNat 1), (484,
    Int.negSucc 3), (503, Int.ofNat 4), (529, Int.negSucc 3), (536, Int.negSucc 3), (557,
    Int.ofNat 1), (593, Int.ofNat 4)] },
  { denominator := Int.ofNat 4, terms := [(204, Int.ofNat 1), (538, Int.ofNat 2), (594, Int.ofNat
    4)] }
]

end VOA.DeligneAudit.D4Two.Certificate

import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,1) (u₍1₎a)₍5₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J1_0 : SectorVector := [(1,
  [(-68, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-580, [0, 1, 1, 1, 1, 3]),
   (1230, [0, 1, 1, 1, 2, 2]),
   (2232, [0, 1, 1, 5]),
   (2160, [0, 1, 2, 4]),
   (-800, [0, 1, 3, 3]),
   (690, [0, 2, 2, 3]),
   (6840, [0, 7]),
   (504, [1, 1, 1, 1, 1, 2]),
   (240, [1, 1, 1, 4]),
   (-3600, [1, 1, 2, 3]),
   (-4020, [1, 2, 2, 2]),
   (-17880, [1, 6]),
   (-5616, [2, 5]),
   (2400, [3, 4])]),
 (-1,
  [(68, [0, 1, 1, 1, 1, 1, 1, 1]),
   (580, [0, 1, 1, 1, 1, 3]),
   (-1230, [0, 1, 1, 1, 2, 2]),
   (-2232, [0, 1, 1, 5]),
   (-2160, [0, 1, 2, 4]),
   (800, [0, 1, 3, 3]),
   (-690, [0, 2, 2, 3]),
   (-6840, [0, 7]),
   (504, [1, 1, 1, 1, 1, 2]),
   (240, [1, 1, 1, 4]),
   (-3600, [1, 1, 2, 3]),
   (-4020, [1, 2, 2, 2]),
   (-17880, [1, 6]),
   (-5616, [2, 5]),
   (2400, [3, 4])])]

def skP_J1_1 : SectorVector := [(-1,
  [(560, [0, 1, 1, 1, 1, 1, 1, 1]),
   (2680, [0, 1, 1, 1, 1, 3]),
   (-3480, [0, 1, 1, 1, 2, 2]),
   (3600, [0, 1, 1, 5]),
   (-5400, [0, 1, 2, 4]),
   (-400, [0, 1, 3, 3]),
   (2460, [0, 2, 2, 3]),
   (-36000, [0, 7]),
   (5760, [1, 1, 1, 1, 1, 2]),
   (11040, [1, 1, 1, 4]),
   (-20160, [1, 1, 2, 3]),
   (-5280, [1, 2, 2, 2]),
   (-34800, [1, 6]),
   (-19440, [2, 5]),
   (2400, [3, 4])]),
 (1,
  [(-560, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-2680, [0, 1, 1, 1, 1, 3]),
   (3480, [0, 1, 1, 1, 2, 2]),
   (-3600, [0, 1, 1, 5]),
   (5400, [0, 1, 2, 4]),
   (400, [0, 1, 3, 3]),
   (-2460, [0, 2, 2, 3]),
   (36000, [0, 7]),
   (5760, [1, 1, 1, 1, 1, 2]),
   (11040, [1, 1, 1, 4]),
   (-20160, [1, 1, 2, 3]),
   (-5280, [1, 2, 2, 2]),
   (-34800, [1, 6]),
   (-19440, [2, 5]),
   (2400, [3, 4])])]

def skP_J1_2 : SectorVector := [(1,
  [(-2160, [0, 1, 1, 1, 1, 1, 1, 1]),
   (10260, [0, 1, 1, 1, 1, 3]),
   (15120, [0, 1, 1, 1, 2, 2]),
   (-32400, [0, 1, 1, 5]),
   (-45360, [0, 1, 2, 4]),
   (-11880, [0, 1, 3, 3]),
   (-13230, [0, 2, 2, 3]),
   (145800, [0, 7]),
   (10800, [1, 1, 1, 1, 1, 2]),
   (-64800, [1, 1, 1, 4]),
   (-21600, [1, 1, 2, 3]),
   (-3240, [1, 2, 2, 2]),
   (226800, [1, 6]),
   (-25920, [2, 5]),
   (-16200, [3, 4])]),
 (-1,
  [(2160, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-10260, [0, 1, 1, 1, 1, 3]),
   (-15120, [0, 1, 1, 1, 2, 2]),
   (32400, [0, 1, 1, 5]),
   (45360, [0, 1, 2, 4]),
   (11880, [0, 1, 3, 3]),
   (13230, [0, 2, 2, 3]),
   (-145800, [0, 7]),
   (10800, [1, 1, 1, 1, 1, 2]),
   (-64800, [1, 1, 1, 4]),
   (-21600, [1, 1, 2, 3]),
   (-3240, [1, 2, 2, 2]),
   (226800, [1, 6]),
   (-25920, [2, 5]),
   (-16200, [3, 4])])]

def skP_J1_3 : SectorVector := [(-1,
  [(5760, [0, 1, 1, 1, 1, 1, 1, 1]),
   (24480, [0, 1, 1, 1, 1, 3]),
   (-95040, [0, 1, 1, 1, 2, 2]),
   (-77760, [0, 1, 1, 5]),
   (252720, [0, 1, 2, 4]),
   (135360, [0, 1, 3, 3]),
   (34560, [0, 2, 2, 3]),
   (-648000, [0, 7]),
   (51840, [1, 1, 1, 1, 1, 2]),
   (-345600, [1, 1, 1, 4]),
   (-259200, [1, 1, 2, 3]),
   (112320, [1, 2, 2, 2]),
   (1771200, [1, 6]),
   (-129600, [2, 5]),
   (-475200, [3, 4])]),
 (1,
  [(-5760, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-24480, [0, 1, 1, 1, 1, 3]),
   (95040, [0, 1, 1, 1, 2, 2]),
   (77760, [0, 1, 1, 5]),
   (-252720, [0, 1, 2, 4]),
   (-135360, [0, 1, 3, 3]),
   (-34560, [0, 2, 2, 3]),
   (648000, [0, 7]),
   (51840, [1, 1, 1, 1, 1, 2]),
   (-345600, [1, 1, 1, 4]),
   (-259200, [1, 1, 2, 3]),
   (112320, [1, 2, 2, 2]),
   (1771200, [1, 6]),
   (-129600, [2, 5]),
   (-475200, [3, 4])])]

def skP_J1_4 : SectorVector := [(1,
  [(46080, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-115200, [0, 1, 1, 1, 1, 3]),
   (-345600, [0, 1, 1, 1, 2, 2]),
   (1399680, [0, 1, 1, 5]),
   (-97200, [0, 1, 2, 4]),
   (-316800, [0, 1, 3, 3]),
   (-280800, [0, 2, 2, 3]),
   (1425600, [0, 7]),
   (207360, [1, 1, 1, 1, 1, 2]),
   (691200, [1, 1, 1, 4]),
   (-2592000, [1, 1, 2, 3]),
   (-820800, [1, 2, 2, 2]),
   (6436800, [1, 6]),
   (1114560, [2, 5]),
   (-216000, [3, 4])]),
 (-1,
  [(-46080, [0, 1, 1, 1, 1, 1, 1, 1]),
   (115200, [0, 1, 1, 1, 1, 3]),
   (345600, [0, 1, 1, 1, 2, 2]),
   (-1399680, [0, 1, 1, 5]),
   (97200, [0, 1, 2, 4]),
   (316800, [0, 1, 3, 3]),
   (280800, [0, 2, 2, 3]),
   (-1425600, [0, 7]),
   (207360, [1, 1, 1, 1, 1, 2]),
   (691200, [1, 1, 1, 4]),
   (-2592000, [1, 1, 2, 3]),
   (-820800, [1, 2, 2, 2]),
   (6436800, [1, 6]),
   (1114560, [2, 5]),
   (-216000, [3, 4])])]

def skP_J1_5 : SectorVector := [(-1,
  [(138240, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-345600, [0, 1, 1, 1, 1, 3]),
   (259200, [0, 1, 1, 1, 2, 2]),
   (-3576960, [0, 1, 1, 5]),
   (-2721600, [0, 1, 2, 4]),
   (-950400, [0, 1, 3, 3]),
   (-518400, [0, 2, 2, 3]),
   (-1555200, [0, 7]),
   (-1658880, [1, 1, 1, 1, 1, 2]),
   (5702400, [1, 1, 1, 4]),
   (5184000, [1, 1, 2, 3]),
   (518400, [1, 2, 2, 2]),
   (9849600, [1, 6]),
   (4043520, [2, 5]),
   (2592000, [3, 4])]),
 (1,
  [(-138240, [0, 1, 1, 1, 1, 1, 1, 1]),
   (345600, [0, 1, 1, 1, 1, 3]),
   (-259200, [0, 1, 1, 1, 2, 2]),
   (3576960, [0, 1, 1, 5]),
   (2721600, [0, 1, 2, 4]),
   (950400, [0, 1, 3, 3]),
   (518400, [0, 2, 2, 3]),
   (1555200, [0, 7]),
   (-1658880, [1, 1, 1, 1, 1, 2]),
   (5702400, [1, 1, 1, 4]),
   (5184000, [1, 1, 2, 3]),
   (518400, [1, 2, 2, 2]),
   (9849600, [1, 6]),
   (4043520, [2, 5]),
   (2592000, [3, 4])])]

def skP_J1_6 : SectorVector := [(1,
  [(-691200, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-6048000, [0, 1, 1, 1, 1, 3]),
   (-9072000, [0, 1, 1, 1, 2, 2]),
   (-5443200, [0, 1, 1, 5]),
   (-6804000, [0, 1, 2, 4]),
   (-3024000, [0, 1, 3, 3]),
   (-2268000, [0, 2, 2, 3]),
   (-972000, [0, 7]),
   (-14515200, [1, 1, 1, 1, 1, 2]),
   (-18144000, [1, 1, 1, 4]),
   (-36288000, [1, 1, 2, 3]),
   (-9072000, [1, 2, 2, 2]),
   (-9072000, [1, 6]),
   (-5443200, [2, 5]),
   (-4536000, [3, 4])]),
 (-1,
  [(691200, [0, 1, 1, 1, 1, 1, 1, 1]),
   (6048000, [0, 1, 1, 1, 1, 3]),
   (9072000, [0, 1, 1, 1, 2, 2]),
   (5443200, [0, 1, 1, 5]),
   (6804000, [0, 1, 2, 4]),
   (3024000, [0, 1, 3, 3]),
   (2268000, [0, 2, 2, 3]),
   (972000, [0, 7]),
   (-14515200, [1, 1, 1, 1, 1, 2]),
   (-18144000, [1, 1, 1, 4]),
   (-36288000, [1, 1, 2, 3]),
   (-9072000, [1, 2, 2, 2]),
   (-9072000, [1, 6]),
   (-5443200, [2, 5]),
   (-4536000, [3, 4])])]

def skP_J1_7 : SectorVector := [(-1,
  [(-5529600, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-48384000, [0, 1, 1, 1, 1, 3]),
   (-72576000, [0, 1, 1, 1, 2, 2]),
   (-43545600, [0, 1, 1, 5]),
   (-54432000, [0, 1, 2, 4]),
   (-24192000, [0, 1, 3, 3]),
   (-18144000, [0, 2, 2, 3]),
   (-7776000, [0, 7]),
   (116121600, [1, 1, 1, 1, 1, 2]),
   (145152000, [1, 1, 1, 4]),
   (290304000, [1, 1, 2, 3]),
   (72576000, [1, 2, 2, 2]),
   (72576000, [1, 6]),
   (43545600, [2, 5]),
   (36288000, [3, 4])]),
 (1,
  [(5529600, [0, 1, 1, 1, 1, 1, 1, 1]),
   (48384000, [0, 1, 1, 1, 1, 3]),
   (72576000, [0, 1, 1, 1, 2, 2]),
   (43545600, [0, 1, 1, 5]),
   (54432000, [0, 1, 2, 4]),
   (24192000, [0, 1, 3, 3]),
   (18144000, [0, 2, 2, 3]),
   (7776000, [0, 7]),
   (116121600, [1, 1, 1, 1, 1, 2]),
   (145152000, [1, 1, 1, 4]),
   (290304000, [1, 1, 2, 3]),
   (72576000, [1, 2, 2, 2]),
   (72576000, [1, 6]),
   (43545600, [2, 5]),
   (36288000, [3, 4])])]

def skP_J1_8 : SectorVector := [(1, []), (-1, [])]

def skP_J1_9 : SectorVector := [(-1, []), (1, [])]

def skP_J1_10 : SectorVector := [(1, []), (-1, [])]

def skP_J1_11 : SectorVector := [(-1, []), (1, [])]

def skY_J1 : SectorVector := [(1,
  [((9708 : Rat)/7, [0, 1, 1, 1, 1, 1, 1, 1]),
   (-14370, [0, 1, 1, 1, 1, 3]),
   (-49770, [0, 1, 1, 1, 2, 2]),
   (-11016, [0, 1, 1, 5]),
   (-30780, [0, 1, 2, 4]),
   (-14700, [0, 1, 3, 3]),
   (-20475, [0, 2, 2, 3]),
   ((-144990 : Rat)/7, [0, 7]),
   (-29232, [1, 1, 1, 1, 1, 2]),
   (-58320, [1, 1, 1, 4]),
   (-210240, [1, 1, 2, 3]),
   (-84600, [1, 2, 2, 2]),
   (-5760, [1, 6]),
   (19008, [2, 5]),
   (27000, [3, 4])]),
 (-1,
  [((-9708 : Rat)/7, [0, 1, 1, 1, 1, 1, 1, 1]),
   (14370, [0, 1, 1, 1, 1, 3]),
   (49770, [0, 1, 1, 1, 2, 2]),
   (11016, [0, 1, 1, 5]),
   (30780, [0, 1, 2, 4]),
   (14700, [0, 1, 3, 3]),
   (20475, [0, 2, 2, 3]),
   ((144990 : Rat)/7, [0, 7]),
   (-29232, [1, 1, 1, 1, 1, 2]),
   (-58320, [1, 1, 1, 4]),
   (-210240, [1, 1, 2, 3]),
   (-84600, [1, 2, 2, 2]),
   (-5760, [1, 6]),
   (19008, [2, 5]),
   (27000, [3, 4])])]

def skQ_J1_0 : SectorVector := [(-1,
  [(15387624, [0, 1, 1, 1, 1, 1]),
   (131432760, [0, 1, 1, 3]),
   (135926100, [0, 1, 2, 2]),
   (-7352856, [0, 5]),
   (-434764800, [1, 1, 1, 2]),
   (-239902560, [1, 4]),
   (-200240640, [2, 3])]),
 (1,
  [(-15387624, [0, 1, 1, 1, 1, 1]),
   (-131432760, [0, 1, 1, 3]),
   (-135926100, [0, 1, 2, 2]),
   (7352856, [0, 5]),
   (-434764800, [1, 1, 1, 2]),
   (-239902560, [1, 4]),
   (-200240640, [2, 3])])]

def skQ_J1_1 : SectorVector := [(1,
  [(-156051360, [0, 1, 1, 1, 1, 1]),
   (-831533040, [0, 1, 1, 3]),
   (-669163680, [0, 1, 2, 2]),
   (-9972720, [0, 5]),
   (-2564239680, [1, 1, 1, 2]),
   (-1059518880, [1, 4]),
   (-1083144960, [2, 3])]),
 (-1,
  [(156051360, [0, 1, 1, 1, 1, 1]),
   (831533040, [0, 1, 1, 3]),
   (669163680, [0, 1, 2, 2]),
   (9972720, [0, 5]),
   (-2564239680, [1, 1, 1, 2]),
   (-1059518880, [1, 4]),
   (-1083144960, [2, 3])])]

def skQ_J1_2 : SectorVector := [(-1,
  [(1037836800, [0, 1, 1, 1, 1, 1]),
   (3634787520, [0, 1, 1, 3]),
   (2763240480, [0, 1, 2, 2]),
   (314889120, [0, 5]),
   (-12557825280, [1, 1, 1, 2]),
   (-5229282240, [1, 4]),
   (-4179651840, [2, 3])]),
 (1,
  [(-1037836800, [0, 1, 1, 1, 1, 1]),
   (-3634787520, [0, 1, 1, 3]),
   (-2763240480, [0, 1, 2, 2]),
   (-314889120, [0, 5]),
   (-12557825280, [1, 1, 1, 2]),
   (-5229282240, [1, 4]),
   (-4179651840, [2, 3])])]

def skQ_J1_3 : SectorVector := [(1,
  [(-4536829440, [0, 1, 1, 1, 1, 1]),
   (-11978928000, [0, 1, 1, 3]),
   (-8824982400, [0, 1, 2, 2]),
   (-2019738240, [0, 5]),
   (-46217433600, [1, 1, 1, 2]),
   (-18923673600, [1, 4]),
   (-12191212800, [2, 3])]),
 (-1,
  [(4536829440, [0, 1, 1, 1, 1, 1]),
   (11978928000, [0, 1, 1, 3]),
   (8824982400, [0, 1, 2, 2]),
   (2019738240, [0, 5]),
   (-46217433600, [1, 1, 1, 2]),
   (-18923673600, [1, 4]),
   (-12191212800, [2, 3])])]

def skQ_J1_4 : SectorVector := [(-1,
  [(10723415040, [0, 1, 1, 1, 1, 1]),
   (26808537600, [0, 1, 1, 3]),
   (20106403200, [0, 1, 2, 2]),
   (4021280640, [0, 5]),
   (-107234150400, [1, 1, 1, 2]),
   (-40212806400, [1, 4]),
   (-26808537600, [2, 3])]),
 (1,
  [(-10723415040, [0, 1, 1, 1, 1, 1]),
   (-26808537600, [0, 1, 1, 3]),
   (-20106403200, [0, 1, 2, 2]),
   (-4021280640, [0, 5]),
   (-107234150400, [1, 1, 1, 2]),
   (-40212806400, [1, 4]),
   (-26808537600, [2, 3])])]

def skQ_J1_5 : SectorVector := [(1,
  [(-7148943360, [0, 1, 1, 1, 1, 1]),
   (-17872358400, [0, 1, 1, 3]),
   (-13404268800, [0, 1, 2, 2]),
   (-2680853760, [0, 5]),
   (-71489433600, [1, 1, 1, 2]),
   (-26808537600, [1, 4]),
   (-17872358400, [2, 3])]),
 (-1,
  [(7148943360, [0, 1, 1, 1, 1, 1]),
   (17872358400, [0, 1, 1, 3]),
   (13404268800, [0, 1, 2, 2]),
   (2680853760, [0, 5]),
   (-71489433600, [1, 1, 1, 2]),
   (-26808537600, [1, 4]),
   (-17872358400, [2, 3])])]

def skQ_J1_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J1_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J1_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J1_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J1 : ℕ → SectorVector
  | 0 => skP_J1_0
  | 1 => skP_J1_1
  | 2 => skP_J1_2
  | 3 => skP_J1_3
  | 4 => skP_J1_4
  | 5 => skP_J1_5
  | 6 => skP_J1_6
  | 7 => skP_J1_7
  | 8 => skP_J1_8
  | 9 => skP_J1_9
  | 10 => skP_J1_10
  | 11 => skP_J1_11
  | _ => []

def skQf_J1 : ℕ → SectorVector
  | 0 => skQ_J1_0
  | 1 => skQ_J1_1
  | 2 => skQ_J1_2
  | 3 => skQ_J1_3
  | 4 => skQ_J1_4
  | 5 => skQ_J1_5
  | 6 => skQ_J1_6
  | 7 => skQ_J1_7
  | 8 => skQ_J1_8
  | 9 => skQ_J1_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J1_0_cert : VectorCertificate (OrbSgl.uTerm true 1 0) skP_J1_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_1_cert : VectorCertificate (OrbSgl.uTerm true 1 1) skP_J1_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_2_cert : VectorCertificate (OrbSgl.uTerm true 1 2) skP_J1_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_3_cert : VectorCertificate (OrbSgl.uTerm true 1 3) skP_J1_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_4_cert : VectorCertificate (OrbSgl.uTerm true 1 4) skP_J1_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_5_cert : VectorCertificate (OrbSgl.uTerm true 1 5) skP_J1_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_6_cert : VectorCertificate (OrbSgl.uTerm true 1 6) skP_J1_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_7_cert : VectorCertificate (OrbSgl.uTerm true 1 7) skP_J1_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_8_cert : VectorCertificate (OrbSgl.uTerm true 1 8) skP_J1_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_9_cert : VectorCertificate (OrbSgl.uTerm true 1 9) skP_J1_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_10_cert : VectorCertificate (OrbSgl.uTerm true 1 10) skP_J1_10 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J1_11_cert : VectorCertificate (OrbSgl.uTerm true 1 11) skP_J1_11 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J1_cert : VectorCertificate (OrbSgl.uSum 1 skPf_J1) skY_J1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 0) skQ_J1_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 1) skQ_J1_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 2) skQ_J1_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 3) skQ_J1_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 4) skQ_J1_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 5) skQ_J1_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 6) skQ_J1_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 7) skQ_J1_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 8) skQ_J1_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J1_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J1 1 9) skQ_J1_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J1_cert : VectorCertificate (OrbSgl.vSum 1 skQf_J1) termJ_1 := by decide +kernel

theorem skY_J1_value : evaluate skY_J1 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 1 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J1_cert]
  apply evaluate_uSum true 1 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J1_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_9_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_10_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J1_11_cert).symm

/-- The certified value of `termJ_1`. -/
theorem sk_J1 : evaluate termJ_1 = ((Nat.choose 15 1 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 1 (aVec true))
      (6 - (1 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J1_cert]
  apply evaluate_vSum true 1 (by norm_num) skY_J1 skY_J1_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J1_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J1_9_cert).symm

end VOA.Classification.COne.OrbSgl

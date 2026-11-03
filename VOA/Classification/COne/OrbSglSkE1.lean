import VOA.Classification.COne.OrbSglSkE1a

/-! # OrbSgl: chunked evaluation of `C(15,1) (u₍1₎a)₍5₎a`, `a = E`: stage 2 and `sk_E1`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skA_E1_Q0_0 : SectorVector := [(-1,
  [((8101888 : Rat)/945, [0, 1, 1, 1, 1, 1]),
   ((-45088768 : Rat)/189, [0, 1, 1, 3]),
   ((-5636096 : Rat)/63, [0, 1, 2, 2]),
   ((90177536 : Rat)/315, [0, 5]),
   ((-5636096 : Rat)/63, [1, 1, 1, 2]),
   ((22544384 : Rat)/63, [1, 4]),
   ((-90177536 : Rat)/63, [2, 3])]),
 (1,
  [((-8101888 : Rat)/945, [0, 1, 1, 1, 1, 1]),
   ((45088768 : Rat)/189, [0, 1, 1, 3]),
   ((5636096 : Rat)/63, [0, 1, 2, 2]),
   ((-90177536 : Rat)/315, [0, 5]),
   ((-5636096 : Rat)/63, [1, 1, 1, 2]),
   ((22544384 : Rat)/63, [1, 4]),
   ((-90177536 : Rat)/63, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_0_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_0)) skA_E1_Q0_0 := by decide +kernel

def skA_E1_Q0_1 : SectorVector := [(-1,
  [((6016 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-8192, [0, 1, 1, 3]),
   (8192, [0, 1, 2, 2]),
   ((65536 : Rat)/5, [0, 5]),
   ((69632 : Rat)/3, [1, 1, 1, 2]),
   (-8192, [1, 4]),
   ((-262144 : Rat)/3, [2, 3])]),
 (1,
  [((-6016 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (8192, [0, 1, 1, 3]),
   (-8192, [0, 1, 2, 2]),
   ((-65536 : Rat)/5, [0, 5]),
   ((69632 : Rat)/3, [1, 1, 1, 2]),
   (-8192, [1, 4]),
   ((-262144 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_1_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_1)) skA_E1_Q0_1 := by decide +kernel

def skA_E1_Q0_2 : SectorVector := [(-1,
  [((906752 : Rat)/45, [0, 1, 1, 1, 1, 1]),
   ((-788480 : Rat)/9, [0, 1, 1, 3]),
   ((1261568 : Rat)/3, [0, 1, 2, 2]),
   ((10092544 : Rat)/15, [0, 5]),
   ((3153920 : Rat)/3, [1, 1, 1, 2]),
   ((-5046272 : Rat)/3, [1, 4]),
   ((-6307840 : Rat)/3, [2, 3])]),
 (1,
  [((-906752 : Rat)/45, [0, 1, 1, 1, 1, 1]),
   ((788480 : Rat)/9, [0, 1, 1, 3]),
   ((-1261568 : Rat)/3, [0, 1, 2, 2]),
   ((-10092544 : Rat)/15, [0, 5]),
   ((3153920 : Rat)/3, [1, 1, 1, 2]),
   ((-5046272 : Rat)/3, [1, 4]),
   ((-6307840 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_2_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_2)) skA_E1_Q0_2 := by decide +kernel

def skA_E1_Q0_3 : SectorVector := [(-1,
  [((-297024 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (319488, [0, 1, 1, 3]),
   (-179712, [0, 1, 2, 2]),
   ((3833856 : Rat)/5, [0, 5]),
   (279552, [1, 1, 1, 2]),
   (-2875392, [1, 4]),
   (-1277952, [2, 3])]),
 (1,
  [((297024 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-319488, [0, 1, 1, 3]),
   (179712, [0, 1, 2, 2]),
   ((-3833856 : Rat)/5, [0, 5]),
   (279552, [1, 1, 1, 2]),
   (-2875392, [1, 4]),
   (-1277952, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_3_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_3)) skA_E1_Q0_3 := by decide +kernel

def skA_E1_Q0_4 : SectorVector := [(-1,
  [((50456 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-54272, [0, 1, 1, 3]),
   (-244224, [0, 1, 2, 2]),
   ((-651264 : Rat)/5, [0, 5]),
   (-189952, [1, 1, 1, 2]),
   (488448, [1, 4]),
   (868352, [2, 3])]),
 (1,
  [((-50456 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (54272, [0, 1, 1, 3]),
   (244224, [0, 1, 2, 2]),
   ((651264 : Rat)/5, [0, 5]),
   (-189952, [1, 1, 1, 2]),
   (488448, [1, 4]),
   (868352, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_4_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_4)) skA_E1_Q0_4 := by decide +kernel

def skA_E1_Q0_5 : SectorVector := [(-1,
  [((504768 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-734208, [0, 1, 1, 3]),
   (-734208, [0, 1, 2, 2]),
   ((-1101312 : Rat)/5, [0, 5]),
   (183552, [1, 1, 1, 2]),
   (2936832, [1, 4]),
   (2936832, [2, 3])]),
 (1,
  [((-504768 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (734208, [0, 1, 1, 3]),
   (734208, [0, 1, 2, 2]),
   ((1101312 : Rat)/5, [0, 5]),
   (183552, [1, 1, 1, 2]),
   (2936832, [1, 4]),
   (2936832, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_5_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_5)) skA_E1_Q0_5 := by decide +kernel

def skA_E1_Q0_6 : SectorVector := [(-1,
  [(88352, [0, 1, 1, 1, 1, 1]),
   (-401600, [0, 1, 1, 3]),
   (-1285120, [0, 1, 2, 2]),
   (-514048, [0, 5]),
   ((642560 : Rat)/3, [1, 1, 1, 2]),
   (1285120, [1, 4]),
   ((6425600 : Rat)/3, [2, 3])]),
 (1,
  [(-88352, [0, 1, 1, 1, 1, 1]),
   (401600, [0, 1, 1, 3]),
   (1285120, [0, 1, 2, 2]),
   (514048, [0, 5]),
   ((642560 : Rat)/3, [1, 1, 1, 2]),
   (1285120, [1, 4]),
   ((6425600 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_6_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_6)) skA_E1_Q0_6 := by decide +kernel

def skA_E1_Q0_7 : SectorVector := [(-1,
  [(39424, [0, 1, 1, 1, 1, 1]),
   (-619520, [0, 1, 1, 3]),
   (-105600, [0, 1, 2, 2]),
   (-270336, [0, 5]),
   (520960, [1, 1, 1, 2]),
   (844800, [1, 4]),
   (901120, [2, 3])]),
 (1,
  [(-39424, [0, 1, 1, 1, 1, 1]),
   (619520, [0, 1, 1, 3]),
   (105600, [0, 1, 2, 2]),
   (270336, [0, 5]),
   (520960, [1, 1, 1, 2]),
   (844800, [1, 4]),
   (901120, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_7_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_7)) skA_E1_Q0_7 := by decide +kernel

def skA_E1_Q0_8 : SectorVector := [(-1,
  [((111104 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-436480 : Rat)/9, [0, 1, 1, 3]),
   ((-396800 : Rat)/3, [0, 1, 2, 2]),
   ((-253952 : Rat)/3, [0, 5]),
   ((734080 : Rat)/3, [1, 1, 1, 2]),
   ((1587200 : Rat)/3, [1, 4]),
   ((317440 : Rat)/3, [2, 3])]),
 (1,
  [((-111104 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((436480 : Rat)/9, [0, 1, 1, 3]),
   ((396800 : Rat)/3, [0, 1, 2, 2]),
   ((253952 : Rat)/3, [0, 5]),
   ((734080 : Rat)/3, [1, 1, 1, 2]),
   ((1587200 : Rat)/3, [1, 4]),
   ((317440 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_8_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_8)) skA_E1_Q0_8 := by decide +kernel

def skA_E1_Q0_9 : SectorVector := [(-1,
  [(-30464, [0, 1, 1, 1, 1, 1]),
   (478720, [0, 1, 1, 3]),
   (652800, [0, 1, 2, 2]),
   (208896, [0, 5]),
   (-805120, [1, 1, 1, 2]),
   (-1305600, [1, 4]),
   (-1392640, [2, 3])]),
 (1,
  [(30464, [0, 1, 1, 1, 1, 1]),
   (-478720, [0, 1, 1, 3]),
   (-652800, [0, 1, 2, 2]),
   (-208896, [0, 5]),
   (-805120, [1, 1, 1, 2]),
   (-1305600, [1, 4]),
   (-1392640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_9_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_9)) skA_E1_Q0_9 := by decide +kernel

def skA_E1_Q0_10 : SectorVector := [(-1,
  [(22528, [0, 1, 1, 1, 1, 1]),
   (299200, [0, 1, 1, 3]),
   (-63360, [0, 1, 2, 2]),
   (135168, [0, 5]),
   (-309760, [1, 1, 1, 2]),
   (-1013760, [1, 4]),
   (-140800, [2, 3])]),
 (1,
  [(-22528, [0, 1, 1, 1, 1, 1]),
   (-299200, [0, 1, 1, 3]),
   (63360, [0, 1, 2, 2]),
   (-135168, [0, 5]),
   (-309760, [1, 1, 1, 2]),
   (-1013760, [1, 4]),
   (-140800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_10_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_10)) skA_E1_Q0_10 := by decide +kernel

def skA_E1_Q0_11 : SectorVector := [(-1,
  [((-139008 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-2953920 : Rat)/7, [0, 1, 1, 3]),
   ((-1563840 : Rat)/7, [0, 1, 2, 2]),
   ((-834048 : Rat)/7, [0, 5]),
   ((5734080 : Rat)/7, [1, 1, 1, 2]),
   ((6255360 : Rat)/7, [1, 4]),
   ((4170240 : Rat)/7, [2, 3])]),
 (1,
  [((139008 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((2953920 : Rat)/7, [0, 1, 1, 3]),
   ((1563840 : Rat)/7, [0, 1, 2, 2]),
   ((834048 : Rat)/7, [0, 5]),
   ((5734080 : Rat)/7, [1, 1, 1, 2]),
   ((6255360 : Rat)/7, [1, 4]),
   ((4170240 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_11_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_11)) skA_E1_Q0_11 := by decide +kernel

def skA_E1_Q0_12 : SectorVector := [(-1,
  [(-50432, [0, 1, 1, 1, 1, 1]),
   (-669800, [0, 1, 1, 3]),
   (-1134720, [0, 1, 2, 2]),
   (-302592, [0, 5]),
   (2773760, [1, 1, 1, 2]),
   (2269440, [1, 4]),
   (1260800, [2, 3])]),
 (1,
  [(50432, [0, 1, 1, 1, 1, 1]),
   (669800, [0, 1, 1, 3]),
   (1134720, [0, 1, 2, 2]),
   (302592, [0, 5]),
   (2773760, [1, 1, 1, 2]),
   (2269440, [1, 4]),
   (1260800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_12_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_12)) skA_E1_Q0_12 := by decide +kernel

def skA_E1_Q0_13 : SectorVector := [(-1,
  [((-297216 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-1263168, [0, 1, 1, 3]),
   (-1337472, [0, 1, 2, 2]),
   ((-668736 : Rat)/5, [0, 5]),
   (3269376, [1, 1, 1, 2]),
   (1337472, [1, 4]),
   (2377728, [2, 3])]),
 (1,
  [((297216 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (1263168, [0, 1, 1, 3]),
   (1337472, [0, 1, 2, 2]),
   ((668736 : Rat)/5, [0, 5]),
   (3269376, [1, 1, 1, 2]),
   (1337472, [1, 4]),
   (2377728, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_13_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_13)) skA_E1_Q0_13 := by decide +kernel

def skA_E1_Q0_14 : SectorVector := [(-1,
  [((104448 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (104448, [0, 1, 1, 3]),
   (-22848, [0, 1, 2, 2]),
   ((104448 : Rat)/5, [0, 5]),
   (87040, [1, 1, 1, 2]),
   (-182784, [1, 4]),
   (34816, [2, 3])]),
 (1,
  [((-104448 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-104448, [0, 1, 1, 3]),
   (22848, [0, 1, 2, 2]),
   ((-104448 : Rat)/5, [0, 5]),
   (87040, [1, 1, 1, 2]),
   (-182784, [1, 4]),
   (34816, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_14_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_14)) skA_E1_Q0_14 := by decide +kernel

def skA_E1_Q0_15 : SectorVector := [(-1,
  [(-132864, [0, 1, 1, 1, 1, 1]),
   (-664320, [0, 1, 1, 3]),
   (-72660, [0, 1, 2, 2]),
   (-132864, [0, 5]),
   (1107200, [1, 1, 1, 2]),
   (1162560, [1, 4]),
   (442880, [2, 3])]),
 (1,
  [(132864, [0, 1, 1, 1, 1, 1]),
   (664320, [0, 1, 1, 3]),
   (72660, [0, 1, 2, 2]),
   (132864, [0, 5]),
   (1107200, [1, 1, 1, 2]),
   (1162560, [1, 4]),
   (442880, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_15_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_15)) skA_E1_Q0_15 := by decide +kernel

def skA_E1_Q0_16 : SectorVector := [(-1,
  [((-1256448 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-785280, [0, 1, 1, 3]),
   (-549696, [0, 1, 2, 2]),
   ((-471168 : Rat)/5, [0, 5]),
   (3141120, [1, 1, 1, 2]),
   (2198784, [1, 4]),
   (785280, [2, 3])]),
 (1,
  [((1256448 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (785280, [0, 1, 1, 3]),
   (549696, [0, 1, 2, 2]),
   ((471168 : Rat)/5, [0, 5]),
   (3141120, [1, 1, 1, 2]),
   (2198784, [1, 4]),
   (785280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_16_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_16)) skA_E1_Q0_16 := by decide +kernel

def skA_E1_Q0_17 : SectorVector := [(-1,
  [(-122112, [0, 1, 1, 1, 1, 1]),
   (-610560, [0, 1, 1, 3]),
   (-267120, [0, 1, 2, 2]),
   (-122112, [0, 5]),
   (1526400, [1, 1, 1, 2]),
   (610560, [2, 3])]),
 (1,
  [(122112, [0, 1, 1, 1, 1, 1]),
   (610560, [0, 1, 1, 3]),
   (267120, [0, 1, 2, 2]),
   (122112, [0, 5]),
   (1526400, [1, 1, 1, 2]),
   (610560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_17_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_17)) skA_E1_Q0_17 := by decide +kernel

def skA_E1_Q0_18 : SectorVector := [(-1,
  [(-77824, [0, 1, 1, 1, 1, 1]),
   (-97280, [0, 1, 1, 3]),
   (-340480, [0, 1, 2, 2]),
   (-77824, [0, 5]),
   ((3891200 : Rat)/3, [1, 1, 1, 2]),
   (340480, [1, 4]),
   ((389120 : Rat)/3, [2, 3])]),
 (1,
  [(77824, [0, 1, 1, 1, 1, 1]),
   (97280, [0, 1, 1, 3]),
   (340480, [0, 1, 2, 2]),
   (77824, [0, 5]),
   ((3891200 : Rat)/3, [1, 1, 1, 2]),
   (340480, [1, 4]),
   ((389120 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_18_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_18)) skA_E1_Q0_18 := by decide +kernel

def skA_E1_Q0_19 : SectorVector := [(-1,
  [((577152 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (577152, [0, 1, 1, 3]),
   (505008, [0, 1, 2, 2]),
   ((577152 : Rat)/5, [0, 5]),
   (-1923840, [1, 1, 1, 2]),
   (-1010016, [1, 4]),
   (-769536, [2, 3])]),
 (1,
  [((-577152 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-577152, [0, 1, 1, 3]),
   (-505008, [0, 1, 2, 2]),
   ((-577152 : Rat)/5, [0, 5]),
   (-1923840, [1, 1, 1, 2]),
   (-1010016, [1, 4]),
   (-769536, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_19_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_19)) skA_E1_Q0_19 := by decide +kernel

def skA_E1_Q0_20 : SectorVector := [(-1,
  [((-260096 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-130048, [0, 1, 1, 3]),
   (12192, [0, 1, 2, 2]),
   ((-36576 : Rat)/5, [0, 5]),
   (130048, [1, 1, 1, 2]),
   (195072, [1, 4]),
   (32512, [2, 3])]),
 (1,
  [((260096 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (130048, [0, 1, 1, 3]),
   (-12192, [0, 1, 2, 2]),
   ((36576 : Rat)/5, [0, 5]),
   (130048, [1, 1, 1, 2]),
   (195072, [1, 4]),
   (32512, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_20_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_20)) skA_E1_Q0_20 := by decide +kernel

def skA_E1_Q0_21 : SectorVector := [(-1,
  [(-99328, [0, 1, 1, 1, 1, 1]),
   (-155200, [0, 1, 1, 3]),
   (-23280, [0, 1, 2, 2]),
   (-37248, [0, 5]),
   (496640, [1, 1, 1, 2]),
   (186240, [1, 4]),
   (77600, [2, 3])]),
 (1,
  [(99328, [0, 1, 1, 1, 1, 1]),
   (155200, [0, 1, 1, 3]),
   (23280, [0, 1, 2, 2]),
   (37248, [0, 5]),
   (496640, [1, 1, 1, 2]),
   (186240, [1, 4]),
   (77600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_21_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_21)) skA_E1_Q0_21 := by decide +kernel

def skA_E1_Q0_22 : SectorVector := [(-1,
  [((-487424 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((152320 : Rat)/27, [0, 1, 1, 3]),
   ((-152320 : Rat)/9, [0, 1, 2, 2]),
   ((-60928 : Rat)/9, [0, 5]),
   ((1218560 : Rat)/9, [1, 1, 1, 2]),
   ((609280 : Rat)/9, [1, 4]),
   ((-38080 : Rat)/9, [2, 3])]),
 (1,
  [((487424 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-152320 : Rat)/27, [0, 1, 1, 3]),
   ((152320 : Rat)/9, [0, 1, 2, 2]),
   ((60928 : Rat)/9, [0, 5]),
   ((1218560 : Rat)/9, [1, 1, 1, 2]),
   ((609280 : Rat)/9, [1, 4]),
   ((-38080 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_22_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_22)) skA_E1_Q0_22 := by decide +kernel

def skA_E1_Q0_23 : SectorVector := [(-1,
  [((149504 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((373760 : Rat)/3, [0, 1, 1, 3]),
   (46720, [0, 1, 2, 2]),
   (18688, [0, 5]),
   (-373760, [1, 1, 1, 2]),
   (-186880, [1, 4]),
   (-93440, [2, 3])]),
 (1,
  [((-149504 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-373760 : Rat)/3, [0, 1, 1, 3]),
   (-46720, [0, 1, 2, 2]),
   (-18688, [0, 5]),
   (-373760, [1, 1, 1, 2]),
   (-186880, [1, 4]),
   (-93440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_23_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_23)) skA_E1_Q0_23 := by decide +kernel

def skA_E1_Q0_24 : SectorVector := [(-1,
  [(-24064, [0, 1, 1, 1, 1, 1]),
   (-37600, [0, 1, 1, 3]),
   (-45120, [0, 1, 2, 2]),
   (-9024, [0, 5]),
   (240640, [1, 1, 1, 2]),
   (90240, [1, 4]),
   (37600, [2, 3])]),
 (1,
  [(24064, [0, 1, 1, 1, 1, 1]),
   (37600, [0, 1, 1, 3]),
   (45120, [0, 1, 2, 2]),
   (9024, [0, 5]),
   (240640, [1, 1, 1, 2]),
   (90240, [1, 4]),
   (37600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_24_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_24)) skA_E1_Q0_24 := by decide +kernel

def skA_E1_Q0_25 : SectorVector := [(-1,
  [(-52992, [0, 1, 1, 1, 1, 1]),
   (-132480, [0, 1, 1, 3]),
   (-99360, [0, 1, 2, 2]),
   (-19872, [0, 5]),
   (529920, [1, 1, 1, 2]),
   (99360, [1, 4]),
   (132480, [2, 3])]),
 (1,
  [(52992, [0, 1, 1, 1, 1, 1]),
   (132480, [0, 1, 1, 3]),
   (99360, [0, 1, 2, 2]),
   (19872, [0, 5]),
   (529920, [1, 1, 1, 2]),
   (99360, [1, 4]),
   (132480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_25_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_25)) skA_E1_Q0_25 := by decide +kernel

def skA_E1_Q0_26 : SectorVector := [(-1,
  [((-318976 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-159488, [0, 1, 1, 3]),
   (-119616, [0, 1, 2, 2]),
   ((-44856 : Rat)/5, [0, 5]),
   (637952, [1, 1, 1, 2]),
   (239232, [1, 4]),
   (159488, [2, 3])]),
 (1,
  [((318976 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (159488, [0, 1, 1, 3]),
   (119616, [0, 1, 2, 2]),
   ((44856 : Rat)/5, [0, 5]),
   (637952, [1, 1, 1, 2]),
   (239232, [1, 4]),
   (159488, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q0_26_cert : VectorCertificate (Tpow 0 (aLeft false (5 : ℤ) skM_E1_26)) skA_E1_Q0_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_0_join : VectorCertificate ([skA_E1_Q0_0, skA_E1_Q0_1, skA_E1_Q0_2, skA_E1_Q0_3, skA_E1_Q0_4, skA_E1_Q0_5, skA_E1_Q0_6, skA_E1_Q0_7, skA_E1_Q0_8, skA_E1_Q0_9, skA_E1_Q0_10, skA_E1_Q0_11, skA_E1_Q0_12, skA_E1_Q0_13, skA_E1_Q0_14, skA_E1_Q0_15, skA_E1_Q0_16, skA_E1_Q0_17, skA_E1_Q0_18, skA_E1_Q0_19, skA_E1_Q0_20, skA_E1_Q0_21, skA_E1_Q0_22, skA_E1_Q0_23, skA_E1_Q0_24, skA_E1_Q0_25, skA_E1_Q0_26] : List SectorVector).flatten skQ_E1_0 := by decide +kernel

theorem skQ_E1_0_val : evaluate skQ_E1_0 = evaluate (OrbSgl.vTerm false skY_E1 1 0) :=
  vTerm_of_chunks false skY_E1 1 0 (5 : ℤ) (by norm_num) skM_E1 [skA_E1_Q0_0, skA_E1_Q0_1, skA_E1_Q0_2, skA_E1_Q0_3, skA_E1_Q0_4, skA_E1_Q0_5, skA_E1_Q0_6, skA_E1_Q0_7, skA_E1_Q0_8, skA_E1_Q0_9, skA_E1_Q0_10, skA_E1_Q0_11, skA_E1_Q0_12, skA_E1_Q0_13, skA_E1_Q0_14, skA_E1_Q0_15, skA_E1_Q0_16, skA_E1_Q0_17, skA_E1_Q0_18, skA_E1_Q0_19, skA_E1_Q0_20, skA_E1_Q0_21, skA_E1_Q0_22, skA_E1_Q0_23, skA_E1_Q0_24, skA_E1_Q0_25, skA_E1_Q0_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q0_0_cert (List.Forall₂.cons skA_E1_Q0_1_cert (List.Forall₂.cons skA_E1_Q0_2_cert (List.Forall₂.cons skA_E1_Q0_3_cert (List.Forall₂.cons skA_E1_Q0_4_cert (List.Forall₂.cons skA_E1_Q0_5_cert (List.Forall₂.cons skA_E1_Q0_6_cert (List.Forall₂.cons skA_E1_Q0_7_cert (List.Forall₂.cons skA_E1_Q0_8_cert (List.Forall₂.cons skA_E1_Q0_9_cert (List.Forall₂.cons skA_E1_Q0_10_cert (List.Forall₂.cons skA_E1_Q0_11_cert (List.Forall₂.cons skA_E1_Q0_12_cert (List.Forall₂.cons skA_E1_Q0_13_cert (List.Forall₂.cons skA_E1_Q0_14_cert (List.Forall₂.cons skA_E1_Q0_15_cert (List.Forall₂.cons skA_E1_Q0_16_cert (List.Forall₂.cons skA_E1_Q0_17_cert (List.Forall₂.cons skA_E1_Q0_18_cert (List.Forall₂.cons skA_E1_Q0_19_cert (List.Forall₂.cons skA_E1_Q0_20_cert (List.Forall₂.cons skA_E1_Q0_21_cert (List.Forall₂.cons skA_E1_Q0_22_cert (List.Forall₂.cons skA_E1_Q0_23_cert (List.Forall₂.cons skA_E1_Q0_24_cert (List.Forall₂.cons skA_E1_Q0_25_cert (List.Forall₂.cons skA_E1_Q0_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_0 skQ_E1_0_join

def skA_E1_Q1_0 : SectorVector := [(1,
  [((-36634624 : Rat)/189, [0, 1, 1, 1, 1, 1]),
   ((191627264 : Rat)/189, [0, 1, 1, 3]),
   ((-11272192 : Rat)/63, [0, 1, 2, 2]),
   ((-90177536 : Rat)/63, [0, 5]),
   ((259260416 : Rat)/189, [1, 1, 1, 2]),
   ((-90177536 : Rat)/63, [1, 4]),
   ((-450887680 : Rat)/189, [2, 3])]),
 (-1,
  [((36634624 : Rat)/189, [0, 1, 1, 1, 1, 1]),
   ((-191627264 : Rat)/189, [0, 1, 1, 3]),
   ((11272192 : Rat)/63, [0, 1, 2, 2]),
   ((90177536 : Rat)/63, [0, 5]),
   ((259260416 : Rat)/189, [1, 1, 1, 2]),
   ((-90177536 : Rat)/63, [1, 4]),
   ((-450887680 : Rat)/189, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_0_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_0)) skA_E1_Q1_0 := by decide +kernel

def skA_E1_Q1_1 : SectorVector := [(1,
  [((-1024 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((8192 : Rat)/3, [0, 1, 1, 3]),
   (-40960, [0, 1, 2, 2]),
   (-32768, [0, 5]),
   ((290816 : Rat)/3, [1, 1, 1, 2]),
   (-131072, [1, 4]),
   ((-851968 : Rat)/3, [2, 3])]),
 (-1,
  [((1024 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-8192 : Rat)/3, [0, 1, 1, 3]),
   (40960, [0, 1, 2, 2]),
   (32768, [0, 5]),
   ((290816 : Rat)/3, [1, 1, 1, 2]),
   (-131072, [1, 4]),
   ((-851968 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_1_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_1)) skA_E1_Q1_1 := by decide +kernel

def skA_E1_Q1_2 : SectorVector := [(1,
  [((2996224 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-9777152 : Rat)/9, [0, 1, 1, 3]),
   ((-4100096 : Rat)/3, [0, 1, 2, 2]),
   ((-10092544 : Rat)/3, [0, 5]),
   ((23339008 : Rat)/9, [1, 1, 1, 2]),
   ((-32800768 : Rat)/3, [1, 4]),
   ((-73170944 : Rat)/9, [2, 3])]),
 (-1,
  [((-2996224 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((9777152 : Rat)/9, [0, 1, 1, 3]),
   ((4100096 : Rat)/3, [0, 1, 2, 2]),
   ((10092544 : Rat)/3, [0, 5]),
   ((23339008 : Rat)/9, [1, 1, 1, 2]),
   ((-32800768 : Rat)/3, [1, 4]),
   ((-73170944 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_2_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_2)) skA_E1_Q1_2 := by decide +kernel

def skA_E1_Q1_3 : SectorVector := [(1,
  [(658944, [0, 1, 1, 1, 1, 1]),
   (-4073472, [0, 1, 1, 3]),
   (239616, [0, 1, 2, 2]),
   (-3833856, [0, 5]),
   (1677312, [1, 1, 1, 2]),
   (-19169280, [1, 4]),
   (-1916928, [2, 3])]),
 (-1,
  [(-658944, [0, 1, 1, 1, 1, 1]),
   (4073472, [0, 1, 1, 3]),
   (-239616, [0, 1, 2, 2]),
   (3833856, [0, 5]),
   (1677312, [1, 1, 1, 2]),
   (-19169280, [1, 4]),
   (-1916928, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_3_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_3)) skA_E1_Q1_3 := by decide +kernel

def skA_E1_Q1_4 : SectorVector := [(1,
  [(-111936, [0, 1, 1, 1, 1, 1]),
   (814080, [0, 1, 1, 3]),
   (814080, [0, 1, 2, 2]),
   (651264, [0, 5]),
   (203520, [1, 1, 1, 2]),
   (3256320, [1, 4]),
   (3256320, [2, 3])]),
 (-1,
  [(111936, [0, 1, 1, 1, 1, 1]),
   (-814080, [0, 1, 1, 3]),
   (-814080, [0, 1, 2, 2]),
   (-651264, [0, 5]),
   (203520, [1, 1, 1, 2]),
   (3256320, [1, 4]),
   (3256320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_4_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_4)) skA_E1_Q1_4 := by decide +kernel

def skA_E1_Q1_5 : SectorVector := [(1,
  [(-443584, [0, 1, 1, 1, 1, 1]),
   (5567744, [0, 1, 1, 3]),
   (3120384, [0, 1, 2, 2]),
   (2936832, [0, 5]),
   (4833536, [1, 1, 1, 2]),
   (17620992, [1, 4]),
   (9789440, [2, 3])]),
 (-1,
  [(443584, [0, 1, 1, 1, 1, 1]),
   (-5567744, [0, 1, 1, 3]),
   (-3120384, [0, 1, 2, 2]),
   (-2936832, [0, 5]),
   (4833536, [1, 1, 1, 2]),
   (17620992, [1, 4]),
   (9789440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_5_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_5)) skA_E1_Q1_5 := by decide +kernel

def skA_E1_Q1_6 : SectorVector := [(1,
  [((-1164640 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((12208640 : Rat)/3, [0, 1, 1, 3]),
   (4497920, [0, 1, 2, 2]),
   (1285120, [0, 5]),
   ((18473600 : Rat)/3, [1, 1, 1, 2]),
   (8995840, [1, 4]),
   ((37268480 : Rat)/3, [2, 3])]),
 (-1,
  [((1164640 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-12208640 : Rat)/3, [0, 1, 1, 3]),
   (-4497920, [0, 1, 2, 2]),
   (-1285120, [0, 5]),
   ((18473600 : Rat)/3, [1, 1, 1, 2]),
   (8995840, [1, 4]),
   ((37268480 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_6_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_6)) skA_E1_Q1_6 := by decide +kernel

def skA_E1_Q1_7 : SectorVector := [(1,
  [(56320, [0, 1, 1, 1, 1, 1]),
   (3182080, [0, 1, 1, 3]),
   (1098240, [0, 1, 2, 2]),
   (675840, [0, 5]),
   (3942400, [1, 1, 1, 2]),
   (8110080, [1, 4]),
   (2928640, [2, 3])]),
 (-1,
  [(-56320, [0, 1, 1, 1, 1, 1]),
   (-3182080, [0, 1, 1, 3]),
   (-1098240, [0, 1, 2, 2]),
   (-675840, [0, 5]),
   (3942400, [1, 1, 1, 2]),
   (8110080, [1, 4]),
   (2928640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_7_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_7)) skA_E1_Q1_7 := by decide +kernel

def skA_E1_Q1_8 : SectorVector := [(1,
  [((158720 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((5515520 : Rat)/9, [0, 1, 1, 3]),
   ((1944320 : Rat)/3, [0, 1, 2, 2]),
   ((1269760 : Rat)/3, [0, 5]),
   ((16348160 : Rat)/9, [1, 1, 1, 2]),
   ((4126720 : Rat)/3, [1, 4]),
   ((9205760 : Rat)/9, [2, 3])]),
 (-1,
  [((-158720 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-5515520 : Rat)/9, [0, 1, 1, 3]),
   ((-1944320 : Rat)/3, [0, 1, 2, 2]),
   ((-1269760 : Rat)/3, [0, 5]),
   ((16348160 : Rat)/9, [1, 1, 1, 2]),
   ((4126720 : Rat)/3, [1, 4]),
   ((9205760 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_8_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_8)) skA_E1_Q1_8 := by decide +kernel

def skA_E1_Q1_9 : SectorVector := [(1,
  [(-43520, [0, 1, 1, 1, 1, 1]),
   (-3176960, [0, 1, 1, 3]),
   (-2480640, [0, 1, 2, 2]),
   (-1044480, [0, 5]),
   (-5918720, [1, 1, 1, 2]),
   (-7311360, [1, 4]),
   (-5918720, [2, 3])]),
 (-1,
  [(43520, [0, 1, 1, 1, 1, 1]),
   (3176960, [0, 1, 1, 3]),
   (2480640, [0, 1, 2, 2]),
   (1044480, [0, 5]),
   (-5918720, [1, 1, 1, 2]),
   (-7311360, [1, 4]),
   (-5918720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_9_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_9)) skA_E1_Q1_9 := by decide +kernel

def skA_E1_Q1_10 : SectorVector := [(1,
  [(-337920, [0, 1, 1, 1, 1, 1]),
   (-1203840, [0, 1, 1, 3]),
   (-274560, [0, 1, 2, 2]),
   (-675840, [0, 5]),
   (-2787840, [1, 1, 1, 2]),
   (-3886080, [1, 4]),
   (-506880, [2, 3])]),
 (-1,
  [(337920, [0, 1, 1, 1, 1, 1]),
   (1203840, [0, 1, 1, 3]),
   (274560, [0, 1, 2, 2]),
   (675840, [0, 5]),
   (-2787840, [1, 1, 1, 2]),
   (-3886080, [1, 4]),
   (-506880, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_10_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_10)) skA_E1_Q1_10 := by decide +kernel

def skA_E1_Q1_11 : SectorVector := [(1,
  [((2085120 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((14986800 : Rat)/7, [0, 1, 1, 3]),
   ((8731440 : Rat)/7, [0, 1, 2, 2]),
   ((4170240 : Rat)/7, [0, 5]),
   ((34925760 : Rat)/7, [1, 1, 1, 2]),
   ((33361920 : Rat)/7, [1, 4]),
   ((16680960 : Rat)/7, [2, 3])]),
 (-1,
  [((-2085120 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-14986800 : Rat)/7, [0, 1, 1, 3]),
   ((-8731440 : Rat)/7, [0, 1, 2, 2]),
   ((-4170240 : Rat)/7, [0, 5]),
   ((34925760 : Rat)/7, [1, 1, 1, 2]),
   ((33361920 : Rat)/7, [1, 4]),
   ((16680960 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_11_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_11)) skA_E1_Q1_11 := by decide +kernel

def skA_E1_Q1_12 : SectorVector := [(1,
  [(756480, [0, 1, 1, 1, 1, 1]),
   (5106240, [0, 1, 1, 3]),
   (4728000, [0, 1, 2, 2]),
   (1512960, [0, 5]),
   (15886080, [1, 1, 1, 2]),
   (8699520, [1, 4]),
   (7943040, [2, 3])]),
 (-1,
  [(-756480, [0, 1, 1, 1, 1, 1]),
   (-5106240, [0, 1, 1, 3]),
   (-4728000, [0, 1, 2, 2]),
   (-1512960, [0, 5]),
   (15886080, [1, 1, 1, 2]),
   (8699520, [1, 4]),
   (7943040, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_12_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_12)) skA_E1_Q1_12 := by decide +kernel

def skA_E1_Q1_13 : SectorVector := [(1,
  [(891648, [0, 1, 1, 1, 1, 1]),
   (7356096, [0, 1, 1, 3]),
   (5572800, [0, 1, 2, 2]),
   (891648, [0, 5]),
   (18724608, [1, 1, 1, 2]),
   (12483072, [1, 4]),
   (10699776, [2, 3])]),
 (-1,
  [(-891648, [0, 1, 1, 1, 1, 1]),
   (-7356096, [0, 1, 1, 3]),
   (-5572800, [0, 1, 2, 2]),
   (-891648, [0, 5]),
   (18724608, [1, 1, 1, 2]),
   (12483072, [1, 4]),
   (10699776, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_13_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_13)) skA_E1_Q1_13 := by decide +kernel

def skA_E1_Q1_14 : SectorVector := [(1,
  [(-139264, [0, 1, 1, 1, 1, 1]),
   (-165376, [0, 1, 1, 3]),
   (104448, [0, 1, 2, 2]),
   (-104448, [0, 5]),
   (-243712, [1, 1, 1, 2]),
   (-940032, [1, 4]),
   (-139264, [2, 3])]),
 (-1,
  [(139264, [0, 1, 1, 1, 1, 1]),
   (165376, [0, 1, 1, 3]),
   (-104448, [0, 1, 2, 2]),
   (104448, [0, 5]),
   (-243712, [1, 1, 1, 2]),
   (-940032, [1, 4]),
   (-139264, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_14_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_14)) skA_E1_Q1_14 := by decide +kernel

def skA_E1_Q1_15 : SectorVector := [(1,
  [(885760, [0, 1, 1, 1, 1, 1]),
   (2546560, [0, 1, 1, 3]),
   (1079520, [0, 1, 2, 2]),
   (664320, [0, 5]),
   (7528960, [1, 1, 1, 2]),
   (5978880, [1, 4]),
   (1882240, [2, 3])]),
 (-1,
  [(-885760, [0, 1, 1, 1, 1, 1]),
   (-2546560, [0, 1, 1, 3]),
   (-1079520, [0, 1, 2, 2]),
   (-664320, [0, 5]),
   (7528960, [1, 1, 1, 2]),
   (5978880, [1, 4]),
   (1882240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_15_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_15)) skA_E1_Q1_15 := by decide +kernel

def skA_E1_Q1_16 : SectorVector := [(1,
  [(1675264, [0, 1, 1, 1, 1, 1]),
   (4659328, [0, 1, 1, 3]),
   (3455232, [0, 1, 2, 2]),
   (1256448, [0, 5]),
   (18009088, [1, 1, 1, 2]),
   (8009856, [1, 4]),
   (4345216, [2, 3])]),
 (-1,
  [(-1675264, [0, 1, 1, 1, 1, 1]),
   (-4659328, [0, 1, 1, 3]),
   (-3455232, [0, 1, 2, 2]),
   (-1256448, [0, 5]),
   (18009088, [1, 1, 1, 2]),
   (8009856, [1, 4]),
   (4345216, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_16_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_16)) skA_E1_Q1_16 := by decide +kernel

def skA_E1_Q1_17 : SectorVector := [(1,
  [(814080, [0, 1, 1, 1, 1, 1]),
   (2798400, [0, 1, 1, 3]),
   (1679040, [0, 1, 2, 2]),
   (8751360, [1, 1, 1, 2]),
   (4273920, [1, 4]),
   (2645760, [2, 3])]),
 (-1,
  [(-814080, [0, 1, 1, 1, 1, 1]),
   (-2798400, [0, 1, 1, 3]),
   (-1679040, [0, 1, 2, 2]),
   (8751360, [1, 1, 1, 2]),
   (4273920, [1, 4]),
   (2645760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_17_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_17)) skA_E1_Q1_17 := by decide +kernel

def skA_E1_Q1_18 : SectorVector := [(1,
  [((1556480 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((4183040 : Rat)/3, [0, 1, 1, 3]),
   (1556480, [0, 1, 2, 2]),
   (194560, [0, 5]),
   ((20234240 : Rat)/3, [1, 1, 1, 2]),
   (1070080, [1, 4]),
   ((5350400 : Rat)/3, [2, 3])]),
 (-1,
  [((-1556480 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-4183040 : Rat)/3, [0, 1, 1, 3]),
   (-1556480, [0, 1, 2, 2]),
   (-194560, [0, 5]),
   ((20234240 : Rat)/3, [1, 1, 1, 2]),
   (1070080, [1, 4]),
   ((5350400 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_18_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_18)) skA_E1_Q1_18 := by decide +kernel

def skA_E1_Q1_19 : SectorVector := [(1,
  [(-769536, [0, 1, 1, 1, 1, 1]),
   (-3078144, [0, 1, 1, 3]),
   (-2308608, [0, 1, 2, 2]),
   (-577152, [0, 5]),
   (-10003968, [1, 1, 1, 2]),
   (-5194368, [1, 4]),
   (-3655296, [2, 3])]),
 (-1,
  [(769536, [0, 1, 1, 1, 1, 1]),
   (3078144, [0, 1, 1, 3]),
   (2308608, [0, 1, 2, 2]),
   (577152, [0, 5]),
   (-10003968, [1, 1, 1, 2]),
   (-5194368, [1, 4]),
   (-3655296, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_19_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_19)) skA_E1_Q1_19 := by decide +kernel

def skA_E1_Q1_20 : SectorVector := [(1,
  [(260096, [0, 1, 1, 1, 1, 1]),
   (357632, [0, 1, 1, 3]),
   (85344, [0, 1, 2, 2]),
   (97536, [0, 5]),
   (1430528, [1, 1, 1, 2]),
   (975360, [1, 4]),
   (211328, [2, 3])]),
 (-1,
  [(-260096, [0, 1, 1, 1, 1, 1]),
   (-357632, [0, 1, 1, 3]),
   (-85344, [0, 1, 2, 2]),
   (-97536, [0, 5]),
   (1430528, [1, 1, 1, 2]),
   (975360, [1, 4]),
   (211328, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_20_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_20)) skA_E1_Q1_20 := by decide +kernel

def skA_E1_Q1_21 : SectorVector := [(1,
  [(496640, [0, 1, 1, 1, 1, 1]),
   (682880, [0, 1, 1, 3]),
   (395760, [0, 1, 2, 2]),
   (93120, [0, 5]),
   (3476480, [1, 1, 1, 2]),
   (1117440, [1, 4]),
   (403520, [2, 3])]),
 (-1,
  [(-496640, [0, 1, 1, 1, 1, 1]),
   (-682880, [0, 1, 1, 3]),
   (-395760, [0, 1, 2, 2]),
   (-93120, [0, 5]),
   (3476480, [1, 1, 1, 2]),
   (1117440, [1, 4]),
   (403520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_21_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_21)) skA_E1_Q1_21 := by decide +kernel

def skA_E1_Q1_22 : SectorVector := [(1,
  [((2437120 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((2437120 : Rat)/27, [0, 1, 1, 3]),
   ((1066240 : Rat)/9, [0, 1, 2, 2]),
   ((304640 : Rat)/9, [0, 5]),
   ((20715520 : Rat)/27, [1, 1, 1, 2]),
   ((304640 : Rat)/9, [1, 4]),
   ((1523200 : Rat)/27, [2, 3])]),
 (-1,
  [((-2437120 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-2437120 : Rat)/27, [0, 1, 1, 3]),
   ((-1066240 : Rat)/9, [0, 1, 2, 2]),
   ((-304640 : Rat)/9, [0, 5]),
   ((20715520 : Rat)/27, [1, 1, 1, 2]),
   ((304640 : Rat)/9, [1, 4]),
   ((1523200 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_22_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_22)) skA_E1_Q1_22 := by decide +kernel

def skA_E1_Q1_23 : SectorVector := [(1,
  [((-747520 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-1588480 : Rat)/3, [0, 1, 1, 3]),
   (-327040, [0, 1, 2, 2]),
   (-93440, [0, 5]),
   ((-6353920 : Rat)/3, [1, 1, 1, 2]),
   (-934400, [1, 4]),
   ((-1308160 : Rat)/3, [2, 3])]),
 (-1,
  [((747520 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((1588480 : Rat)/3, [0, 1, 1, 3]),
   (327040, [0, 1, 2, 2]),
   (93440, [0, 5]),
   ((-6353920 : Rat)/3, [1, 1, 1, 2]),
   (-934400, [1, 4]),
   ((-1308160 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_23_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_23)) skA_E1_Q1_23 := by decide +kernel

def skA_E1_Q1_24 : SectorVector := [(1,
  [(120320, [0, 1, 1, 1, 1, 1]),
   (255680, [0, 1, 1, 3]),
   (225600, [0, 1, 2, 2]),
   (45120, [0, 5]),
   (1203200, [1, 1, 1, 2]),
   (315840, [1, 4]),
   (255680, [2, 3])]),
 (-1,
  [(-120320, [0, 1, 1, 1, 1, 1]),
   (-255680, [0, 1, 1, 3]),
   (-225600, [0, 1, 2, 2]),
   (-45120, [0, 5]),
   (1203200, [1, 1, 1, 2]),
   (315840, [1, 4]),
   (255680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_24_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_24)) skA_E1_Q1_24 := by decide +kernel

def skA_E1_Q1_25 : SectorVector := [(1,
  [(264960, [0, 1, 1, 1, 1, 1]),
   (662400, [0, 1, 1, 3]),
   (496800, [0, 1, 2, 2]),
   (49680, [0, 5]),
   (2649600, [1, 1, 1, 2]),
   (894240, [1, 4]),
   (662400, [2, 3])]),
 (-1,
  [(-264960, [0, 1, 1, 1, 1, 1]),
   (-662400, [0, 1, 1, 3]),
   (-496800, [0, 1, 2, 2]),
   (-49680, [0, 5]),
   (2649600, [1, 1, 1, 2]),
   (894240, [1, 4]),
   (662400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_25_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_25)) skA_E1_Q1_25 := by decide +kernel

def skA_E1_Q1_26 : SectorVector := [(1,
  [(318976, [0, 1, 1, 1, 1, 1]),
   (797440, [0, 1, 1, 3]),
   (598080, [0, 1, 2, 2]),
   (119616, [0, 5]),
   (3189760, [1, 1, 1, 2]),
   (1196160, [1, 4]),
   (797440, [2, 3])]),
 (-1,
  [(-318976, [0, 1, 1, 1, 1, 1]),
   (-797440, [0, 1, 1, 3]),
   (-598080, [0, 1, 2, 2]),
   (-119616, [0, 5]),
   (3189760, [1, 1, 1, 2]),
   (1196160, [1, 4]),
   (797440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q1_26_cert : VectorCertificate (Tpow 1 (aLeft false (6 : ℤ) skM_E1_26)) skA_E1_Q1_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_1_join : VectorCertificate ([skA_E1_Q1_0, skA_E1_Q1_1, skA_E1_Q1_2, skA_E1_Q1_3, skA_E1_Q1_4, skA_E1_Q1_5, skA_E1_Q1_6, skA_E1_Q1_7, skA_E1_Q1_8, skA_E1_Q1_9, skA_E1_Q1_10, skA_E1_Q1_11, skA_E1_Q1_12, skA_E1_Q1_13, skA_E1_Q1_14, skA_E1_Q1_15, skA_E1_Q1_16, skA_E1_Q1_17, skA_E1_Q1_18, skA_E1_Q1_19, skA_E1_Q1_20, skA_E1_Q1_21, skA_E1_Q1_22, skA_E1_Q1_23, skA_E1_Q1_24, skA_E1_Q1_25, skA_E1_Q1_26] : List SectorVector).flatten skQ_E1_1 := by decide +kernel

theorem skQ_E1_1_val : evaluate skQ_E1_1 = evaluate (OrbSgl.vTerm false skY_E1 1 1) :=
  vTerm_of_chunks false skY_E1 1 1 (6 : ℤ) (by norm_num) skM_E1 [skA_E1_Q1_0, skA_E1_Q1_1, skA_E1_Q1_2, skA_E1_Q1_3, skA_E1_Q1_4, skA_E1_Q1_5, skA_E1_Q1_6, skA_E1_Q1_7, skA_E1_Q1_8, skA_E1_Q1_9, skA_E1_Q1_10, skA_E1_Q1_11, skA_E1_Q1_12, skA_E1_Q1_13, skA_E1_Q1_14, skA_E1_Q1_15, skA_E1_Q1_16, skA_E1_Q1_17, skA_E1_Q1_18, skA_E1_Q1_19, skA_E1_Q1_20, skA_E1_Q1_21, skA_E1_Q1_22, skA_E1_Q1_23, skA_E1_Q1_24, skA_E1_Q1_25, skA_E1_Q1_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q1_0_cert (List.Forall₂.cons skA_E1_Q1_1_cert (List.Forall₂.cons skA_E1_Q1_2_cert (List.Forall₂.cons skA_E1_Q1_3_cert (List.Forall₂.cons skA_E1_Q1_4_cert (List.Forall₂.cons skA_E1_Q1_5_cert (List.Forall₂.cons skA_E1_Q1_6_cert (List.Forall₂.cons skA_E1_Q1_7_cert (List.Forall₂.cons skA_E1_Q1_8_cert (List.Forall₂.cons skA_E1_Q1_9_cert (List.Forall₂.cons skA_E1_Q1_10_cert (List.Forall₂.cons skA_E1_Q1_11_cert (List.Forall₂.cons skA_E1_Q1_12_cert (List.Forall₂.cons skA_E1_Q1_13_cert (List.Forall₂.cons skA_E1_Q1_14_cert (List.Forall₂.cons skA_E1_Q1_15_cert (List.Forall₂.cons skA_E1_Q1_16_cert (List.Forall₂.cons skA_E1_Q1_17_cert (List.Forall₂.cons skA_E1_Q1_18_cert (List.Forall₂.cons skA_E1_Q1_19_cert (List.Forall₂.cons skA_E1_Q1_20_cert (List.Forall₂.cons skA_E1_Q1_21_cert (List.Forall₂.cons skA_E1_Q1_22_cert (List.Forall₂.cons skA_E1_Q1_23_cert (List.Forall₂.cons skA_E1_Q1_24_cert (List.Forall₂.cons skA_E1_Q1_25_cert (List.Forall₂.cons skA_E1_Q1_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_1 skQ_E1_1_join

def skA_E1_Q2_0 : SectorVector := [(-1,
  [((45088768 : Rat)/189, [0, 1, 1, 1, 1, 1]),
   ((349437952 : Rat)/189, [0, 1, 1, 3]),
   ((-90177536 : Rat)/63, [0, 1, 2, 2]),
   ((360710144 : Rat)/63, [0, 5]),
   ((495976448 : Rat)/189, [1, 1, 1, 2]),
   ((-1239941120 : Rat)/63, [1, 4]),
   ((-112721920 : Rat)/189, [2, 3])]),
 (1,
  [((-45088768 : Rat)/189, [0, 1, 1, 1, 1, 1]),
   ((-349437952 : Rat)/189, [0, 1, 1, 3]),
   ((90177536 : Rat)/63, [0, 1, 2, 2]),
   ((-360710144 : Rat)/63, [0, 5]),
   ((495976448 : Rat)/189, [1, 1, 1, 2]),
   ((-1239941120 : Rat)/63, [1, 4]),
   ((-112721920 : Rat)/189, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_0_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_0)) skA_E1_Q2_0 := by decide +kernel

def skA_E1_Q2_1 : SectorVector := [(-1,
  [((-139264 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((813056 : Rat)/3, [0, 1, 1, 3]),
   (63488, [0, 1, 2, 2]),
   (262144, [0, 5]),
   ((188416 : Rat)/3, [1, 1, 1, 2]),
   (-1245184, [1, 4]),
   ((-1114112 : Rat)/3, [2, 3])]),
 (1,
  [((139264 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-813056 : Rat)/3, [0, 1, 1, 3]),
   (-63488, [0, 1, 2, 2]),
   (-262144, [0, 5]),
   ((188416 : Rat)/3, [1, 1, 1, 2]),
   (-1245184, [1, 4]),
   ((-1114112 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_1_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_1)) skA_E1_Q2_1 := by decide +kernel

def skA_E1_Q2_2 : SectorVector := [(-1,
  [((-25231360 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((122372096 : Rat)/9, [0, 1, 1, 3]),
   ((16400384 : Rat)/3, [0, 1, 2, 2]),
   ((25231360 : Rat)/3, [0, 5]),
   ((-5046272 : Rat)/9, [1, 1, 1, 2]),
   ((-146341888 : Rat)/3, [1, 4]),
   ((-186712064 : Rat)/9, [2, 3])]),
 (1,
  [((25231360 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-122372096 : Rat)/9, [0, 1, 1, 3]),
   ((-16400384 : Rat)/3, [0, 1, 2, 2]),
   ((-25231360 : Rat)/3, [0, 5]),
   ((-5046272 : Rat)/9, [1, 1, 1, 2]),
   ((-146341888 : Rat)/3, [1, 4]),
   ((-186712064 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_2_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_2)) skA_E1_Q2_2 := by decide +kernel

def skA_E1_Q2_3 : SectorVector := [(-1,
  [(-2236416, [0, 1, 1, 1, 1, 1]),
   (14297088, [0, 1, 1, 3]),
   (2635776, [0, 1, 2, 2]),
   (15335424, [0, 5]),
   (4153344, [1, 1, 1, 2]),
   (-69967872, [1, 4]),
   (-18849792, [2, 3])]),
 (1,
  [(2236416, [0, 1, 1, 1, 1, 1]),
   (-14297088, [0, 1, 1, 3]),
   (-2635776, [0, 1, 2, 2]),
   (-15335424, [0, 5]),
   (4153344, [1, 1, 1, 2]),
   (-69967872, [1, 4]),
   (-18849792, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_3_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_3)) skA_E1_Q2_3 := by decide +kernel

def skA_E1_Q2_4 : SectorVector := [(-1,
  [(379904, [0, 1, 1, 1, 1, 1]),
   (-5359360, [0, 1, 1, 3]),
   (-2645760, [0, 1, 2, 2]),
   (-2605056, [0, 5]),
   (5155840, [1, 1, 1, 2]),
   (16281600, [1, 4]),
   (7598080, [2, 3])]),
 (1,
  [(-379904, [0, 1, 1, 1, 1, 1]),
   (5359360, [0, 1, 1, 3]),
   (2645760, [0, 1, 2, 2]),
   (2605056, [0, 5]),
   (5155840, [1, 1, 1, 2]),
   (16281600, [1, 4]),
   (7598080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_4_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_4)) skA_E1_Q2_4 := by decide +kernel

def skA_E1_Q2_5 : SectorVector := [(-1,
  [(-489472, [0, 1, 1, 1, 1, 1]),
   (-25819648, [0, 1, 1, 3]),
   (-13582848, [0, 1, 2, 2]),
   (-11747328, [0, 5]),
   (38668288, [1, 1, 1, 2]),
   (73420800, [1, 4]),
   (34263040, [2, 3])]),
 (1,
  [(489472, [0, 1, 1, 1, 1, 1]),
   (25819648, [0, 1, 1, 3]),
   (13582848, [0, 1, 2, 2]),
   (11747328, [0, 5]),
   (38668288, [1, 1, 1, 2]),
   (73420800, [1, 4]),
   (34263040, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_5_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_5)) skA_E1_Q2_5 := by decide +kernel

def skA_E1_Q2_6 : SectorVector := [(-1,
  [((-1285120 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-75500800 : Rat)/3, [0, 1, 1, 3]),
   (-15742720, [0, 1, 2, 2]),
   (-6425600, [0, 5]),
   ((132367360 : Rat)/3, [1, 1, 1, 2]),
   (56545280, [1, 4]),
   ((105379840 : Rat)/3, [2, 3])]),
 (1,
  [((1285120 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((75500800 : Rat)/3, [0, 1, 1, 3]),
   (15742720, [0, 1, 2, 2]),
   (6425600, [0, 5]),
   ((132367360 : Rat)/3, [1, 1, 1, 2]),
   (56545280, [1, 4]),
   ((105379840 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_6_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_6)) skA_E1_Q2_6 := by decide +kernel

def skA_E1_Q2_7 : SectorVector := [(-1,
  [(-2083840, [0, 1, 1, 1, 1, 1]),
   (-11925760, [0, 1, 1, 3]),
   (-6631680, [0, 1, 2, 2]),
   (-5406720, [0, 5]),
   (28103680, [1, 1, 1, 2]),
   (31764480, [1, 4]),
   (13742080, [2, 3])]),
 (1,
  [(2083840, [0, 1, 1, 1, 1, 1]),
   (11925760, [0, 1, 1, 3]),
   (6631680, [0, 1, 2, 2]),
   (5406720, [0, 5]),
   (28103680, [1, 1, 1, 2]),
   (31764480, [1, 4]),
   (13742080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_7_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_7)) skA_E1_Q2_7 := by decide +kernel

def skA_E1_Q2_8 : SectorVector := [(-1,
  [((-5872640 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-35513600 : Rat)/9, [0, 1, 1, 3]),
   ((-8610560 : Rat)/3, [0, 1, 2, 2]),
   ((-1269760 : Rat)/3, [0, 5]),
   ((98247680 : Rat)/9, [1, 1, 1, 2]),
   ((19363840 : Rat)/3, [1, 4]),
   ((45393920 : Rat)/9, [2, 3])]),
 (1,
  [((5872640 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((35513600 : Rat)/9, [0, 1, 1, 3]),
   ((8610560 : Rat)/3, [0, 1, 2, 2]),
   ((1269760 : Rat)/3, [0, 5]),
   ((98247680 : Rat)/9, [1, 1, 1, 2]),
   ((19363840 : Rat)/3, [1, 4]),
   ((45393920 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_8_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_8)) skA_E1_Q2_8 := by decide +kernel

def skA_E1_Q2_9 : SectorVector := [(-1,
  [(1610240, [0, 1, 1, 1, 1, 1]),
   (14437760, [0, 1, 1, 3]),
   (9041280, [0, 1, 2, 2]),
   (4177920, [0, 5]),
   (-32161280, [1, 1, 1, 2]),
   (-32378880, [1, 4]),
   (-18452480, [2, 3])]),
 (1,
  [(-1610240, [0, 1, 1, 1, 1, 1]),
   (-14437760, [0, 1, 1, 3]),
   (-9041280, [0, 1, 2, 2]),
   (-4177920, [0, 5]),
   (-32161280, [1, 1, 1, 2]),
   (-32378880, [1, 4]),
   (-18452480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_9_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_9)) skA_E1_Q2_9 := by decide +kernel

def skA_E1_Q2_10 : SectorVector := [(-1,
  [(2478080, [0, 1, 1, 1, 1, 1]),
   (5012480, [0, 1, 1, 3]),
   (3379200, [0, 1, 2, 2]),
   (1689600, [0, 5]),
   (-21401600, [1, 1, 1, 2]),
   (-9799680, [1, 4]),
   (-4167680, [2, 3])]),
 (1,
  [(-2478080, [0, 1, 1, 1, 1, 1]),
   (-5012480, [0, 1, 1, 3]),
   (-3379200, [0, 1, 2, 2]),
   (-1689600, [0, 5]),
   (-21401600, [1, 1, 1, 2]),
   (-9799680, [1, 4]),
   (-4167680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_10_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_10)) skA_E1_Q2_10 := by decide +kernel

def skA_E1_Q2_11 : SectorVector := [(-1,
  [((-15290880 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-60120960 : Rat)/7, [0, 1, 1, 3]),
   ((-39617280 : Rat)/7, [0, 1, 2, 2]),
   ((-16680960 : Rat)/7, [0, 5]),
   ((182100480 : Rat)/7, [1, 1, 1, 2]),
   ((123022080 : Rat)/7, [1, 4]),
   ((67418880 : Rat)/7, [2, 3])]),
 (1,
  [((15290880 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((60120960 : Rat)/7, [0, 1, 1, 3]),
   ((39617280 : Rat)/7, [0, 1, 2, 2]),
   ((16680960 : Rat)/7, [0, 5]),
   ((182100480 : Rat)/7, [1, 1, 1, 2]),
   ((123022080 : Rat)/7, [1, 4]),
   ((67418880 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_11_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_11)) skA_E1_Q2_11 := by decide +kernel

def skA_E1_Q2_12 : SectorVector := [(-1,
  [(-5547520, [0, 1, 1, 1, 1, 1]),
   (-24837760, [0, 1, 1, 3]),
   (-17777280, [0, 1, 2, 2]),
   (-3782400, [0, 5]),
   (75143680, [1, 1, 1, 2]),
   (42362880, [1, 4]),
   (29754880, [2, 3])]),
 (1,
  [(5547520, [0, 1, 1, 1, 1, 1]),
   (24837760, [0, 1, 1, 3]),
   (17777280, [0, 1, 2, 2]),
   (3782400, [0, 5]),
   (75143680, [1, 1, 1, 2]),
   (42362880, [1, 4]),
   (29754880, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_12_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_12)) skA_E1_Q2_12 := by decide +kernel

def skA_E1_Q2_13 : SectorVector := [(-1,
  [(-6538752, [0, 1, 1, 1, 1, 1]),
   (-31059072, [0, 1, 1, 3]),
   (-20953728, [0, 1, 2, 2]),
   (-7133184, [0, 5]),
   (88570368, [1, 1, 1, 2]),
   (60632064, [1, 4]),
   (36854784, [2, 3])]),
 (1,
  [(6538752, [0, 1, 1, 1, 1, 1]),
   (31059072, [0, 1, 1, 3]),
   (20953728, [0, 1, 2, 2]),
   (7133184, [0, 5]),
   (88570368, [1, 1, 1, 2]),
   (60632064, [1, 4]),
   (36854784, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_13_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_13)) skA_E1_Q2_13 := by decide +kernel

def skA_E1_Q2_14 : SectorVector := [(-1,
  [(696320, [0, 1, 1, 1, 1, 1]),
   (435200, [0, 1, 1, 3]),
   (248064, [0, 1, 2, 2]),
   (417792, [0, 5]),
   (-4143104, [1, 1, 1, 2]),
   (-1122816, [1, 4]),
   (269824, [2, 3])]),
 (1,
  [(-696320, [0, 1, 1, 1, 1, 1]),
   (-435200, [0, 1, 1, 3]),
   (-248064, [0, 1, 2, 2]),
   (-417792, [0, 5]),
   (-4143104, [1, 1, 1, 2]),
   (-1122816, [1, 4]),
   (269824, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_14_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_14)) skA_E1_Q2_14 := by decide +kernel

def skA_E1_Q2_15 : SectorVector := [(-1,
  [(-4428800, [0, 1, 1, 1, 1, 1]),
   (-9743360, [0, 1, 1, 3]),
   (-6809280, [0, 1, 2, 2]),
   (-2657280, [0, 5]),
   (40302080, [1, 1, 1, 2]),
   (17604480, [1, 4]),
   (8746880, [2, 3])]),
 (1,
  [(4428800, [0, 1, 1, 1, 1, 1]),
   (9743360, [0, 1, 1, 3]),
   (6809280, [0, 1, 2, 2]),
   (2657280, [0, 5]),
   (40302080, [1, 1, 1, 2]),
   (17604480, [1, 4]),
   (8746880, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_15_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_15)) skA_E1_Q2_15 := by decide +kernel

def skA_E1_Q2_16 : SectorVector := [(-1,
  [(-8376320, [0, 1, 1, 1, 1, 1]),
   (-21569024, [0, 1, 1, 3]),
   (-16176768, [0, 1, 2, 2]),
   (-3141120, [0, 5]),
   (85019648, [1, 1, 1, 2]),
   (32353536, [1, 4]),
   (21883136, [2, 3])]),
 (1,
  [(8376320, [0, 1, 1, 1, 1, 1]),
   (21569024, [0, 1, 1, 3]),
   (16176768, [0, 1, 2, 2]),
   (3141120, [0, 5]),
   (85019648, [1, 1, 1, 2]),
   (32353536, [1, 4]),
   (21883136, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_16_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_16)) skA_E1_Q2_16 := by decide +kernel

def skA_E1_Q2_17 : SectorVector := [(-1,
  [(-4070400, [0, 1, 1, 1, 1, 1]),
   (-11091840, [0, 1, 1, 3]),
   (-7860960, [0, 1, 2, 2]),
   (-2442240, [0, 5]),
   (41314560, [1, 1, 1, 2]),
   (19385280, [1, 4]),
   (11244480, [2, 3])]),
 (1,
  [(4070400, [0, 1, 1, 1, 1, 1]),
   (11091840, [0, 1, 1, 3]),
   (7860960, [0, 1, 2, 2]),
   (2442240, [0, 5]),
   (41314560, [1, 1, 1, 2]),
   (19385280, [1, 4]),
   (11244480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_17_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_17)) skA_E1_Q2_17 := by decide +kernel

def skA_E1_Q2_18 : SectorVector := [(-1,
  [((-7782400 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-22958080 : Rat)/3, [0, 1, 1, 3]),
   (-6031360, [0, 1, 2, 2]),
   (-389120, [0, 5]),
   ((87162880 : Rat)/3, [1, 1, 1, 2]),
   (9728000, [1, 4]),
   ((25292800 : Rat)/3, [2, 3])]),
 (1,
  [((7782400 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((22958080 : Rat)/3, [0, 1, 1, 3]),
   (6031360, [0, 1, 2, 2]),
   (389120, [0, 5]),
   ((87162880 : Rat)/3, [1, 1, 1, 2]),
   (9728000, [1, 4]),
   ((25292800 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_18_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_18)) skA_E1_Q2_18 := by decide +kernel

def skA_E1_Q2_19 : SectorVector := [(-1,
  [(3847680, [0, 1, 1, 1, 1, 1]),
   (12504960, [0, 1, 1, 3]),
   (8945856, [0, 1, 2, 2]),
   (2308608, [0, 5]),
   (-43094016, [1, 1, 1, 2]),
   (-21354624, [1, 4]),
   (-13659264, [2, 3])]),
 (1,
  [(-3847680, [0, 1, 1, 1, 1, 1]),
   (-12504960, [0, 1, 1, 3]),
   (-8945856, [0, 1, 2, 2]),
   (-2308608, [0, 5]),
   (-43094016, [1, 1, 1, 2]),
   (-21354624, [1, 4]),
   (-13659264, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_19_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_19)) skA_E1_Q2_19 := by decide +kernel

def skA_E1_Q2_20 : SectorVector := [(-1,
  [(-1040384, [0, 1, 1, 1, 1, 1]),
   (-1430528, [0, 1, 1, 3]),
   (-1072896, [0, 1, 2, 2]),
   (-390144, [0, 5]),
   (8062976, [1, 1, 1, 2]),
   (2145792, [1, 4]),
   (845312, [2, 3])]),
 (1,
  [(1040384, [0, 1, 1, 1, 1, 1]),
   (1430528, [0, 1, 1, 3]),
   (1072896, [0, 1, 2, 2]),
   (390144, [0, 5]),
   (8062976, [1, 1, 1, 2]),
   (2145792, [1, 4]),
   (845312, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_20_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_20)) skA_E1_Q2_20 := by decide +kernel

def skA_E1_Q2_21 : SectorVector := [(-1,
  [(-1986560, [0, 1, 1, 1, 1, 1]),
   (-3290240, [0, 1, 1, 3]),
   (-2607360, [0, 1, 2, 2]),
   (-465600, [0, 5]),
   (16885760, [1, 1, 1, 2]),
   (4097280, [1, 4]),
   (2545280, [2, 3])]),
 (1,
  [(1986560, [0, 1, 1, 1, 1, 1]),
   (3290240, [0, 1, 1, 3]),
   (2607360, [0, 1, 2, 2]),
   (465600, [0, 5]),
   (16885760, [1, 1, 1, 2]),
   (4097280, [1, 4]),
   (2545280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_21_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_21)) skA_E1_Q2_21 := by decide +kernel

def skA_E1_Q2_22 : SectorVector := [(-1,
  [((-9748480 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-17973760 : Rat)/27, [0, 1, 1, 3]),
   ((-5178880 : Rat)/9, [0, 1, 2, 2]),
   ((152320 : Rat)/9, [0, 5]),
   ((90173440 : Rat)/27, [1, 1, 1, 2]),
   ((4874240 : Rat)/9, [1, 4]),
   ((16145920 : Rat)/27, [2, 3])]),
 (1,
  [((9748480 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((17973760 : Rat)/27, [0, 1, 1, 3]),
   ((5178880 : Rat)/9, [0, 1, 2, 2]),
   ((-152320 : Rat)/9, [0, 5]),
   ((90173440 : Rat)/27, [1, 1, 1, 2]),
   ((4874240 : Rat)/9, [1, 4]),
   ((16145920 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_22_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_22)) skA_E1_Q2_22 := by decide +kernel

def skA_E1_Q2_23 : SectorVector := [(-1,
  [((2990080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((6353920 : Rat)/3, [0, 1, 1, 3]),
   (1588480, [0, 1, 2, 2]),
   (373760, [0, 5]),
   ((-27658240 : Rat)/3, [1, 1, 1, 2]),
   (-3176960, [1, 4]),
   ((-5793280 : Rat)/3, [2, 3])]),
 (1,
  [((-2990080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-6353920 : Rat)/3, [0, 1, 1, 3]),
   (-1588480, [0, 1, 2, 2]),
   (-373760, [0, 5]),
   ((-27658240 : Rat)/3, [1, 1, 1, 2]),
   (-3176960, [1, 4]),
   ((-5793280 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_23_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_23)) skA_E1_Q2_23 := by decide +kernel

def skA_E1_Q2_24 : SectorVector := [(-1,
  [(-481280, [0, 1, 1, 1, 1, 1]),
   (-1158080, [0, 1, 1, 3]),
   (-902400, [0, 1, 2, 2]),
   (-112800, [0, 5]),
   (4812800, [1, 1, 1, 2]),
   (1534080, [1, 4]),
   (1158080, [2, 3])]),
 (1,
  [(481280, [0, 1, 1, 1, 1, 1]),
   (1158080, [0, 1, 1, 3]),
   (902400, [0, 1, 2, 2]),
   (112800, [0, 5]),
   (4812800, [1, 1, 1, 2]),
   (1534080, [1, 4]),
   (1158080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_24_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_24)) skA_E1_Q2_24 := by decide +kernel

def skA_E1_Q2_25 : SectorVector := [(-1,
  [(-1059840, [0, 1, 1, 1, 1, 1]),
   (-2649600, [0, 1, 1, 3]),
   (-1987200, [0, 1, 2, 2]),
   (-397440, [0, 5]),
   (10598400, [1, 1, 1, 2]),
   (3974400, [1, 4]),
   (2649600, [2, 3])]),
 (1,
  [(1059840, [0, 1, 1, 1, 1, 1]),
   (2649600, [0, 1, 1, 3]),
   (1987200, [0, 1, 2, 2]),
   (397440, [0, 5]),
   (10598400, [1, 1, 1, 2]),
   (3974400, [1, 4]),
   (2649600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_25_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_25)) skA_E1_Q2_25 := by decide +kernel

def skA_E1_Q2_26 : SectorVector := [(-1,
  [(-1275904, [0, 1, 1, 1, 1, 1]),
   (-3189760, [0, 1, 1, 3]),
   (-2392320, [0, 1, 2, 2]),
   (-478464, [0, 5]),
   (12759040, [1, 1, 1, 2]),
   (4784640, [1, 4]),
   (3189760, [2, 3])]),
 (1,
  [(1275904, [0, 1, 1, 1, 1, 1]),
   (3189760, [0, 1, 1, 3]),
   (2392320, [0, 1, 2, 2]),
   (478464, [0, 5]),
   (12759040, [1, 1, 1, 2]),
   (4784640, [1, 4]),
   (3189760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q2_26_cert : VectorCertificate (Tpow 2 (aLeft false (7 : ℤ) skM_E1_26)) skA_E1_Q2_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_2_join : VectorCertificate ([skA_E1_Q2_0, skA_E1_Q2_1, skA_E1_Q2_2, skA_E1_Q2_3, skA_E1_Q2_4, skA_E1_Q2_5, skA_E1_Q2_6, skA_E1_Q2_7, skA_E1_Q2_8, skA_E1_Q2_9, skA_E1_Q2_10, skA_E1_Q2_11, skA_E1_Q2_12, skA_E1_Q2_13, skA_E1_Q2_14, skA_E1_Q2_15, skA_E1_Q2_16, skA_E1_Q2_17, skA_E1_Q2_18, skA_E1_Q2_19, skA_E1_Q2_20, skA_E1_Q2_21, skA_E1_Q2_22, skA_E1_Q2_23, skA_E1_Q2_24, skA_E1_Q2_25, skA_E1_Q2_26] : List SectorVector).flatten skQ_E1_2 := by decide +kernel

theorem skQ_E1_2_val : evaluate skQ_E1_2 = evaluate (OrbSgl.vTerm false skY_E1 1 2) :=
  vTerm_of_chunks false skY_E1 1 2 (7 : ℤ) (by norm_num) skM_E1 [skA_E1_Q2_0, skA_E1_Q2_1, skA_E1_Q2_2, skA_E1_Q2_3, skA_E1_Q2_4, skA_E1_Q2_5, skA_E1_Q2_6, skA_E1_Q2_7, skA_E1_Q2_8, skA_E1_Q2_9, skA_E1_Q2_10, skA_E1_Q2_11, skA_E1_Q2_12, skA_E1_Q2_13, skA_E1_Q2_14, skA_E1_Q2_15, skA_E1_Q2_16, skA_E1_Q2_17, skA_E1_Q2_18, skA_E1_Q2_19, skA_E1_Q2_20, skA_E1_Q2_21, skA_E1_Q2_22, skA_E1_Q2_23, skA_E1_Q2_24, skA_E1_Q2_25, skA_E1_Q2_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q2_0_cert (List.Forall₂.cons skA_E1_Q2_1_cert (List.Forall₂.cons skA_E1_Q2_2_cert (List.Forall₂.cons skA_E1_Q2_3_cert (List.Forall₂.cons skA_E1_Q2_4_cert (List.Forall₂.cons skA_E1_Q2_5_cert (List.Forall₂.cons skA_E1_Q2_6_cert (List.Forall₂.cons skA_E1_Q2_7_cert (List.Forall₂.cons skA_E1_Q2_8_cert (List.Forall₂.cons skA_E1_Q2_9_cert (List.Forall₂.cons skA_E1_Q2_10_cert (List.Forall₂.cons skA_E1_Q2_11_cert (List.Forall₂.cons skA_E1_Q2_12_cert (List.Forall₂.cons skA_E1_Q2_13_cert (List.Forall₂.cons skA_E1_Q2_14_cert (List.Forall₂.cons skA_E1_Q2_15_cert (List.Forall₂.cons skA_E1_Q2_16_cert (List.Forall₂.cons skA_E1_Q2_17_cert (List.Forall₂.cons skA_E1_Q2_18_cert (List.Forall₂.cons skA_E1_Q2_19_cert (List.Forall₂.cons skA_E1_Q2_20_cert (List.Forall₂.cons skA_E1_Q2_21_cert (List.Forall₂.cons skA_E1_Q2_22_cert (List.Forall₂.cons skA_E1_Q2_23_cert (List.Forall₂.cons skA_E1_Q2_24_cert (List.Forall₂.cons skA_E1_Q2_25_cert (List.Forall₂.cons skA_E1_Q2_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_2 skQ_E1_2_join

def skA_E1_Q3_0 : SectorVector := [(1,
  [((360710144 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((-991952896 : Rat)/63, [0, 1, 1, 3]),
   ((-90177536 : Rat)/21, [0, 1, 2, 2]),
   ((-90177536 : Rat)/7, [0, 5]),
   ((360710144 : Rat)/21, [1, 1, 1, 2]),
   ((-1442840576 : Rat)/21, [1, 4]),
   ((-180355072 : Rat)/7, [2, 3])]),
 (-1,
  [((-360710144 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((991952896 : Rat)/63, [0, 1, 1, 3]),
   ((90177536 : Rat)/21, [0, 1, 2, 2]),
   ((90177536 : Rat)/7, [0, 5]),
   ((360710144 : Rat)/21, [1, 1, 1, 2]),
   ((-1442840576 : Rat)/21, [1, 4]),
   ((-180355072 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_0_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_0)) skA_E1_Q3_0 := by decide +kernel

def skA_E1_Q3_1 : SectorVector := [(1,
  [(196608, [0, 1, 1, 1, 1, 1]),
   (-1228800, [0, 1, 1, 3]),
   (-491520, [0, 1, 2, 2]),
   (-786432, [0, 5]),
   (-327680, [1, 1, 1, 2]),
   (-4423680, [1, 4]),
   (-1802240, [2, 3])]),
 (-1,
  [(-196608, [0, 1, 1, 1, 1, 1]),
   (1228800, [0, 1, 1, 3]),
   (491520, [0, 1, 2, 2]),
   (786432, [0, 5]),
   (-327680, [1, 1, 1, 2]),
   (-4423680, [1, 4]),
   (-1802240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_1_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_1)) skA_E1_Q3_1 := by decide +kernel

def skA_E1_Q3_2 : SectorVector := [(1,
  [((10092544 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-164003840 : Rat)/3, [0, 1, 1, 3]),
   (-25231360, [0, 1, 2, 2]),
   (-30277632, [0, 5]),
   (-50462720, [1, 1, 1, 2]),
   (-176619520, [1, 4]),
   (-75694080, [2, 3])]),
 (-1,
  [((-10092544 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((164003840 : Rat)/3, [0, 1, 1, 3]),
   (25231360, [0, 1, 2, 2]),
   (30277632, [0, 5]),
   (-50462720, [1, 1, 1, 2]),
   (-176619520, [1, 4]),
   (-75694080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_2_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_2)) skA_E1_Q3_2 := by decide +kernel

def skA_E1_Q3_3 : SectorVector := [(1,
  [(-7667712, [0, 1, 1, 1, 1, 1]),
   (-36421632, [0, 1, 1, 3]),
   (-23003136, [0, 1, 2, 2]),
   (-11501568, [0, 5]),
   (-99680256, [1, 1, 1, 2]),
   (-80510976, [1, 4]),
   (-42172416, [2, 3])]),
 (-1,
  [(7667712, [0, 1, 1, 1, 1, 1]),
   (36421632, [0, 1, 1, 3]),
   (23003136, [0, 1, 2, 2]),
   (11501568, [0, 5]),
   (-99680256, [1, 1, 1, 2]),
   (-80510976, [1, 4]),
   (-42172416, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_3_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_3)) skA_E1_Q3_3 := by decide +kernel

def skA_E1_Q3_4 : SectorVector := [(1,
  [(1302528, [0, 1, 1, 1, 1, 1]),
   (17909760, [0, 1, 1, 3]),
   (9768960, [0, 1, 2, 2]),
   (7815168, [0, 5]),
   (32563200, [1, 1, 1, 2]),
   (48844800, [1, 4]),
   (22794240, [2, 3])]),
 (-1,
  [(-1302528, [0, 1, 1, 1, 1, 1]),
   (-17909760, [0, 1, 1, 3]),
   (-9768960, [0, 1, 2, 2]),
   (-7815168, [0, 5]),
   (32563200, [1, 1, 1, 2]),
   (48844800, [1, 4]),
   (22794240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_4_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_4)) skA_E1_Q3_4 := by decide +kernel

def skA_E1_Q3_5 : SectorVector := [(1,
  [(17620992, [0, 1, 1, 1, 1, 1]),
   (83699712, [0, 1, 1, 3]),
   (52862976, [0, 1, 2, 2]),
   (26431488, [0, 5]),
   (229072896, [1, 1, 1, 2]),
   (185020416, [1, 4]),
   (96915456, [2, 3])]),
 (-1,
  [(-17620992, [0, 1, 1, 1, 1, 1]),
   (-83699712, [0, 1, 1, 3]),
   (-52862976, [0, 1, 2, 2]),
   (-26431488, [0, 5]),
   (229072896, [1, 1, 1, 2]),
   (185020416, [1, 4]),
   (96915456, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_5_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_5)) skA_E1_Q3_5 := by decide +kernel

def skA_E1_Q3_6 : SectorVector := [(1,
  [(15421440, [0, 1, 1, 1, 1, 1]),
   (88673280, [0, 1, 1, 3]),
   (53975040, [0, 1, 2, 2]),
   (30842880, [0, 5]),
   (221040640, [1, 1, 1, 2]),
   (208189440, [1, 4]),
   (105379840, [2, 3])]),
 (-1,
  [(-15421440, [0, 1, 1, 1, 1, 1]),
   (-88673280, [0, 1, 1, 3]),
   (-53975040, [0, 1, 2, 2]),
   (-30842880, [0, 5]),
   (221040640, [1, 1, 1, 2]),
   (208189440, [1, 4]),
   (105379840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_6_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_6)) skA_E1_Q3_6 := by decide +kernel

def skA_E1_Q3_7 : SectorVector := [(1,
  [(14868480, [0, 1, 1, 1, 1, 1]),
   (42240000, [0, 1, 1, 3]),
   (30412800, [0, 1, 2, 2]),
   (8110080, [0, 5]),
   (155443200, [1, 1, 1, 2]),
   (70963200, [1, 4]),
   (43929600, [2, 3])]),
 (-1,
  [(-14868480, [0, 1, 1, 1, 1, 1]),
   (-42240000, [0, 1, 1, 3]),
   (-30412800, [0, 1, 2, 2]),
   (-8110080, [0, 5]),
   (155443200, [1, 1, 1, 2]),
   (70963200, [1, 4]),
   (43929600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_7_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_7)) skA_E1_Q3_7 := by decide +kernel

def skA_E1_Q3_8 : SectorVector := [(1,
  [((13967360 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((47298560 : Rat)/3, [0, 1, 1, 3]),
   (10792960, [0, 1, 2, 2]),
   (3809280, [0, 5]),
   (52060160, [1, 1, 1, 2]),
   (29839360, [1, 4]),
   (17141760, [2, 3])]),
 (-1,
  [((-13967360 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-47298560 : Rat)/3, [0, 1, 1, 3]),
   (-10792960, [0, 1, 2, 2]),
   (-3809280, [0, 5]),
   (52060160, [1, 1, 1, 2]),
   (29839360, [1, 4]),
   (17141760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_8_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_8)) skA_E1_Q3_8 := by decide +kernel

def skA_E1_Q3_9 : SectorVector := [(1,
  [(-11489280, [0, 1, 1, 1, 1, 1]),
   (-45173760, [0, 1, 1, 3]),
   (-29767680, [0, 1, 2, 2]),
   (-12533760, [0, 5]),
   (-136826880, [1, 1, 1, 2]),
   (-92436480, [1, 4]),
   (-50657280, [2, 3])]),
 (-1,
  [(11489280, [0, 1, 1, 1, 1, 1]),
   (45173760, [0, 1, 1, 3]),
   (29767680, [0, 1, 2, 2]),
   (12533760, [0, 5]),
   (-136826880, [1, 1, 1, 2]),
   (-92436480, [1, 4]),
   (-50657280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_9_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_9)) skA_E1_Q3_9 := by decide +kernel

def skA_E1_Q3_10 : SectorVector := [(1,
  [(-11489280, [0, 1, 1, 1, 1, 1]),
   (-24161280, [0, 1, 1, 3]),
   (-19261440, [0, 1, 2, 2]),
   (-2027520, [0, 5]),
   (-108810240, [1, 1, 1, 2]),
   (-29399040, [1, 4]),
   (-22640640, [2, 3])]),
 (-1,
  [(11489280, [0, 1, 1, 1, 1, 1]),
   (24161280, [0, 1, 1, 3]),
   (19261440, [0, 1, 2, 2]),
   (2027520, [0, 5]),
   (-108810240, [1, 1, 1, 2]),
   (-29399040, [1, 4]),
   (-22640640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_10_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_10)) skA_E1_Q3_10 := by decide +kernel

def skA_E1_Q3_11 : SectorVector := [(1,
  [((70894080 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((199128960 : Rat)/7, [0, 1, 1, 3]),
   ((143873280 : Rat)/7, [0, 1, 2, 2]),
   ((37532160 : Rat)/7, [0, 5]),
   ((738132480 : Rat)/7, [1, 1, 1, 2]),
   ((331534080 : Rat)/7, [1, 4]),
   ((206426880 : Rat)/7, [2, 3])]),
 (-1,
  [((-70894080 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-199128960 : Rat)/7, [0, 1, 1, 3]),
   ((-143873280 : Rat)/7, [0, 1, 2, 2]),
   ((-37532160 : Rat)/7, [0, 5]),
   ((738132480 : Rat)/7, [1, 1, 1, 2]),
   ((331534080 : Rat)/7, [1, 4]),
   ((206426880 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_11_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_11)) skA_E1_Q3_11 := by decide +kernel

def skA_E1_Q3_12 : SectorVector := [(1,
  [(25720320, [0, 1, 1, 1, 1, 1]),
   (81321600, [0, 1, 1, 3]),
   (56736000, [0, 1, 2, 2]),
   (18155520, [0, 5]),
   (279897600, [1, 1, 1, 2]),
   (147513600, [1, 4]),
   (86995200, [2, 3])]),
 (-1,
  [(-25720320, [0, 1, 1, 1, 1, 1]),
   (-81321600, [0, 1, 1, 3]),
   (-56736000, [0, 1, 2, 2]),
   (-18155520, [0, 5]),
   (279897600, [1, 1, 1, 2]),
   (147513600, [1, 4]),
   (86995200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_12_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_12)) skA_E1_Q3_12 := by decide +kernel

def skA_E1_Q3_13 : SectorVector := [(1,
  [(30316032, [0, 1, 1, 1, 1, 1]),
   (95852160, [0, 1, 1, 3]),
   (66873600, [0, 1, 2, 2]),
   (21399552, [0, 5]),
   (329909760, [1, 1, 1, 2]),
   (173871360, [1, 4]),
   (102539520, [2, 3])]),
 (-1,
  [(-30316032, [0, 1, 1, 1, 1, 1]),
   (-95852160, [0, 1, 1, 3]),
   (-66873600, [0, 1, 2, 2]),
   (-21399552, [0, 5]),
   (329909760, [1, 1, 1, 2]),
   (173871360, [1, 4]),
   (102539520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_13_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_13)) skA_E1_Q3_13 := by decide +kernel

def skA_E1_Q3_14 : SectorVector := [(1,
  [(-2506752, [0, 1, 1, 1, 1, 1]),
   (-3760128, [0, 1, 1, 3]),
   (-3446784, [0, 1, 2, 2]),
   (313344, [0, 5]),
   (-21725184, [1, 1, 1, 2]),
   (-1880064, [1, 4]),
   (-2924544, [2, 3])]),
 (-1,
  [(2506752, [0, 1, 1, 1, 1, 1]),
   (3760128, [0, 1, 1, 3]),
   (3446784, [0, 1, 2, 2]),
   (-313344, [0, 5]),
   (-21725184, [1, 1, 1, 2]),
   (-1880064, [1, 4]),
   (-2924544, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_14_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_14)) skA_E1_Q3_14 := by decide +kernel

def skA_E1_Q3_15 : SectorVector := [(1,
  [(15943680, [0, 1, 1, 1, 1, 1]),
   (35873280, [0, 1, 1, 3]),
   (27901440, [0, 1, 2, 2]),
   (3985920, [0, 5]),
   (154122240, [1, 1, 1, 2]),
   (47831040, [1, 4]),
   (34544640, [2, 3])]),
 (-1,
  [(-15943680, [0, 1, 1, 1, 1, 1]),
   (-35873280, [0, 1, 1, 3]),
   (-27901440, [0, 1, 2, 2]),
   (-3985920, [0, 5]),
   (154122240, [1, 1, 1, 2]),
   (47831040, [1, 4]),
   (34544640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_15_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_15)) skA_E1_Q3_15 := by decide +kernel

def skA_E1_Q3_16 : SectorVector := [(1,
  [(30154752, [0, 1, 1, 1, 1, 1]),
   (75386880, [0, 1, 1, 3]),
   (56540160, [0, 1, 2, 2]),
   (11308032, [0, 5]),
   (301547520, [1, 1, 1, 2]),
   (113080320, [1, 4]),
   (75386880, [2, 3])]),
 (-1,
  [(-30154752, [0, 1, 1, 1, 1, 1]),
   (-75386880, [0, 1, 1, 3]),
   (-56540160, [0, 1, 2, 2]),
   (-11308032, [0, 5]),
   (301547520, [1, 1, 1, 2]),
   (113080320, [1, 4]),
   (75386880, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_16_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_16)) skA_E1_Q3_16 := by decide +kernel

def skA_E1_Q3_17 : SectorVector := [(1,
  [(14653440, [0, 1, 1, 1, 1, 1]),
   (36633600, [0, 1, 1, 3]),
   (27475200, [0, 1, 2, 2]),
   (5495040, [0, 5]),
   (146534400, [1, 1, 1, 2]),
   (54950400, [1, 4]),
   (36633600, [2, 3])]),
 (-1,
  [(-14653440, [0, 1, 1, 1, 1, 1]),
   (-36633600, [0, 1, 1, 3]),
   (-27475200, [0, 1, 2, 2]),
   (-5495040, [0, 5]),
   (146534400, [1, 1, 1, 2]),
   (54950400, [1, 4]),
   (36633600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_17_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_17)) skA_E1_Q3_17 := by decide +kernel

def skA_E1_Q3_18 : SectorVector := [(1,
  [(9338880, [0, 1, 1, 1, 1, 1]),
   (25681920, [0, 1, 1, 3]),
   (18677760, [0, 1, 2, 2]),
   (4669440, [0, 5]),
   (96501760, [1, 1, 1, 2]),
   (42024960, [1, 4]),
   (26460160, [2, 3])]),
 (-1,
  [(-9338880, [0, 1, 1, 1, 1, 1]),
   (-25681920, [0, 1, 1, 3]),
   (-18677760, [0, 1, 2, 2]),
   (-4669440, [0, 5]),
   (96501760, [1, 1, 1, 2]),
   (42024960, [1, 4]),
   (26460160, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_18_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_18)) skA_E1_Q3_18 := by decide +kernel

def skA_E1_Q3_19 : SectorVector := [(1,
  [(-13851648, [0, 1, 1, 1, 1, 1]),
   (-38092032, [0, 1, 1, 3]),
   (-27703296, [0, 1, 2, 2]),
   (-6925824, [0, 5]),
   (-143133696, [1, 1, 1, 2]),
   (-62332416, [1, 4]),
   (-39246336, [2, 3])]),
 (-1,
  [(13851648, [0, 1, 1, 1, 1, 1]),
   (38092032, [0, 1, 1, 3]),
   (27703296, [0, 1, 2, 2]),
   (6925824, [0, 5]),
   (-143133696, [1, 1, 1, 2]),
   (-62332416, [1, 4]),
   (-39246336, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_19_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_19)) skA_E1_Q3_19 := by decide +kernel

def skA_E1_Q3_20 : SectorVector := [(1,
  [(3121152, [0, 1, 1, 1, 1, 1]),
   (6047232, [0, 1, 1, 3]),
   (4974336, [0, 1, 2, 2]),
   (292608, [0, 5]),
   (28870656, [1, 1, 1, 2]),
   (6437376, [1, 4]),
   (5462016, [2, 3])]),
 (-1,
  [(-3121152, [0, 1, 1, 1, 1, 1]),
   (-6047232, [0, 1, 1, 3]),
   (-4974336, [0, 1, 2, 2]),
   (-292608, [0, 5]),
   (28870656, [1, 1, 1, 2]),
   (6437376, [1, 4]),
   (5462016, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_20_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_20)) skA_E1_Q3_20 := by decide +kernel

def skA_E1_Q3_21 : SectorVector := [(1,
  [(5959680, [0, 1, 1, 1, 1, 1]),
   (12664320, [0, 1, 1, 3]),
   (10056960, [0, 1, 2, 2]),
   (1117440, [0, 5]),
   (56616960, [1, 1, 1, 2]),
   (15644160, [1, 4]),
   (11919360, [2, 3])]),
 (-1,
  [(-5959680, [0, 1, 1, 1, 1, 1]),
   (-12664320, [0, 1, 1, 3]),
   (-10056960, [0, 1, 2, 2]),
   (-1117440, [0, 5]),
   (56616960, [1, 1, 1, 2]),
   (15644160, [1, 4]),
   (11919360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_21_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_21)) skA_E1_Q3_21 := by decide +kernel

def skA_E1_Q3_22 : SectorVector := [(1,
  [((9748480 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((22543360 : Rat)/9, [0, 1, 1, 3]),
   ((5788160 : Rat)/3, [0, 1, 2, 2]),
   (304640, [0, 5]),
   ((31682560 : Rat)/3, [1, 1, 1, 2]),
   ((10357760 : Rat)/3, [1, 4]),
   (2437120, [2, 3])]),
 (-1,
  [((-9748480 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-22543360 : Rat)/9, [0, 1, 1, 3]),
   ((-5788160 : Rat)/3, [0, 1, 2, 2]),
   (-304640, [0, 5]),
   ((31682560 : Rat)/3, [1, 1, 1, 2]),
   ((10357760 : Rat)/3, [1, 4]),
   (2437120, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_22_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_22)) skA_E1_Q3_22 := by decide +kernel

def skA_E1_Q3_23 : SectorVector := [(1,
  [(-2990080, [0, 1, 1, 1, 1, 1]),
   (-6914560, [0, 1, 1, 3]),
   (-5326080, [0, 1, 2, 2]),
   (-840960, [0, 5]),
   (-29153280, [1, 1, 1, 2]),
   (-9530880, [1, 4]),
   (-6727680, [2, 3])]),
 (-1,
  [(2990080, [0, 1, 1, 1, 1, 1]),
   (6914560, [0, 1, 1, 3]),
   (5326080, [0, 1, 2, 2]),
   (840960, [0, 5]),
   (-29153280, [1, 1, 1, 2]),
   (-9530880, [1, 4]),
   (-6727680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_23_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_23)) skA_E1_Q3_23 := by decide +kernel

def skA_E1_Q3_24 : SectorVector := [(1,
  [(1443840, [0, 1, 1, 1, 1, 1]),
   (3609600, [0, 1, 1, 3]),
   (2707200, [0, 1, 2, 2]),
   (541440, [0, 5]),
   (14438400, [1, 1, 1, 2]),
   (5414400, [1, 4]),
   (3609600, [2, 3])]),
 (-1,
  [(-1443840, [0, 1, 1, 1, 1, 1]),
   (-3609600, [0, 1, 1, 3]),
   (-2707200, [0, 1, 2, 2]),
   (-541440, [0, 5]),
   (14438400, [1, 1, 1, 2]),
   (5414400, [1, 4]),
   (3609600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_24_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_24)) skA_E1_Q3_24 := by decide +kernel

def skA_E1_Q3_25 : SectorVector := [(1,
  [(3179520, [0, 1, 1, 1, 1, 1]),
   (7948800, [0, 1, 1, 3]),
   (5961600, [0, 1, 2, 2]),
   (1192320, [0, 5]),
   (31795200, [1, 1, 1, 2]),
   (11923200, [1, 4]),
   (7948800, [2, 3])]),
 (-1,
  [(-3179520, [0, 1, 1, 1, 1, 1]),
   (-7948800, [0, 1, 1, 3]),
   (-5961600, [0, 1, 2, 2]),
   (-1192320, [0, 5]),
   (31795200, [1, 1, 1, 2]),
   (11923200, [1, 4]),
   (7948800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_25_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_25)) skA_E1_Q3_25 := by decide +kernel

def skA_E1_Q3_26 : SectorVector := [(1,
  [(3827712, [0, 1, 1, 1, 1, 1]),
   (9569280, [0, 1, 1, 3]),
   (7176960, [0, 1, 2, 2]),
   (1435392, [0, 5]),
   (38277120, [1, 1, 1, 2]),
   (14353920, [1, 4]),
   (9569280, [2, 3])]),
 (-1,
  [(-3827712, [0, 1, 1, 1, 1, 1]),
   (-9569280, [0, 1, 1, 3]),
   (-7176960, [0, 1, 2, 2]),
   (-1435392, [0, 5]),
   (38277120, [1, 1, 1, 2]),
   (14353920, [1, 4]),
   (9569280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q3_26_cert : VectorCertificate (Tpow 3 (aLeft false (8 : ℤ) skM_E1_26)) skA_E1_Q3_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_3_join : VectorCertificate ([skA_E1_Q3_0, skA_E1_Q3_1, skA_E1_Q3_2, skA_E1_Q3_3, skA_E1_Q3_4, skA_E1_Q3_5, skA_E1_Q3_6, skA_E1_Q3_7, skA_E1_Q3_8, skA_E1_Q3_9, skA_E1_Q3_10, skA_E1_Q3_11, skA_E1_Q3_12, skA_E1_Q3_13, skA_E1_Q3_14, skA_E1_Q3_15, skA_E1_Q3_16, skA_E1_Q3_17, skA_E1_Q3_18, skA_E1_Q3_19, skA_E1_Q3_20, skA_E1_Q3_21, skA_E1_Q3_22, skA_E1_Q3_23, skA_E1_Q3_24, skA_E1_Q3_25, skA_E1_Q3_26] : List SectorVector).flatten skQ_E1_3 := by decide +kernel

theorem skQ_E1_3_val : evaluate skQ_E1_3 = evaluate (OrbSgl.vTerm false skY_E1 1 3) :=
  vTerm_of_chunks false skY_E1 1 3 (8 : ℤ) (by norm_num) skM_E1 [skA_E1_Q3_0, skA_E1_Q3_1, skA_E1_Q3_2, skA_E1_Q3_3, skA_E1_Q3_4, skA_E1_Q3_5, skA_E1_Q3_6, skA_E1_Q3_7, skA_E1_Q3_8, skA_E1_Q3_9, skA_E1_Q3_10, skA_E1_Q3_11, skA_E1_Q3_12, skA_E1_Q3_13, skA_E1_Q3_14, skA_E1_Q3_15, skA_E1_Q3_16, skA_E1_Q3_17, skA_E1_Q3_18, skA_E1_Q3_19, skA_E1_Q3_20, skA_E1_Q3_21, skA_E1_Q3_22, skA_E1_Q3_23, skA_E1_Q3_24, skA_E1_Q3_25, skA_E1_Q3_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q3_0_cert (List.Forall₂.cons skA_E1_Q3_1_cert (List.Forall₂.cons skA_E1_Q3_2_cert (List.Forall₂.cons skA_E1_Q3_3_cert (List.Forall₂.cons skA_E1_Q3_4_cert (List.Forall₂.cons skA_E1_Q3_5_cert (List.Forall₂.cons skA_E1_Q3_6_cert (List.Forall₂.cons skA_E1_Q3_7_cert (List.Forall₂.cons skA_E1_Q3_8_cert (List.Forall₂.cons skA_E1_Q3_9_cert (List.Forall₂.cons skA_E1_Q3_10_cert (List.Forall₂.cons skA_E1_Q3_11_cert (List.Forall₂.cons skA_E1_Q3_12_cert (List.Forall₂.cons skA_E1_Q3_13_cert (List.Forall₂.cons skA_E1_Q3_14_cert (List.Forall₂.cons skA_E1_Q3_15_cert (List.Forall₂.cons skA_E1_Q3_16_cert (List.Forall₂.cons skA_E1_Q3_17_cert (List.Forall₂.cons skA_E1_Q3_18_cert (List.Forall₂.cons skA_E1_Q3_19_cert (List.Forall₂.cons skA_E1_Q3_20_cert (List.Forall₂.cons skA_E1_Q3_21_cert (List.Forall₂.cons skA_E1_Q3_22_cert (List.Forall₂.cons skA_E1_Q3_23_cert (List.Forall₂.cons skA_E1_Q3_24_cert (List.Forall₂.cons skA_E1_Q3_25_cert (List.Forall₂.cons skA_E1_Q3_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_3 skQ_E1_3_join

def skA_E1_Q4_0 : SectorVector := [(-1,
  [((-721420288 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((-1803550720 : Rat)/63, [0, 1, 1, 3]),
   ((-450887680 : Rat)/21, [0, 1, 2, 2]),
   ((-90177536 : Rat)/21, [0, 5]),
   ((7214202880 : Rat)/63, [1, 1, 1, 2]),
   ((901775360 : Rat)/21, [1, 4]),
   ((1803550720 : Rat)/63, [2, 3])]),
 (1,
  [((721420288 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((1803550720 : Rat)/63, [0, 1, 1, 3]),
   ((450887680 : Rat)/21, [0, 1, 2, 2]),
   ((90177536 : Rat)/21, [0, 5]),
   ((7214202880 : Rat)/63, [1, 1, 1, 2]),
   ((901775360 : Rat)/21, [1, 4]),
   ((1803550720 : Rat)/63, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_0_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_0)) skA_E1_Q4_0 := by decide +kernel

def skA_E1_Q4_1 : SectorVector := [(-1,
  [(524288, [0, 1, 1, 1, 1, 1]),
   (1310720, [0, 1, 1, 3]),
   (983040, [0, 1, 2, 2]),
   (196608, [0, 5]),
   (-5242880, [1, 1, 1, 2]),
   (-1966080, [1, 4]),
   (-1310720, [2, 3])]),
 (1,
  [(-524288, [0, 1, 1, 1, 1, 1]),
   (-1310720, [0, 1, 1, 3]),
   (-983040, [0, 1, 2, 2]),
   (-196608, [0, 5]),
   (-5242880, [1, 1, 1, 2]),
   (-1966080, [1, 4]),
   (-1310720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_1_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_1)) skA_E1_Q4_1 := by decide +kernel

def skA_E1_Q4_2 : SectorVector := [(-1,
  [((161480704 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((403701760 : Rat)/3, [0, 1, 1, 3]),
   (100925440, [0, 1, 2, 2]),
   (20185088, [0, 5]),
   ((-1614807040 : Rat)/3, [1, 1, 1, 2]),
   (-201850880, [1, 4]),
   ((-403701760 : Rat)/3, [2, 3])]),
 (1,
  [((-161480704 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-403701760 : Rat)/3, [0, 1, 1, 3]),
   (-100925440, [0, 1, 2, 2]),
   (-20185088, [0, 5]),
   ((-1614807040 : Rat)/3, [1, 1, 1, 2]),
   (-201850880, [1, 4]),
   ((-403701760 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_2_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_2)) skA_E1_Q4_2 := by decide +kernel

def skA_E1_Q4_3 : SectorVector := [(-1,
  [(92012544, [0, 1, 1, 1, 1, 1]),
   (230031360, [0, 1, 1, 3]),
   (172523520, [0, 1, 2, 2]),
   (34504704, [0, 5]),
   (-920125440, [1, 1, 1, 2]),
   (-345047040, [1, 4]),
   (-230031360, [2, 3])]),
 (1,
  [(-92012544, [0, 1, 1, 1, 1, 1]),
   (-230031360, [0, 1, 1, 3]),
   (-172523520, [0, 1, 2, 2]),
   (-34504704, [0, 5]),
   (-920125440, [1, 1, 1, 2]),
   (-345047040, [1, 4]),
   (-230031360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_3_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_3)) skA_E1_Q4_3 := by decide +kernel

def skA_E1_Q4_4 : SectorVector := [(-1,
  [(-15630336, [0, 1, 1, 1, 1, 1]),
   (-39075840, [0, 1, 1, 3]),
   (-29306880, [0, 1, 2, 2]),
   (-5861376, [0, 5]),
   (156303360, [1, 1, 1, 2]),
   (58613760, [1, 4]),
   (39075840, [2, 3])]),
 (1,
  [(15630336, [0, 1, 1, 1, 1, 1]),
   (39075840, [0, 1, 1, 3]),
   (29306880, [0, 1, 2, 2]),
   (5861376, [0, 5]),
   (156303360, [1, 1, 1, 2]),
   (58613760, [1, 4]),
   (39075840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_4_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_4)) skA_E1_Q4_4 := by decide +kernel

def skA_E1_Q4_5 : SectorVector := [(-1,
  [(-93978624, [0, 1, 1, 1, 1, 1]),
   (-234946560, [0, 1, 1, 3]),
   (-176209920, [0, 1, 2, 2]),
   (-35241984, [0, 5]),
   (939786240, [1, 1, 1, 2]),
   (352419840, [1, 4]),
   (234946560, [2, 3])]),
 (1,
  [(93978624, [0, 1, 1, 1, 1, 1]),
   (234946560, [0, 1, 1, 3]),
   (176209920, [0, 1, 2, 2]),
   (35241984, [0, 5]),
   (939786240, [1, 1, 1, 2]),
   (352419840, [1, 4]),
   (234946560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_5_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_5)) skA_E1_Q4_5 := by decide +kernel

def skA_E1_Q4_6 : SectorVector := [(-1,
  [(-82247680, [0, 1, 1, 1, 1, 1]),
   (-205619200, [0, 1, 1, 3]),
   (-154214400, [0, 1, 2, 2]),
   (-30842880, [0, 5]),
   (822476800, [1, 1, 1, 2]),
   (308428800, [1, 4]),
   (205619200, [2, 3])]),
 (1,
  [(82247680, [0, 1, 1, 1, 1, 1]),
   (205619200, [0, 1, 1, 3]),
   (154214400, [0, 1, 2, 2]),
   (30842880, [0, 5]),
   (822476800, [1, 1, 1, 2]),
   (308428800, [1, 4]),
   (205619200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_6_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_6)) skA_E1_Q4_6 := by decide +kernel

def skA_E1_Q4_7 : SectorVector := [(-1,
  [(-54067200, [0, 1, 1, 1, 1, 1]),
   (-135168000, [0, 1, 1, 3]),
   (-101376000, [0, 1, 2, 2]),
   (-20275200, [0, 5]),
   (540672000, [1, 1, 1, 2]),
   (202752000, [1, 4]),
   (135168000, [2, 3])]),
 (1,
  [(54067200, [0, 1, 1, 1, 1, 1]),
   (135168000, [0, 1, 1, 3]),
   (101376000, [0, 1, 2, 2]),
   (20275200, [0, 5]),
   (540672000, [1, 1, 1, 2]),
   (202752000, [1, 4]),
   (135168000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_7_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_7)) skA_E1_Q4_7 := by decide +kernel

def skA_E1_Q4_8 : SectorVector := [(-1,
  [((-50790400 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-126976000 : Rat)/3, [0, 1, 1, 3]),
   (-31744000, [0, 1, 2, 2]),
   (-6348800, [0, 5]),
   ((507904000 : Rat)/3, [1, 1, 1, 2]),
   (63488000, [1, 4]),
   ((126976000 : Rat)/3, [2, 3])]),
 (1,
  [((50790400 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((126976000 : Rat)/3, [0, 1, 1, 3]),
   (31744000, [0, 1, 2, 2]),
   (6348800, [0, 5]),
   ((507904000 : Rat)/3, [1, 1, 1, 2]),
   (63488000, [1, 4]),
   ((126976000 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_8_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_8)) skA_E1_Q4_8 := by decide +kernel

def skA_E1_Q4_9 : SectorVector := [(-1,
  [(41779200, [0, 1, 1, 1, 1, 1]),
   (104448000, [0, 1, 1, 3]),
   (78336000, [0, 1, 2, 2]),
   (15667200, [0, 5]),
   (-417792000, [1, 1, 1, 2]),
   (-156672000, [1, 4]),
   (-104448000, [2, 3])]),
 (1,
  [(-41779200, [0, 1, 1, 1, 1, 1]),
   (-104448000, [0, 1, 1, 3]),
   (-78336000, [0, 1, 2, 2]),
   (-15667200, [0, 5]),
   (-417792000, [1, 1, 1, 2]),
   (-156672000, [1, 4]),
   (-104448000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_9_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_9)) skA_E1_Q4_9 := by decide +kernel

def skA_E1_Q4_10 : SectorVector := [(-1,
  [(32440320, [0, 1, 1, 1, 1, 1]),
   (81100800, [0, 1, 1, 3]),
   (60825600, [0, 1, 2, 2]),
   (12165120, [0, 5]),
   (-324403200, [1, 1, 1, 2]),
   (-121651200, [1, 4]),
   (-81100800, [2, 3])]),
 (1,
  [(-32440320, [0, 1, 1, 1, 1, 1]),
   (-81100800, [0, 1, 1, 3]),
   (-60825600, [0, 1, 2, 2]),
   (-12165120, [0, 5]),
   (-324403200, [1, 1, 1, 2]),
   (-121651200, [1, 4]),
   (-81100800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_10_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_10)) skA_E1_Q4_10 := by decide +kernel

def skA_E1_Q4_11 : SectorVector := [(-1,
  [((-200171520 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-500428800 : Rat)/7, [0, 1, 1, 3]),
   ((-375321600 : Rat)/7, [0, 1, 2, 2]),
   ((-75064320 : Rat)/7, [0, 5]),
   ((2001715200 : Rat)/7, [1, 1, 1, 2]),
   ((750643200 : Rat)/7, [1, 4]),
   ((500428800 : Rat)/7, [2, 3])]),
 (1,
  [((200171520 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((500428800 : Rat)/7, [0, 1, 1, 3]),
   ((375321600 : Rat)/7, [0, 1, 2, 2]),
   ((75064320 : Rat)/7, [0, 5]),
   ((2001715200 : Rat)/7, [1, 1, 1, 2]),
   ((750643200 : Rat)/7, [1, 4]),
   ((500428800 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_11_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_11)) skA_E1_Q4_11 := by decide +kernel

def skA_E1_Q4_12 : SectorVector := [(-1,
  [(-72622080, [0, 1, 1, 1, 1, 1]),
   (-181555200, [0, 1, 1, 3]),
   (-136166400, [0, 1, 2, 2]),
   (-27233280, [0, 5]),
   (726220800, [1, 1, 1, 2]),
   (272332800, [1, 4]),
   (181555200, [2, 3])]),
 (1,
  [(72622080, [0, 1, 1, 1, 1, 1]),
   (181555200, [0, 1, 1, 3]),
   (136166400, [0, 1, 2, 2]),
   (27233280, [0, 5]),
   (726220800, [1, 1, 1, 2]),
   (272332800, [1, 4]),
   (181555200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_12_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_12)) skA_E1_Q4_12 := by decide +kernel

def skA_E1_Q4_13 : SectorVector := [(-1,
  [(-85598208, [0, 1, 1, 1, 1, 1]),
   (-213995520, [0, 1, 1, 3]),
   (-160496640, [0, 1, 2, 2]),
   (-32099328, [0, 5]),
   (855982080, [1, 1, 1, 2]),
   (320993280, [1, 4]),
   (213995520, [2, 3])]),
 (1,
  [(85598208, [0, 1, 1, 1, 1, 1]),
   (213995520, [0, 1, 1, 3]),
   (160496640, [0, 1, 2, 2]),
   (32099328, [0, 5]),
   (855982080, [1, 1, 1, 2]),
   (320993280, [1, 4]),
   (213995520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_13_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_13)) skA_E1_Q4_13 := by decide +kernel

def skA_E1_Q4_14 : SectorVector := [(-1,
  [(5849088, [0, 1, 1, 1, 1, 1]),
   (14622720, [0, 1, 1, 3]),
   (10967040, [0, 1, 2, 2]),
   (2193408, [0, 5]),
   (-58490880, [1, 1, 1, 2]),
   (-21934080, [1, 4]),
   (-14622720, [2, 3])]),
 (1,
  [(-5849088, [0, 1, 1, 1, 1, 1]),
   (-14622720, [0, 1, 1, 3]),
   (-10967040, [0, 1, 2, 2]),
   (-2193408, [0, 5]),
   (-58490880, [1, 1, 1, 2]),
   (-21934080, [1, 4]),
   (-14622720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_14_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_14)) skA_E1_Q4_14 := by decide +kernel

def skA_E1_Q4_15 : SectorVector := [(-1,
  [(-37201920, [0, 1, 1, 1, 1, 1]),
   (-93004800, [0, 1, 1, 3]),
   (-69753600, [0, 1, 2, 2]),
   (-13950720, [0, 5]),
   (372019200, [1, 1, 1, 2]),
   (139507200, [1, 4]),
   (93004800, [2, 3])]),
 (1,
  [(37201920, [0, 1, 1, 1, 1, 1]),
   (93004800, [0, 1, 1, 3]),
   (69753600, [0, 1, 2, 2]),
   (13950720, [0, 5]),
   (372019200, [1, 1, 1, 2]),
   (139507200, [1, 4]),
   (93004800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_15_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_15)) skA_E1_Q4_15 := by decide +kernel

def skA_E1_Q4_16 : SectorVector := [(-1,
  [(-70361088, [0, 1, 1, 1, 1, 1]),
   (-175902720, [0, 1, 1, 3]),
   (-131927040, [0, 1, 2, 2]),
   (-26385408, [0, 5]),
   (703610880, [1, 1, 1, 2]),
   (263854080, [1, 4]),
   (175902720, [2, 3])]),
 (1,
  [(70361088, [0, 1, 1, 1, 1, 1]),
   (175902720, [0, 1, 1, 3]),
   (131927040, [0, 1, 2, 2]),
   (26385408, [0, 5]),
   (703610880, [1, 1, 1, 2]),
   (263854080, [1, 4]),
   (175902720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_16_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_16)) skA_E1_Q4_16 := by decide +kernel

def skA_E1_Q4_17 : SectorVector := [(-1,
  [(-34191360, [0, 1, 1, 1, 1, 1]),
   (-85478400, [0, 1, 1, 3]),
   (-64108800, [0, 1, 2, 2]),
   (-12821760, [0, 5]),
   (341913600, [1, 1, 1, 2]),
   (128217600, [1, 4]),
   (85478400, [2, 3])]),
 (1,
  [(34191360, [0, 1, 1, 1, 1, 1]),
   (85478400, [0, 1, 1, 3]),
   (64108800, [0, 1, 2, 2]),
   (12821760, [0, 5]),
   (341913600, [1, 1, 1, 2]),
   (128217600, [1, 4]),
   (85478400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_17_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_17)) skA_E1_Q4_17 := by decide +kernel

def skA_E1_Q4_18 : SectorVector := [(-1,
  [(-21790720, [0, 1, 1, 1, 1, 1]),
   (-54476800, [0, 1, 1, 3]),
   (-40857600, [0, 1, 2, 2]),
   (-8171520, [0, 5]),
   (217907200, [1, 1, 1, 2]),
   (81715200, [1, 4]),
   (54476800, [2, 3])]),
 (1,
  [(21790720, [0, 1, 1, 1, 1, 1]),
   (54476800, [0, 1, 1, 3]),
   (40857600, [0, 1, 2, 2]),
   (8171520, [0, 5]),
   (217907200, [1, 1, 1, 2]),
   (81715200, [1, 4]),
   (54476800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_18_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_18)) skA_E1_Q4_18 := by decide +kernel

def skA_E1_Q4_19 : SectorVector := [(-1,
  [(32320512, [0, 1, 1, 1, 1, 1]),
   (80801280, [0, 1, 1, 3]),
   (60600960, [0, 1, 2, 2]),
   (12120192, [0, 5]),
   (-323205120, [1, 1, 1, 2]),
   (-121201920, [1, 4]),
   (-80801280, [2, 3])]),
 (1,
  [(-32320512, [0, 1, 1, 1, 1, 1]),
   (-80801280, [0, 1, 1, 3]),
   (-60600960, [0, 1, 2, 2]),
   (-12120192, [0, 5]),
   (-323205120, [1, 1, 1, 2]),
   (-121201920, [1, 4]),
   (-80801280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_19_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_19)) skA_E1_Q4_19 := by decide +kernel

def skA_E1_Q4_20 : SectorVector := [(-1,
  [(-6242304, [0, 1, 1, 1, 1, 1]),
   (-15605760, [0, 1, 1, 3]),
   (-11704320, [0, 1, 2, 2]),
   (-2340864, [0, 5]),
   (62423040, [1, 1, 1, 2]),
   (23408640, [1, 4]),
   (15605760, [2, 3])]),
 (1,
  [(6242304, [0, 1, 1, 1, 1, 1]),
   (15605760, [0, 1, 1, 3]),
   (11704320, [0, 1, 2, 2]),
   (2340864, [0, 5]),
   (62423040, [1, 1, 1, 2]),
   (23408640, [1, 4]),
   (15605760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_20_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_20)) skA_E1_Q4_20 := by decide +kernel

def skA_E1_Q4_21 : SectorVector := [(-1,
  [(-11919360, [0, 1, 1, 1, 1, 1]),
   (-29798400, [0, 1, 1, 3]),
   (-22348800, [0, 1, 2, 2]),
   (-4469760, [0, 5]),
   (119193600, [1, 1, 1, 2]),
   (44697600, [1, 4]),
   (29798400, [2, 3])]),
 (1,
  [(11919360, [0, 1, 1, 1, 1, 1]),
   (29798400, [0, 1, 1, 3]),
   (22348800, [0, 1, 2, 2]),
   (4469760, [0, 5]),
   (119193600, [1, 1, 1, 2]),
   (44697600, [1, 4]),
   (29798400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_21_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_21)) skA_E1_Q4_21 := by decide +kernel

def skA_E1_Q4_22 : SectorVector := [(-1,
  [((-19496960 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-48742400 : Rat)/9, [0, 1, 1, 3]),
   ((-12185600 : Rat)/3, [0, 1, 2, 2]),
   ((-2437120 : Rat)/3, [0, 5]),
   ((194969600 : Rat)/9, [1, 1, 1, 2]),
   ((24371200 : Rat)/3, [1, 4]),
   ((48742400 : Rat)/9, [2, 3])]),
 (1,
  [((19496960 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((48742400 : Rat)/9, [0, 1, 1, 3]),
   ((12185600 : Rat)/3, [0, 1, 2, 2]),
   ((2437120 : Rat)/3, [0, 5]),
   ((194969600 : Rat)/9, [1, 1, 1, 2]),
   ((24371200 : Rat)/3, [1, 4]),
   ((48742400 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_22_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_22)) skA_E1_Q4_22 := by decide +kernel

def skA_E1_Q4_23 : SectorVector := [(-1,
  [(5980160, [0, 1, 1, 1, 1, 1]),
   (14950400, [0, 1, 1, 3]),
   (11212800, [0, 1, 2, 2]),
   (2242560, [0, 5]),
   (-59801600, [1, 1, 1, 2]),
   (-22425600, [1, 4]),
   (-14950400, [2, 3])]),
 (1,
  [(-5980160, [0, 1, 1, 1, 1, 1]),
   (-14950400, [0, 1, 1, 3]),
   (-11212800, [0, 1, 2, 2]),
   (-2242560, [0, 5]),
   (-59801600, [1, 1, 1, 2]),
   (-22425600, [1, 4]),
   (-14950400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_23_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_23)) skA_E1_Q4_23 := by decide +kernel

def skA_E1_Q4_24 : SectorVector := [(-1,
  [(-2887680, [0, 1, 1, 1, 1, 1]),
   (-7219200, [0, 1, 1, 3]),
   (-5414400, [0, 1, 2, 2]),
   (-1082880, [0, 5]),
   (28876800, [1, 1, 1, 2]),
   (10828800, [1, 4]),
   (7219200, [2, 3])]),
 (1,
  [(2887680, [0, 1, 1, 1, 1, 1]),
   (7219200, [0, 1, 1, 3]),
   (5414400, [0, 1, 2, 2]),
   (1082880, [0, 5]),
   (28876800, [1, 1, 1, 2]),
   (10828800, [1, 4]),
   (7219200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_24_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_24)) skA_E1_Q4_24 := by decide +kernel

def skA_E1_Q4_25 : SectorVector := [(-1,
  [(-6359040, [0, 1, 1, 1, 1, 1]),
   (-15897600, [0, 1, 1, 3]),
   (-11923200, [0, 1, 2, 2]),
   (-2384640, [0, 5]),
   (63590400, [1, 1, 1, 2]),
   (23846400, [1, 4]),
   (15897600, [2, 3])]),
 (1,
  [(6359040, [0, 1, 1, 1, 1, 1]),
   (15897600, [0, 1, 1, 3]),
   (11923200, [0, 1, 2, 2]),
   (2384640, [0, 5]),
   (63590400, [1, 1, 1, 2]),
   (23846400, [1, 4]),
   (15897600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_25_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_25)) skA_E1_Q4_25 := by decide +kernel

def skA_E1_Q4_26 : SectorVector := [(-1,
  [(-7655424, [0, 1, 1, 1, 1, 1]),
   (-19138560, [0, 1, 1, 3]),
   (-14353920, [0, 1, 2, 2]),
   (-2870784, [0, 5]),
   (76554240, [1, 1, 1, 2]),
   (28707840, [1, 4]),
   (19138560, [2, 3])]),
 (1,
  [(7655424, [0, 1, 1, 1, 1, 1]),
   (19138560, [0, 1, 1, 3]),
   (14353920, [0, 1, 2, 2]),
   (2870784, [0, 5]),
   (76554240, [1, 1, 1, 2]),
   (28707840, [1, 4]),
   (19138560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q4_26_cert : VectorCertificate (Tpow 4 (aLeft false (9 : ℤ) skM_E1_26)) skA_E1_Q4_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_4_join : VectorCertificate ([skA_E1_Q4_0, skA_E1_Q4_1, skA_E1_Q4_2, skA_E1_Q4_3, skA_E1_Q4_4, skA_E1_Q4_5, skA_E1_Q4_6, skA_E1_Q4_7, skA_E1_Q4_8, skA_E1_Q4_9, skA_E1_Q4_10, skA_E1_Q4_11, skA_E1_Q4_12, skA_E1_Q4_13, skA_E1_Q4_14, skA_E1_Q4_15, skA_E1_Q4_16, skA_E1_Q4_17, skA_E1_Q4_18, skA_E1_Q4_19, skA_E1_Q4_20, skA_E1_Q4_21, skA_E1_Q4_22, skA_E1_Q4_23, skA_E1_Q4_24, skA_E1_Q4_25, skA_E1_Q4_26] : List SectorVector).flatten skQ_E1_4 := by decide +kernel

theorem skQ_E1_4_val : evaluate skQ_E1_4 = evaluate (OrbSgl.vTerm false skY_E1 1 4) :=
  vTerm_of_chunks false skY_E1 1 4 (9 : ℤ) (by norm_num) skM_E1 [skA_E1_Q4_0, skA_E1_Q4_1, skA_E1_Q4_2, skA_E1_Q4_3, skA_E1_Q4_4, skA_E1_Q4_5, skA_E1_Q4_6, skA_E1_Q4_7, skA_E1_Q4_8, skA_E1_Q4_9, skA_E1_Q4_10, skA_E1_Q4_11, skA_E1_Q4_12, skA_E1_Q4_13, skA_E1_Q4_14, skA_E1_Q4_15, skA_E1_Q4_16, skA_E1_Q4_17, skA_E1_Q4_18, skA_E1_Q4_19, skA_E1_Q4_20, skA_E1_Q4_21, skA_E1_Q4_22, skA_E1_Q4_23, skA_E1_Q4_24, skA_E1_Q4_25, skA_E1_Q4_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q4_0_cert (List.Forall₂.cons skA_E1_Q4_1_cert (List.Forall₂.cons skA_E1_Q4_2_cert (List.Forall₂.cons skA_E1_Q4_3_cert (List.Forall₂.cons skA_E1_Q4_4_cert (List.Forall₂.cons skA_E1_Q4_5_cert (List.Forall₂.cons skA_E1_Q4_6_cert (List.Forall₂.cons skA_E1_Q4_7_cert (List.Forall₂.cons skA_E1_Q4_8_cert (List.Forall₂.cons skA_E1_Q4_9_cert (List.Forall₂.cons skA_E1_Q4_10_cert (List.Forall₂.cons skA_E1_Q4_11_cert (List.Forall₂.cons skA_E1_Q4_12_cert (List.Forall₂.cons skA_E1_Q4_13_cert (List.Forall₂.cons skA_E1_Q4_14_cert (List.Forall₂.cons skA_E1_Q4_15_cert (List.Forall₂.cons skA_E1_Q4_16_cert (List.Forall₂.cons skA_E1_Q4_17_cert (List.Forall₂.cons skA_E1_Q4_18_cert (List.Forall₂.cons skA_E1_Q4_19_cert (List.Forall₂.cons skA_E1_Q4_20_cert (List.Forall₂.cons skA_E1_Q4_21_cert (List.Forall₂.cons skA_E1_Q4_22_cert (List.Forall₂.cons skA_E1_Q4_23_cert (List.Forall₂.cons skA_E1_Q4_24_cert (List.Forall₂.cons skA_E1_Q4_25_cert (List.Forall₂.cons skA_E1_Q4_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_4 skQ_E1_4_join

def skA_E1_Q5_0 : SectorVector := [(1,
  [((-5771362304 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((-14428405760 : Rat)/63, [0, 1, 1, 3]),
   ((-3607101440 : Rat)/21, [0, 1, 2, 2]),
   ((-721420288 : Rat)/21, [0, 5]),
   ((-57713623040 : Rat)/63, [1, 1, 1, 2]),
   ((-7214202880 : Rat)/21, [1, 4]),
   ((-14428405760 : Rat)/63, [2, 3])]),
 (-1,
  [((5771362304 : Rat)/63, [0, 1, 1, 1, 1, 1]),
   ((14428405760 : Rat)/63, [0, 1, 1, 3]),
   ((3607101440 : Rat)/21, [0, 1, 2, 2]),
   ((721420288 : Rat)/21, [0, 5]),
   ((-57713623040 : Rat)/63, [1, 1, 1, 2]),
   ((-7214202880 : Rat)/21, [1, 4]),
   ((-14428405760 : Rat)/63, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_0_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_0)) skA_E1_Q5_0 := by decide +kernel

def skA_E1_Q5_1 : SectorVector := [(1,
  [(-4194304, [0, 1, 1, 1, 1, 1]),
   (-10485760, [0, 1, 1, 3]),
   (-7864320, [0, 1, 2, 2]),
   (-1572864, [0, 5]),
   (-41943040, [1, 1, 1, 2]),
   (-15728640, [1, 4]),
   (-10485760, [2, 3])]),
 (-1,
  [(4194304, [0, 1, 1, 1, 1, 1]),
   (10485760, [0, 1, 1, 3]),
   (7864320, [0, 1, 2, 2]),
   (1572864, [0, 5]),
   (-41943040, [1, 1, 1, 2]),
   (-15728640, [1, 4]),
   (-10485760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_1_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_1)) skA_E1_Q5_1 := by decide +kernel

def skA_E1_Q5_2 : SectorVector := [(1,
  [((-645922816 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-1614807040 : Rat)/3, [0, 1, 1, 3]),
   (-403701760, [0, 1, 2, 2]),
   (-80740352, [0, 5]),
   ((-6459228160 : Rat)/3, [1, 1, 1, 2]),
   (-807403520, [1, 4]),
   ((-1614807040 : Rat)/3, [2, 3])]),
 (-1,
  [((645922816 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((1614807040 : Rat)/3, [0, 1, 1, 3]),
   (403701760, [0, 1, 2, 2]),
   (80740352, [0, 5]),
   ((-6459228160 : Rat)/3, [1, 1, 1, 2]),
   (-807403520, [1, 4]),
   ((-1614807040 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_2_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_2)) skA_E1_Q5_2 := by decide +kernel

def skA_E1_Q5_3 : SectorVector := [(1,
  [(-245366784, [0, 1, 1, 1, 1, 1]),
   (-613416960, [0, 1, 1, 3]),
   (-460062720, [0, 1, 2, 2]),
   (-92012544, [0, 5]),
   (-2453667840, [1, 1, 1, 2]),
   (-920125440, [1, 4]),
   (-613416960, [2, 3])]),
 (-1,
  [(245366784, [0, 1, 1, 1, 1, 1]),
   (613416960, [0, 1, 1, 3]),
   (460062720, [0, 1, 2, 2]),
   (92012544, [0, 5]),
   (-2453667840, [1, 1, 1, 2]),
   (-920125440, [1, 4]),
   (-613416960, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_3_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_3)) skA_E1_Q5_3 := by decide +kernel

def skA_E1_Q5_4 : SectorVector := [(1,
  [(41680896, [0, 1, 1, 1, 1, 1]),
   (104202240, [0, 1, 1, 3]),
   (78151680, [0, 1, 2, 2]),
   (15630336, [0, 5]),
   (416808960, [1, 1, 1, 2]),
   (156303360, [1, 4]),
   (104202240, [2, 3])]),
 (-1,
  [(-41680896, [0, 1, 1, 1, 1, 1]),
   (-104202240, [0, 1, 1, 3]),
   (-78151680, [0, 1, 2, 2]),
   (-15630336, [0, 5]),
   (416808960, [1, 1, 1, 2]),
   (156303360, [1, 4]),
   (104202240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_4_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_4)) skA_E1_Q5_4 := by decide +kernel

def skA_E1_Q5_5 : SectorVector := [(1,
  [(187957248, [0, 1, 1, 1, 1, 1]),
   (469893120, [0, 1, 1, 3]),
   (352419840, [0, 1, 2, 2]),
   (70483968, [0, 5]),
   (1879572480, [1, 1, 1, 2]),
   (704839680, [1, 4]),
   (469893120, [2, 3])]),
 (-1,
  [(-187957248, [0, 1, 1, 1, 1, 1]),
   (-469893120, [0, 1, 1, 3]),
   (-352419840, [0, 1, 2, 2]),
   (-70483968, [0, 5]),
   (1879572480, [1, 1, 1, 2]),
   (704839680, [1, 4]),
   (469893120, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_5_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_5)) skA_E1_Q5_5 := by decide +kernel

def skA_E1_Q5_6 : SectorVector := [(1,
  [(164495360, [0, 1, 1, 1, 1, 1]),
   (411238400, [0, 1, 1, 3]),
   (308428800, [0, 1, 2, 2]),
   (61685760, [0, 5]),
   (1644953600, [1, 1, 1, 2]),
   (616857600, [1, 4]),
   (411238400, [2, 3])]),
 (-1,
  [(-164495360, [0, 1, 1, 1, 1, 1]),
   (-411238400, [0, 1, 1, 3]),
   (-308428800, [0, 1, 2, 2]),
   (-61685760, [0, 5]),
   (1644953600, [1, 1, 1, 2]),
   (616857600, [1, 4]),
   (411238400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_6_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_6)) skA_E1_Q5_6 := by decide +kernel

def skA_E1_Q5_7 : SectorVector := [(1,
  [(86507520, [0, 1, 1, 1, 1, 1]),
   (216268800, [0, 1, 1, 3]),
   (162201600, [0, 1, 2, 2]),
   (32440320, [0, 5]),
   (865075200, [1, 1, 1, 2]),
   (324403200, [1, 4]),
   (216268800, [2, 3])]),
 (-1,
  [(-86507520, [0, 1, 1, 1, 1, 1]),
   (-216268800, [0, 1, 1, 3]),
   (-162201600, [0, 1, 2, 2]),
   (-32440320, [0, 5]),
   (865075200, [1, 1, 1, 2]),
   (324403200, [1, 4]),
   (216268800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_7_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_7)) skA_E1_Q5_7 := by decide +kernel

def skA_E1_Q5_8 : SectorVector := [(1,
  [((81264640 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((203161600 : Rat)/3, [0, 1, 1, 3]),
   (50790400, [0, 1, 2, 2]),
   (10158080, [0, 5]),
   ((812646400 : Rat)/3, [1, 1, 1, 2]),
   (101580800, [1, 4]),
   ((203161600 : Rat)/3, [2, 3])]),
 (-1,
  [((-81264640 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-203161600 : Rat)/3, [0, 1, 1, 3]),
   (-50790400, [0, 1, 2, 2]),
   (-10158080, [0, 5]),
   ((812646400 : Rat)/3, [1, 1, 1, 2]),
   (101580800, [1, 4]),
   ((203161600 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_8_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_8)) skA_E1_Q5_8 := by decide +kernel

def skA_E1_Q5_9 : SectorVector := [(1,
  [(-66846720, [0, 1, 1, 1, 1, 1]),
   (-167116800, [0, 1, 1, 3]),
   (-125337600, [0, 1, 2, 2]),
   (-25067520, [0, 5]),
   (-668467200, [1, 1, 1, 2]),
   (-250675200, [1, 4]),
   (-167116800, [2, 3])]),
 (-1,
  [(66846720, [0, 1, 1, 1, 1, 1]),
   (167116800, [0, 1, 1, 3]),
   (125337600, [0, 1, 2, 2]),
   (25067520, [0, 5]),
   (-668467200, [1, 1, 1, 2]),
   (-250675200, [1, 4]),
   (-167116800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_9_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_9)) skA_E1_Q5_9 := by decide +kernel

def skA_E1_Q5_10 : SectorVector := [(1,
  [(-43253760, [0, 1, 1, 1, 1, 1]),
   (-108134400, [0, 1, 1, 3]),
   (-81100800, [0, 1, 2, 2]),
   (-16220160, [0, 5]),
   (-432537600, [1, 1, 1, 2]),
   (-162201600, [1, 4]),
   (-108134400, [2, 3])]),
 (-1,
  [(43253760, [0, 1, 1, 1, 1, 1]),
   (108134400, [0, 1, 1, 3]),
   (81100800, [0, 1, 2, 2]),
   (16220160, [0, 5]),
   (-432537600, [1, 1, 1, 2]),
   (-162201600, [1, 4]),
   (-108134400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_10_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_10)) skA_E1_Q5_10 := by decide +kernel

def skA_E1_Q5_11 : SectorVector := [(1,
  [((266895360 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((667238400 : Rat)/7, [0, 1, 1, 3]),
   ((500428800 : Rat)/7, [0, 1, 2, 2]),
   ((100085760 : Rat)/7, [0, 5]),
   ((2668953600 : Rat)/7, [1, 1, 1, 2]),
   ((1000857600 : Rat)/7, [1, 4]),
   ((667238400 : Rat)/7, [2, 3])]),
 (-1,
  [((-266895360 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-667238400 : Rat)/7, [0, 1, 1, 3]),
   ((-500428800 : Rat)/7, [0, 1, 2, 2]),
   ((-100085760 : Rat)/7, [0, 5]),
   ((2668953600 : Rat)/7, [1, 1, 1, 2]),
   ((1000857600 : Rat)/7, [1, 4]),
   ((667238400 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_11_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_11)) skA_E1_Q5_11 := by decide +kernel

def skA_E1_Q5_12 : SectorVector := [(1,
  [(96829440, [0, 1, 1, 1, 1, 1]),
   (242073600, [0, 1, 1, 3]),
   (181555200, [0, 1, 2, 2]),
   (36311040, [0, 5]),
   (968294400, [1, 1, 1, 2]),
   (363110400, [1, 4]),
   (242073600, [2, 3])]),
 (-1,
  [(-96829440, [0, 1, 1, 1, 1, 1]),
   (-242073600, [0, 1, 1, 3]),
   (-181555200, [0, 1, 2, 2]),
   (-36311040, [0, 5]),
   (968294400, [1, 1, 1, 2]),
   (363110400, [1, 4]),
   (242073600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_12_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_12)) skA_E1_Q5_12 := by decide +kernel

def skA_E1_Q5_13 : SectorVector := [(1,
  [(114130944, [0, 1, 1, 1, 1, 1]),
   (285327360, [0, 1, 1, 3]),
   (213995520, [0, 1, 2, 2]),
   (42799104, [0, 5]),
   (1141309440, [1, 1, 1, 2]),
   (427991040, [1, 4]),
   (285327360, [2, 3])]),
 (-1,
  [(-114130944, [0, 1, 1, 1, 1, 1]),
   (-285327360, [0, 1, 1, 3]),
   (-213995520, [0, 1, 2, 2]),
   (-42799104, [0, 5]),
   (1141309440, [1, 1, 1, 2]),
   (427991040, [1, 4]),
   (285327360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_13_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_13)) skA_E1_Q5_13 := by decide +kernel

def skA_E1_Q5_14 : SectorVector := [(1,
  [(-6684672, [0, 1, 1, 1, 1, 1]),
   (-16711680, [0, 1, 1, 3]),
   (-12533760, [0, 1, 2, 2]),
   (-2506752, [0, 5]),
   (-66846720, [1, 1, 1, 2]),
   (-25067520, [1, 4]),
   (-16711680, [2, 3])]),
 (-1,
  [(6684672, [0, 1, 1, 1, 1, 1]),
   (16711680, [0, 1, 1, 3]),
   (12533760, [0, 1, 2, 2]),
   (2506752, [0, 5]),
   (-66846720, [1, 1, 1, 2]),
   (-25067520, [1, 4]),
   (-16711680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_14_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_14)) skA_E1_Q5_14 := by decide +kernel

def skA_E1_Q5_15 : SectorVector := [(1,
  [(42516480, [0, 1, 1, 1, 1, 1]),
   (106291200, [0, 1, 1, 3]),
   (79718400, [0, 1, 2, 2]),
   (15943680, [0, 5]),
   (425164800, [1, 1, 1, 2]),
   (159436800, [1, 4]),
   (106291200, [2, 3])]),
 (-1,
  [(-42516480, [0, 1, 1, 1, 1, 1]),
   (-106291200, [0, 1, 1, 3]),
   (-79718400, [0, 1, 2, 2]),
   (-15943680, [0, 5]),
   (425164800, [1, 1, 1, 2]),
   (159436800, [1, 4]),
   (106291200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_15_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_15)) skA_E1_Q5_15 := by decide +kernel

def skA_E1_Q5_16 : SectorVector := [(1,
  [(80412672, [0, 1, 1, 1, 1, 1]),
   (201031680, [0, 1, 1, 3]),
   (150773760, [0, 1, 2, 2]),
   (30154752, [0, 5]),
   (804126720, [1, 1, 1, 2]),
   (301547520, [1, 4]),
   (201031680, [2, 3])]),
 (-1,
  [(-80412672, [0, 1, 1, 1, 1, 1]),
   (-201031680, [0, 1, 1, 3]),
   (-150773760, [0, 1, 2, 2]),
   (-30154752, [0, 5]),
   (804126720, [1, 1, 1, 2]),
   (301547520, [1, 4]),
   (201031680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_16_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_16)) skA_E1_Q5_16 := by decide +kernel

def skA_E1_Q5_17 : SectorVector := [(1,
  [(39075840, [0, 1, 1, 1, 1, 1]),
   (97689600, [0, 1, 1, 3]),
   (73267200, [0, 1, 2, 2]),
   (14653440, [0, 5]),
   (390758400, [1, 1, 1, 2]),
   (146534400, [1, 4]),
   (97689600, [2, 3])]),
 (-1,
  [(-39075840, [0, 1, 1, 1, 1, 1]),
   (-97689600, [0, 1, 1, 3]),
   (-73267200, [0, 1, 2, 2]),
   (-14653440, [0, 5]),
   (390758400, [1, 1, 1, 2]),
   (146534400, [1, 4]),
   (97689600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_17_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_17)) skA_E1_Q5_17 := by decide +kernel

def skA_E1_Q5_18 : SectorVector := [(1,
  [(24903680, [0, 1, 1, 1, 1, 1]),
   (62259200, [0, 1, 1, 3]),
   (46694400, [0, 1, 2, 2]),
   (9338880, [0, 5]),
   (249036800, [1, 1, 1, 2]),
   (93388800, [1, 4]),
   (62259200, [2, 3])]),
 (-1,
  [(-24903680, [0, 1, 1, 1, 1, 1]),
   (-62259200, [0, 1, 1, 3]),
   (-46694400, [0, 1, 2, 2]),
   (-9338880, [0, 5]),
   (249036800, [1, 1, 1, 2]),
   (93388800, [1, 4]),
   (62259200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_18_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_18)) skA_E1_Q5_18 := by decide +kernel

def skA_E1_Q5_19 : SectorVector := [(1,
  [(-36937728, [0, 1, 1, 1, 1, 1]),
   (-92344320, [0, 1, 1, 3]),
   (-69258240, [0, 1, 2, 2]),
   (-13851648, [0, 5]),
   (-369377280, [1, 1, 1, 2]),
   (-138516480, [1, 4]),
   (-92344320, [2, 3])]),
 (-1,
  [(36937728, [0, 1, 1, 1, 1, 1]),
   (92344320, [0, 1, 1, 3]),
   (69258240, [0, 1, 2, 2]),
   (13851648, [0, 5]),
   (-369377280, [1, 1, 1, 2]),
   (-138516480, [1, 4]),
   (-92344320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_19_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_19)) skA_E1_Q5_19 := by decide +kernel

def skA_E1_Q5_20 : SectorVector := [(1,
  [(6242304, [0, 1, 1, 1, 1, 1]),
   (15605760, [0, 1, 1, 3]),
   (11704320, [0, 1, 2, 2]),
   (2340864, [0, 5]),
   (62423040, [1, 1, 1, 2]),
   (23408640, [1, 4]),
   (15605760, [2, 3])]),
 (-1,
  [(-6242304, [0, 1, 1, 1, 1, 1]),
   (-15605760, [0, 1, 1, 3]),
   (-11704320, [0, 1, 2, 2]),
   (-2340864, [0, 5]),
   (62423040, [1, 1, 1, 2]),
   (23408640, [1, 4]),
   (15605760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_20_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_20)) skA_E1_Q5_20 := by decide +kernel

def skA_E1_Q5_21 : SectorVector := [(1,
  [(11919360, [0, 1, 1, 1, 1, 1]),
   (29798400, [0, 1, 1, 3]),
   (22348800, [0, 1, 2, 2]),
   (4469760, [0, 5]),
   (119193600, [1, 1, 1, 2]),
   (44697600, [1, 4]),
   (29798400, [2, 3])]),
 (-1,
  [(-11919360, [0, 1, 1, 1, 1, 1]),
   (-29798400, [0, 1, 1, 3]),
   (-22348800, [0, 1, 2, 2]),
   (-4469760, [0, 5]),
   (119193600, [1, 1, 1, 2]),
   (44697600, [1, 4]),
   (29798400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_21_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_21)) skA_E1_Q5_21 := by decide +kernel

def skA_E1_Q5_22 : SectorVector := [(1,
  [((19496960 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((48742400 : Rat)/9, [0, 1, 1, 3]),
   ((12185600 : Rat)/3, [0, 1, 2, 2]),
   ((2437120 : Rat)/3, [0, 5]),
   ((194969600 : Rat)/9, [1, 1, 1, 2]),
   ((24371200 : Rat)/3, [1, 4]),
   ((48742400 : Rat)/9, [2, 3])]),
 (-1,
  [((-19496960 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-48742400 : Rat)/9, [0, 1, 1, 3]),
   ((-12185600 : Rat)/3, [0, 1, 2, 2]),
   ((-2437120 : Rat)/3, [0, 5]),
   ((194969600 : Rat)/9, [1, 1, 1, 2]),
   ((24371200 : Rat)/3, [1, 4]),
   ((48742400 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_22_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_22)) skA_E1_Q5_22 := by decide +kernel

def skA_E1_Q5_23 : SectorVector := [(1,
  [(-5980160, [0, 1, 1, 1, 1, 1]),
   (-14950400, [0, 1, 1, 3]),
   (-11212800, [0, 1, 2, 2]),
   (-2242560, [0, 5]),
   (-59801600, [1, 1, 1, 2]),
   (-22425600, [1, 4]),
   (-14950400, [2, 3])]),
 (-1,
  [(5980160, [0, 1, 1, 1, 1, 1]),
   (14950400, [0, 1, 1, 3]),
   (11212800, [0, 1, 2, 2]),
   (2242560, [0, 5]),
   (-59801600, [1, 1, 1, 2]),
   (-22425600, [1, 4]),
   (-14950400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_23_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_23)) skA_E1_Q5_23 := by decide +kernel

def skA_E1_Q5_24 : SectorVector := [(1,
  [(2887680, [0, 1, 1, 1, 1, 1]),
   (7219200, [0, 1, 1, 3]),
   (5414400, [0, 1, 2, 2]),
   (1082880, [0, 5]),
   (28876800, [1, 1, 1, 2]),
   (10828800, [1, 4]),
   (7219200, [2, 3])]),
 (-1,
  [(-2887680, [0, 1, 1, 1, 1, 1]),
   (-7219200, [0, 1, 1, 3]),
   (-5414400, [0, 1, 2, 2]),
   (-1082880, [0, 5]),
   (28876800, [1, 1, 1, 2]),
   (10828800, [1, 4]),
   (7219200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_24_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_24)) skA_E1_Q5_24 := by decide +kernel

def skA_E1_Q5_25 : SectorVector := [(1,
  [(6359040, [0, 1, 1, 1, 1, 1]),
   (15897600, [0, 1, 1, 3]),
   (11923200, [0, 1, 2, 2]),
   (2384640, [0, 5]),
   (63590400, [1, 1, 1, 2]),
   (23846400, [1, 4]),
   (15897600, [2, 3])]),
 (-1,
  [(-6359040, [0, 1, 1, 1, 1, 1]),
   (-15897600, [0, 1, 1, 3]),
   (-11923200, [0, 1, 2, 2]),
   (-2384640, [0, 5]),
   (63590400, [1, 1, 1, 2]),
   (23846400, [1, 4]),
   (15897600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_25_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_25)) skA_E1_Q5_25 := by decide +kernel

def skA_E1_Q5_26 : SectorVector := [(1,
  [(7655424, [0, 1, 1, 1, 1, 1]),
   (19138560, [0, 1, 1, 3]),
   (14353920, [0, 1, 2, 2]),
   (2870784, [0, 5]),
   (76554240, [1, 1, 1, 2]),
   (28707840, [1, 4]),
   (19138560, [2, 3])]),
 (-1,
  [(-7655424, [0, 1, 1, 1, 1, 1]),
   (-19138560, [0, 1, 1, 3]),
   (-14353920, [0, 1, 2, 2]),
   (-2870784, [0, 5]),
   (76554240, [1, 1, 1, 2]),
   (28707840, [1, 4]),
   (19138560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q5_26_cert : VectorCertificate (Tpow 5 (aLeft false (10 : ℤ) skM_E1_26)) skA_E1_Q5_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_5_join : VectorCertificate ([skA_E1_Q5_0, skA_E1_Q5_1, skA_E1_Q5_2, skA_E1_Q5_3, skA_E1_Q5_4, skA_E1_Q5_5, skA_E1_Q5_6, skA_E1_Q5_7, skA_E1_Q5_8, skA_E1_Q5_9, skA_E1_Q5_10, skA_E1_Q5_11, skA_E1_Q5_12, skA_E1_Q5_13, skA_E1_Q5_14, skA_E1_Q5_15, skA_E1_Q5_16, skA_E1_Q5_17, skA_E1_Q5_18, skA_E1_Q5_19, skA_E1_Q5_20, skA_E1_Q5_21, skA_E1_Q5_22, skA_E1_Q5_23, skA_E1_Q5_24, skA_E1_Q5_25, skA_E1_Q5_26] : List SectorVector).flatten skQ_E1_5 := by decide +kernel

theorem skQ_E1_5_val : evaluate skQ_E1_5 = evaluate (OrbSgl.vTerm false skY_E1 1 5) :=
  vTerm_of_chunks false skY_E1 1 5 (10 : ℤ) (by norm_num) skM_E1 [skA_E1_Q5_0, skA_E1_Q5_1, skA_E1_Q5_2, skA_E1_Q5_3, skA_E1_Q5_4, skA_E1_Q5_5, skA_E1_Q5_6, skA_E1_Q5_7, skA_E1_Q5_8, skA_E1_Q5_9, skA_E1_Q5_10, skA_E1_Q5_11, skA_E1_Q5_12, skA_E1_Q5_13, skA_E1_Q5_14, skA_E1_Q5_15, skA_E1_Q5_16, skA_E1_Q5_17, skA_E1_Q5_18, skA_E1_Q5_19, skA_E1_Q5_20, skA_E1_Q5_21, skA_E1_Q5_22, skA_E1_Q5_23, skA_E1_Q5_24, skA_E1_Q5_25, skA_E1_Q5_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q5_0_cert (List.Forall₂.cons skA_E1_Q5_1_cert (List.Forall₂.cons skA_E1_Q5_2_cert (List.Forall₂.cons skA_E1_Q5_3_cert (List.Forall₂.cons skA_E1_Q5_4_cert (List.Forall₂.cons skA_E1_Q5_5_cert (List.Forall₂.cons skA_E1_Q5_6_cert (List.Forall₂.cons skA_E1_Q5_7_cert (List.Forall₂.cons skA_E1_Q5_8_cert (List.Forall₂.cons skA_E1_Q5_9_cert (List.Forall₂.cons skA_E1_Q5_10_cert (List.Forall₂.cons skA_E1_Q5_11_cert (List.Forall₂.cons skA_E1_Q5_12_cert (List.Forall₂.cons skA_E1_Q5_13_cert (List.Forall₂.cons skA_E1_Q5_14_cert (List.Forall₂.cons skA_E1_Q5_15_cert (List.Forall₂.cons skA_E1_Q5_16_cert (List.Forall₂.cons skA_E1_Q5_17_cert (List.Forall₂.cons skA_E1_Q5_18_cert (List.Forall₂.cons skA_E1_Q5_19_cert (List.Forall₂.cons skA_E1_Q5_20_cert (List.Forall₂.cons skA_E1_Q5_21_cert (List.Forall₂.cons skA_E1_Q5_22_cert (List.Forall₂.cons skA_E1_Q5_23_cert (List.Forall₂.cons skA_E1_Q5_24_cert (List.Forall₂.cons skA_E1_Q5_25_cert (List.Forall₂.cons skA_E1_Q5_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_5 skQ_E1_5_join

def skA_E1_Q6_0 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_0_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_0)) skA_E1_Q6_0 := by decide +kernel

def skA_E1_Q6_1 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_1_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_1)) skA_E1_Q6_1 := by decide +kernel

def skA_E1_Q6_2 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_2_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_2)) skA_E1_Q6_2 := by decide +kernel

def skA_E1_Q6_3 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_3_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_3)) skA_E1_Q6_3 := by decide +kernel

def skA_E1_Q6_4 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_4_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_4)) skA_E1_Q6_4 := by decide +kernel

def skA_E1_Q6_5 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_5_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_5)) skA_E1_Q6_5 := by decide +kernel

def skA_E1_Q6_6 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_6_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_6)) skA_E1_Q6_6 := by decide +kernel

def skA_E1_Q6_7 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_7_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_7)) skA_E1_Q6_7 := by decide +kernel

def skA_E1_Q6_8 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_8_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_8)) skA_E1_Q6_8 := by decide +kernel

def skA_E1_Q6_9 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_9_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_9)) skA_E1_Q6_9 := by decide +kernel

def skA_E1_Q6_10 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_10_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_10)) skA_E1_Q6_10 := by decide +kernel

def skA_E1_Q6_11 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_11_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_11)) skA_E1_Q6_11 := by decide +kernel

def skA_E1_Q6_12 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_12_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_12)) skA_E1_Q6_12 := by decide +kernel

def skA_E1_Q6_13 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_13_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_13)) skA_E1_Q6_13 := by decide +kernel

def skA_E1_Q6_14 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_14_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_14)) skA_E1_Q6_14 := by decide +kernel

def skA_E1_Q6_15 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_15_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_15)) skA_E1_Q6_15 := by decide +kernel

def skA_E1_Q6_16 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_16_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_16)) skA_E1_Q6_16 := by decide +kernel

def skA_E1_Q6_17 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_17_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_17)) skA_E1_Q6_17 := by decide +kernel

def skA_E1_Q6_18 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_18_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_18)) skA_E1_Q6_18 := by decide +kernel

def skA_E1_Q6_19 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_19_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_19)) skA_E1_Q6_19 := by decide +kernel

def skA_E1_Q6_20 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_20_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_20)) skA_E1_Q6_20 := by decide +kernel

def skA_E1_Q6_21 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_21_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_21)) skA_E1_Q6_21 := by decide +kernel

def skA_E1_Q6_22 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_22_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_22)) skA_E1_Q6_22 := by decide +kernel

def skA_E1_Q6_23 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_23_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_23)) skA_E1_Q6_23 := by decide +kernel

def skA_E1_Q6_24 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_24_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_24)) skA_E1_Q6_24 := by decide +kernel

def skA_E1_Q6_25 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_25_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_25)) skA_E1_Q6_25 := by decide +kernel

def skA_E1_Q6_26 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q6_26_cert : VectorCertificate (Tpow 6 (aLeft false (11 : ℤ) skM_E1_26)) skA_E1_Q6_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_6_join : VectorCertificate ([skA_E1_Q6_0, skA_E1_Q6_1, skA_E1_Q6_2, skA_E1_Q6_3, skA_E1_Q6_4, skA_E1_Q6_5, skA_E1_Q6_6, skA_E1_Q6_7, skA_E1_Q6_8, skA_E1_Q6_9, skA_E1_Q6_10, skA_E1_Q6_11, skA_E1_Q6_12, skA_E1_Q6_13, skA_E1_Q6_14, skA_E1_Q6_15, skA_E1_Q6_16, skA_E1_Q6_17, skA_E1_Q6_18, skA_E1_Q6_19, skA_E1_Q6_20, skA_E1_Q6_21, skA_E1_Q6_22, skA_E1_Q6_23, skA_E1_Q6_24, skA_E1_Q6_25, skA_E1_Q6_26] : List SectorVector).flatten skQ_E1_6 := by decide +kernel

theorem skQ_E1_6_val : evaluate skQ_E1_6 = evaluate (OrbSgl.vTerm false skY_E1 1 6) :=
  vTerm_of_chunks false skY_E1 1 6 (11 : ℤ) (by norm_num) skM_E1 [skA_E1_Q6_0, skA_E1_Q6_1, skA_E1_Q6_2, skA_E1_Q6_3, skA_E1_Q6_4, skA_E1_Q6_5, skA_E1_Q6_6, skA_E1_Q6_7, skA_E1_Q6_8, skA_E1_Q6_9, skA_E1_Q6_10, skA_E1_Q6_11, skA_E1_Q6_12, skA_E1_Q6_13, skA_E1_Q6_14, skA_E1_Q6_15, skA_E1_Q6_16, skA_E1_Q6_17, skA_E1_Q6_18, skA_E1_Q6_19, skA_E1_Q6_20, skA_E1_Q6_21, skA_E1_Q6_22, skA_E1_Q6_23, skA_E1_Q6_24, skA_E1_Q6_25, skA_E1_Q6_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q6_0_cert (List.Forall₂.cons skA_E1_Q6_1_cert (List.Forall₂.cons skA_E1_Q6_2_cert (List.Forall₂.cons skA_E1_Q6_3_cert (List.Forall₂.cons skA_E1_Q6_4_cert (List.Forall₂.cons skA_E1_Q6_5_cert (List.Forall₂.cons skA_E1_Q6_6_cert (List.Forall₂.cons skA_E1_Q6_7_cert (List.Forall₂.cons skA_E1_Q6_8_cert (List.Forall₂.cons skA_E1_Q6_9_cert (List.Forall₂.cons skA_E1_Q6_10_cert (List.Forall₂.cons skA_E1_Q6_11_cert (List.Forall₂.cons skA_E1_Q6_12_cert (List.Forall₂.cons skA_E1_Q6_13_cert (List.Forall₂.cons skA_E1_Q6_14_cert (List.Forall₂.cons skA_E1_Q6_15_cert (List.Forall₂.cons skA_E1_Q6_16_cert (List.Forall₂.cons skA_E1_Q6_17_cert (List.Forall₂.cons skA_E1_Q6_18_cert (List.Forall₂.cons skA_E1_Q6_19_cert (List.Forall₂.cons skA_E1_Q6_20_cert (List.Forall₂.cons skA_E1_Q6_21_cert (List.Forall₂.cons skA_E1_Q6_22_cert (List.Forall₂.cons skA_E1_Q6_23_cert (List.Forall₂.cons skA_E1_Q6_24_cert (List.Forall₂.cons skA_E1_Q6_25_cert (List.Forall₂.cons skA_E1_Q6_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_6 skQ_E1_6_join

def skA_E1_Q7_0 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_0_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_0)) skA_E1_Q7_0 := by decide +kernel

def skA_E1_Q7_1 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_1_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_1)) skA_E1_Q7_1 := by decide +kernel

def skA_E1_Q7_2 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_2_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_2)) skA_E1_Q7_2 := by decide +kernel

def skA_E1_Q7_3 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_3_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_3)) skA_E1_Q7_3 := by decide +kernel

def skA_E1_Q7_4 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_4_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_4)) skA_E1_Q7_4 := by decide +kernel

def skA_E1_Q7_5 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_5_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_5)) skA_E1_Q7_5 := by decide +kernel

def skA_E1_Q7_6 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_6_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_6)) skA_E1_Q7_6 := by decide +kernel

def skA_E1_Q7_7 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_7_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_7)) skA_E1_Q7_7 := by decide +kernel

def skA_E1_Q7_8 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_8_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_8)) skA_E1_Q7_8 := by decide +kernel

def skA_E1_Q7_9 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_9_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_9)) skA_E1_Q7_9 := by decide +kernel

def skA_E1_Q7_10 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_10_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_10)) skA_E1_Q7_10 := by decide +kernel

def skA_E1_Q7_11 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_11_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_11)) skA_E1_Q7_11 := by decide +kernel

def skA_E1_Q7_12 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_12_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_12)) skA_E1_Q7_12 := by decide +kernel

def skA_E1_Q7_13 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_13_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_13)) skA_E1_Q7_13 := by decide +kernel

def skA_E1_Q7_14 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_14_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_14)) skA_E1_Q7_14 := by decide +kernel

def skA_E1_Q7_15 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_15_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_15)) skA_E1_Q7_15 := by decide +kernel

def skA_E1_Q7_16 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_16_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_16)) skA_E1_Q7_16 := by decide +kernel

def skA_E1_Q7_17 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_17_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_17)) skA_E1_Q7_17 := by decide +kernel

def skA_E1_Q7_18 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_18_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_18)) skA_E1_Q7_18 := by decide +kernel

def skA_E1_Q7_19 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_19_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_19)) skA_E1_Q7_19 := by decide +kernel

def skA_E1_Q7_20 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_20_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_20)) skA_E1_Q7_20 := by decide +kernel

def skA_E1_Q7_21 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_21_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_21)) skA_E1_Q7_21 := by decide +kernel

def skA_E1_Q7_22 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_22_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_22)) skA_E1_Q7_22 := by decide +kernel

def skA_E1_Q7_23 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_23_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_23)) skA_E1_Q7_23 := by decide +kernel

def skA_E1_Q7_24 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_24_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_24)) skA_E1_Q7_24 := by decide +kernel

def skA_E1_Q7_25 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_25_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_25)) skA_E1_Q7_25 := by decide +kernel

def skA_E1_Q7_26 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q7_26_cert : VectorCertificate (Tpow 7 (aLeft false (12 : ℤ) skM_E1_26)) skA_E1_Q7_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_7_join : VectorCertificate ([skA_E1_Q7_0, skA_E1_Q7_1, skA_E1_Q7_2, skA_E1_Q7_3, skA_E1_Q7_4, skA_E1_Q7_5, skA_E1_Q7_6, skA_E1_Q7_7, skA_E1_Q7_8, skA_E1_Q7_9, skA_E1_Q7_10, skA_E1_Q7_11, skA_E1_Q7_12, skA_E1_Q7_13, skA_E1_Q7_14, skA_E1_Q7_15, skA_E1_Q7_16, skA_E1_Q7_17, skA_E1_Q7_18, skA_E1_Q7_19, skA_E1_Q7_20, skA_E1_Q7_21, skA_E1_Q7_22, skA_E1_Q7_23, skA_E1_Q7_24, skA_E1_Q7_25, skA_E1_Q7_26] : List SectorVector).flatten skQ_E1_7 := by decide +kernel

theorem skQ_E1_7_val : evaluate skQ_E1_7 = evaluate (OrbSgl.vTerm false skY_E1 1 7) :=
  vTerm_of_chunks false skY_E1 1 7 (12 : ℤ) (by norm_num) skM_E1 [skA_E1_Q7_0, skA_E1_Q7_1, skA_E1_Q7_2, skA_E1_Q7_3, skA_E1_Q7_4, skA_E1_Q7_5, skA_E1_Q7_6, skA_E1_Q7_7, skA_E1_Q7_8, skA_E1_Q7_9, skA_E1_Q7_10, skA_E1_Q7_11, skA_E1_Q7_12, skA_E1_Q7_13, skA_E1_Q7_14, skA_E1_Q7_15, skA_E1_Q7_16, skA_E1_Q7_17, skA_E1_Q7_18, skA_E1_Q7_19, skA_E1_Q7_20, skA_E1_Q7_21, skA_E1_Q7_22, skA_E1_Q7_23, skA_E1_Q7_24, skA_E1_Q7_25, skA_E1_Q7_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q7_0_cert (List.Forall₂.cons skA_E1_Q7_1_cert (List.Forall₂.cons skA_E1_Q7_2_cert (List.Forall₂.cons skA_E1_Q7_3_cert (List.Forall₂.cons skA_E1_Q7_4_cert (List.Forall₂.cons skA_E1_Q7_5_cert (List.Forall₂.cons skA_E1_Q7_6_cert (List.Forall₂.cons skA_E1_Q7_7_cert (List.Forall₂.cons skA_E1_Q7_8_cert (List.Forall₂.cons skA_E1_Q7_9_cert (List.Forall₂.cons skA_E1_Q7_10_cert (List.Forall₂.cons skA_E1_Q7_11_cert (List.Forall₂.cons skA_E1_Q7_12_cert (List.Forall₂.cons skA_E1_Q7_13_cert (List.Forall₂.cons skA_E1_Q7_14_cert (List.Forall₂.cons skA_E1_Q7_15_cert (List.Forall₂.cons skA_E1_Q7_16_cert (List.Forall₂.cons skA_E1_Q7_17_cert (List.Forall₂.cons skA_E1_Q7_18_cert (List.Forall₂.cons skA_E1_Q7_19_cert (List.Forall₂.cons skA_E1_Q7_20_cert (List.Forall₂.cons skA_E1_Q7_21_cert (List.Forall₂.cons skA_E1_Q7_22_cert (List.Forall₂.cons skA_E1_Q7_23_cert (List.Forall₂.cons skA_E1_Q7_24_cert (List.Forall₂.cons skA_E1_Q7_25_cert (List.Forall₂.cons skA_E1_Q7_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_7 skQ_E1_7_join

def skA_E1_Q8_0 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_0_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_0)) skA_E1_Q8_0 := by decide +kernel

def skA_E1_Q8_1 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_1_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_1)) skA_E1_Q8_1 := by decide +kernel

def skA_E1_Q8_2 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_2_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_2)) skA_E1_Q8_2 := by decide +kernel

def skA_E1_Q8_3 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_3_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_3)) skA_E1_Q8_3 := by decide +kernel

def skA_E1_Q8_4 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_4_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_4)) skA_E1_Q8_4 := by decide +kernel

def skA_E1_Q8_5 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_5_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_5)) skA_E1_Q8_5 := by decide +kernel

def skA_E1_Q8_6 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_6_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_6)) skA_E1_Q8_6 := by decide +kernel

def skA_E1_Q8_7 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_7_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_7)) skA_E1_Q8_7 := by decide +kernel

def skA_E1_Q8_8 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_8_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_8)) skA_E1_Q8_8 := by decide +kernel

def skA_E1_Q8_9 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_9_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_9)) skA_E1_Q8_9 := by decide +kernel

def skA_E1_Q8_10 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_10_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_10)) skA_E1_Q8_10 := by decide +kernel

def skA_E1_Q8_11 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_11_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_11)) skA_E1_Q8_11 := by decide +kernel

def skA_E1_Q8_12 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_12_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_12)) skA_E1_Q8_12 := by decide +kernel

def skA_E1_Q8_13 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_13_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_13)) skA_E1_Q8_13 := by decide +kernel

def skA_E1_Q8_14 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_14_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_14)) skA_E1_Q8_14 := by decide +kernel

def skA_E1_Q8_15 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_15_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_15)) skA_E1_Q8_15 := by decide +kernel

def skA_E1_Q8_16 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_16_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_16)) skA_E1_Q8_16 := by decide +kernel

def skA_E1_Q8_17 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_17_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_17)) skA_E1_Q8_17 := by decide +kernel

def skA_E1_Q8_18 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_18_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_18)) skA_E1_Q8_18 := by decide +kernel

def skA_E1_Q8_19 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_19_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_19)) skA_E1_Q8_19 := by decide +kernel

def skA_E1_Q8_20 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_20_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_20)) skA_E1_Q8_20 := by decide +kernel

def skA_E1_Q8_21 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_21_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_21)) skA_E1_Q8_21 := by decide +kernel

def skA_E1_Q8_22 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_22_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_22)) skA_E1_Q8_22 := by decide +kernel

def skA_E1_Q8_23 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_23_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_23)) skA_E1_Q8_23 := by decide +kernel

def skA_E1_Q8_24 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_24_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_24)) skA_E1_Q8_24 := by decide +kernel

def skA_E1_Q8_25 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_25_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_25)) skA_E1_Q8_25 := by decide +kernel

def skA_E1_Q8_26 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q8_26_cert : VectorCertificate (Tpow 8 (aLeft false (13 : ℤ) skM_E1_26)) skA_E1_Q8_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_8_join : VectorCertificate ([skA_E1_Q8_0, skA_E1_Q8_1, skA_E1_Q8_2, skA_E1_Q8_3, skA_E1_Q8_4, skA_E1_Q8_5, skA_E1_Q8_6, skA_E1_Q8_7, skA_E1_Q8_8, skA_E1_Q8_9, skA_E1_Q8_10, skA_E1_Q8_11, skA_E1_Q8_12, skA_E1_Q8_13, skA_E1_Q8_14, skA_E1_Q8_15, skA_E1_Q8_16, skA_E1_Q8_17, skA_E1_Q8_18, skA_E1_Q8_19, skA_E1_Q8_20, skA_E1_Q8_21, skA_E1_Q8_22, skA_E1_Q8_23, skA_E1_Q8_24, skA_E1_Q8_25, skA_E1_Q8_26] : List SectorVector).flatten skQ_E1_8 := by decide +kernel

theorem skQ_E1_8_val : evaluate skQ_E1_8 = evaluate (OrbSgl.vTerm false skY_E1 1 8) :=
  vTerm_of_chunks false skY_E1 1 8 (13 : ℤ) (by norm_num) skM_E1 [skA_E1_Q8_0, skA_E1_Q8_1, skA_E1_Q8_2, skA_E1_Q8_3, skA_E1_Q8_4, skA_E1_Q8_5, skA_E1_Q8_6, skA_E1_Q8_7, skA_E1_Q8_8, skA_E1_Q8_9, skA_E1_Q8_10, skA_E1_Q8_11, skA_E1_Q8_12, skA_E1_Q8_13, skA_E1_Q8_14, skA_E1_Q8_15, skA_E1_Q8_16, skA_E1_Q8_17, skA_E1_Q8_18, skA_E1_Q8_19, skA_E1_Q8_20, skA_E1_Q8_21, skA_E1_Q8_22, skA_E1_Q8_23, skA_E1_Q8_24, skA_E1_Q8_25, skA_E1_Q8_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q8_0_cert (List.Forall₂.cons skA_E1_Q8_1_cert (List.Forall₂.cons skA_E1_Q8_2_cert (List.Forall₂.cons skA_E1_Q8_3_cert (List.Forall₂.cons skA_E1_Q8_4_cert (List.Forall₂.cons skA_E1_Q8_5_cert (List.Forall₂.cons skA_E1_Q8_6_cert (List.Forall₂.cons skA_E1_Q8_7_cert (List.Forall₂.cons skA_E1_Q8_8_cert (List.Forall₂.cons skA_E1_Q8_9_cert (List.Forall₂.cons skA_E1_Q8_10_cert (List.Forall₂.cons skA_E1_Q8_11_cert (List.Forall₂.cons skA_E1_Q8_12_cert (List.Forall₂.cons skA_E1_Q8_13_cert (List.Forall₂.cons skA_E1_Q8_14_cert (List.Forall₂.cons skA_E1_Q8_15_cert (List.Forall₂.cons skA_E1_Q8_16_cert (List.Forall₂.cons skA_E1_Q8_17_cert (List.Forall₂.cons skA_E1_Q8_18_cert (List.Forall₂.cons skA_E1_Q8_19_cert (List.Forall₂.cons skA_E1_Q8_20_cert (List.Forall₂.cons skA_E1_Q8_21_cert (List.Forall₂.cons skA_E1_Q8_22_cert (List.Forall₂.cons skA_E1_Q8_23_cert (List.Forall₂.cons skA_E1_Q8_24_cert (List.Forall₂.cons skA_E1_Q8_25_cert (List.Forall₂.cons skA_E1_Q8_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_8 skQ_E1_8_join

def skA_E1_Q9_0 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_0_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_0)) skA_E1_Q9_0 := by decide +kernel

def skA_E1_Q9_1 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_1_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_1)) skA_E1_Q9_1 := by decide +kernel

def skA_E1_Q9_2 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_2_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_2)) skA_E1_Q9_2 := by decide +kernel

def skA_E1_Q9_3 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_3_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_3)) skA_E1_Q9_3 := by decide +kernel

def skA_E1_Q9_4 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_4_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_4)) skA_E1_Q9_4 := by decide +kernel

def skA_E1_Q9_5 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_5_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_5)) skA_E1_Q9_5 := by decide +kernel

def skA_E1_Q9_6 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_6_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_6)) skA_E1_Q9_6 := by decide +kernel

def skA_E1_Q9_7 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_7_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_7)) skA_E1_Q9_7 := by decide +kernel

def skA_E1_Q9_8 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_8_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_8)) skA_E1_Q9_8 := by decide +kernel

def skA_E1_Q9_9 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_9_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_9)) skA_E1_Q9_9 := by decide +kernel

def skA_E1_Q9_10 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_10_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_10)) skA_E1_Q9_10 := by decide +kernel

def skA_E1_Q9_11 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_11_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_11)) skA_E1_Q9_11 := by decide +kernel

def skA_E1_Q9_12 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_12_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_12)) skA_E1_Q9_12 := by decide +kernel

def skA_E1_Q9_13 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_13_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_13)) skA_E1_Q9_13 := by decide +kernel

def skA_E1_Q9_14 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_14_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_14)) skA_E1_Q9_14 := by decide +kernel

def skA_E1_Q9_15 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_15_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_15)) skA_E1_Q9_15 := by decide +kernel

def skA_E1_Q9_16 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_16_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_16)) skA_E1_Q9_16 := by decide +kernel

def skA_E1_Q9_17 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_17_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_17)) skA_E1_Q9_17 := by decide +kernel

def skA_E1_Q9_18 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_18_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_18)) skA_E1_Q9_18 := by decide +kernel

def skA_E1_Q9_19 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_19_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_19)) skA_E1_Q9_19 := by decide +kernel

def skA_E1_Q9_20 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_20_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_20)) skA_E1_Q9_20 := by decide +kernel

def skA_E1_Q9_21 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_21_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_21)) skA_E1_Q9_21 := by decide +kernel

def skA_E1_Q9_22 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_22_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_22)) skA_E1_Q9_22 := by decide +kernel

def skA_E1_Q9_23 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_23_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_23)) skA_E1_Q9_23 := by decide +kernel

def skA_E1_Q9_24 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_24_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_24)) skA_E1_Q9_24 := by decide +kernel

def skA_E1_Q9_25 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_25_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_25)) skA_E1_Q9_25 := by decide +kernel

def skA_E1_Q9_26 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E1_Q9_26_cert : VectorCertificate (Tpow 9 (aLeft false (14 : ℤ) skM_E1_26)) skA_E1_Q9_26 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E1_9_join : VectorCertificate ([skA_E1_Q9_0, skA_E1_Q9_1, skA_E1_Q9_2, skA_E1_Q9_3, skA_E1_Q9_4, skA_E1_Q9_5, skA_E1_Q9_6, skA_E1_Q9_7, skA_E1_Q9_8, skA_E1_Q9_9, skA_E1_Q9_10, skA_E1_Q9_11, skA_E1_Q9_12, skA_E1_Q9_13, skA_E1_Q9_14, skA_E1_Q9_15, skA_E1_Q9_16, skA_E1_Q9_17, skA_E1_Q9_18, skA_E1_Q9_19, skA_E1_Q9_20, skA_E1_Q9_21, skA_E1_Q9_22, skA_E1_Q9_23, skA_E1_Q9_24, skA_E1_Q9_25, skA_E1_Q9_26] : List SectorVector).flatten skQ_E1_9 := by decide +kernel

theorem skQ_E1_9_val : evaluate skQ_E1_9 = evaluate (OrbSgl.vTerm false skY_E1 1 9) :=
  vTerm_of_chunks false skY_E1 1 9 (14 : ℤ) (by norm_num) skM_E1 [skA_E1_Q9_0, skA_E1_Q9_1, skA_E1_Q9_2, skA_E1_Q9_3, skA_E1_Q9_4, skA_E1_Q9_5, skA_E1_Q9_6, skA_E1_Q9_7, skA_E1_Q9_8, skA_E1_Q9_9, skA_E1_Q9_10, skA_E1_Q9_11, skA_E1_Q9_12, skA_E1_Q9_13, skA_E1_Q9_14, skA_E1_Q9_15, skA_E1_Q9_16, skA_E1_Q9_17, skA_E1_Q9_18, skA_E1_Q9_19, skA_E1_Q9_20, skA_E1_Q9_21, skA_E1_Q9_22, skA_E1_Q9_23, skA_E1_Q9_24, skA_E1_Q9_25, skA_E1_Q9_26] skM_E1_cert
    (List.Forall₂.cons skA_E1_Q9_0_cert (List.Forall₂.cons skA_E1_Q9_1_cert (List.Forall₂.cons skA_E1_Q9_2_cert (List.Forall₂.cons skA_E1_Q9_3_cert (List.Forall₂.cons skA_E1_Q9_4_cert (List.Forall₂.cons skA_E1_Q9_5_cert (List.Forall₂.cons skA_E1_Q9_6_cert (List.Forall₂.cons skA_E1_Q9_7_cert (List.Forall₂.cons skA_E1_Q9_8_cert (List.Forall₂.cons skA_E1_Q9_9_cert (List.Forall₂.cons skA_E1_Q9_10_cert (List.Forall₂.cons skA_E1_Q9_11_cert (List.Forall₂.cons skA_E1_Q9_12_cert (List.Forall₂.cons skA_E1_Q9_13_cert (List.Forall₂.cons skA_E1_Q9_14_cert (List.Forall₂.cons skA_E1_Q9_15_cert (List.Forall₂.cons skA_E1_Q9_16_cert (List.Forall₂.cons skA_E1_Q9_17_cert (List.Forall₂.cons skA_E1_Q9_18_cert (List.Forall₂.cons skA_E1_Q9_19_cert (List.Forall₂.cons skA_E1_Q9_20_cert (List.Forall₂.cons skA_E1_Q9_21_cert (List.Forall₂.cons skA_E1_Q9_22_cert (List.Forall₂.cons skA_E1_Q9_23_cert (List.Forall₂.cons skA_E1_Q9_24_cert (List.Forall₂.cons skA_E1_Q9_25_cert (List.Forall₂.cons skA_E1_Q9_26_cert List.Forall₂.nil)))))))))))))))))))))))))))
    skQ_E1_9 skQ_E1_9_join

theorem skY_E1_value : evaluate skY_E1 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 1 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E1_cert]
  apply evaluate_uSum false 1 (by norm_num)
  intro i hi
  interval_cases i
  · exact skP_E1_0_val
  · exact skP_E1_1_val
  · exact skP_E1_2_val
  · exact skP_E1_3_val
  · exact skP_E1_4_val
  · exact skP_E1_5_val
  · exact skP_E1_6_val
  · exact skP_E1_7_val
  · exact skP_E1_8_val
  · exact skP_E1_9_val
  · exact skP_E1_10_val
  · exact skP_E1_11_val

/-- The certified value of `termE_1`. -/
theorem sk_E1 : evaluate termE_1 = ((Nat.choose 15 1 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 1 (aVec false))
      (6 - (1 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E1_cert]
  apply evaluate_vSum false 1 (by norm_num) skY_E1 skY_E1_value
  intro j hj
  interval_cases j
  · exact skQ_E1_0_val
  · exact skQ_E1_1_val
  · exact skQ_E1_2_val
  · exact skQ_E1_3_val
  · exact skQ_E1_4_val
  · exact skQ_E1_5_val
  · exact skQ_E1_6_val
  · exact skQ_E1_7_val
  · exact skQ_E1_8_val
  · exact skQ_E1_9_val

end VOA.Classification.COne.OrbSgl

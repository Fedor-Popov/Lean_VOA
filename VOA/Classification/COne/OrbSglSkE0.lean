import VOA.Classification.COne.OrbSglSkE0a

/-! # OrbSgl: chunked evaluation of `C(15,0) (u₍0₎a)₍6₎a`, `a = E`: stage 2 and `sk_E0`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skA_E0_Q0_0 : SectorVector := [(-1,
  [((-67108864 : Rat)/22275, [0, 1, 1, 1, 1, 1]),
   ((268435456 : Rat)/31185, [0, 1, 1, 3]),
   ((-536870912 : Rat)/10395, [0, 1, 2, 2]),
   ((1073741824 : Rat)/51975, [0, 5]),
   ((-268435456 : Rat)/4455, [1, 1, 1, 2]),
   ((1073741824 : Rat)/10395, [1, 4]),
   ((-4294967296 : Rat)/31185, [2, 3])]),
 (1,
  [((67108864 : Rat)/22275, [0, 1, 1, 1, 1, 1]),
   ((-268435456 : Rat)/31185, [0, 1, 1, 3]),
   ((536870912 : Rat)/10395, [0, 1, 2, 2]),
   ((-1073741824 : Rat)/51975, [0, 5]),
   ((-268435456 : Rat)/4455, [1, 1, 1, 2]),
   ((1073741824 : Rat)/10395, [1, 4]),
   ((-4294967296 : Rat)/31185, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_0_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_0)) skA_E0_Q0_0 := by decide +kernel

def skA_E0_Q0_1 : SectorVector := [(-1,
  [((3014656 : Rat)/405, [0, 1, 1, 1, 1, 1]),
   ((-10485760 : Rat)/81, [0, 1, 1, 3]),
   ((-4194304 : Rat)/27, [0, 1, 2, 2]),
   ((33554432 : Rat)/135, [0, 5]),
   ((-8388608 : Rat)/81, [1, 1, 1, 2]),
   ((8388608 : Rat)/27, [1, 4]),
   ((-83886080 : Rat)/81, [2, 3])]),
 (1,
  [((-3014656 : Rat)/405, [0, 1, 1, 1, 1, 1]),
   ((10485760 : Rat)/81, [0, 1, 1, 3]),
   ((4194304 : Rat)/27, [0, 1, 2, 2]),
   ((-33554432 : Rat)/135, [0, 5]),
   ((-8388608 : Rat)/81, [1, 1, 1, 2]),
   ((8388608 : Rat)/27, [1, 4]),
   ((-83886080 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_1_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_1)) skA_E0_Q0_1 := by decide +kernel

def skA_E0_Q0_2 : SectorVector := [(-1,
  [((8912896 : Rat)/105, [0, 1, 1, 1, 1, 1]),
   ((-16777216 : Rat)/21, [0, 1, 1, 3]),
   ((33554432 : Rat)/35, [0, 5]),
   ((8388608 : Rat)/21, [1, 1, 1, 2]),
   ((-67108864 : Rat)/21, [2, 3])]),
 (1,
  [((-8912896 : Rat)/105, [0, 1, 1, 1, 1, 1]),
   ((16777216 : Rat)/21, [0, 1, 1, 3]),
   ((-33554432 : Rat)/35, [0, 5]),
   ((8388608 : Rat)/21, [1, 1, 1, 2]),
   ((-67108864 : Rat)/21, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_2_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_2)) skA_E0_Q0_2 := by decide +kernel

def skA_E0_Q0_3 : SectorVector := [(-1,
  [((-192512 : Rat)/25, [0, 1, 1, 1, 1, 1]),
   ((262144 : Rat)/5, [0, 1, 1, 3]),
   ((-262144 : Rat)/5, [0, 1, 2, 2]),
   ((-786432 : Rat)/25, [0, 5]),
   ((-2228224 : Rat)/15, [1, 1, 1, 2]),
   ((524288 : Rat)/5, [1, 4]),
   ((8388608 : Rat)/15, [2, 3])]),
 (1,
  [((192512 : Rat)/25, [0, 1, 1, 1, 1, 1]),
   ((-262144 : Rat)/5, [0, 1, 1, 3]),
   ((262144 : Rat)/5, [0, 1, 2, 2]),
   ((786432 : Rat)/25, [0, 5]),
   ((-2228224 : Rat)/15, [1, 1, 1, 2]),
   ((524288 : Rat)/5, [1, 4]),
   ((8388608 : Rat)/15, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_3_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_3)) skA_E0_Q0_3 := by decide +kernel

def skA_E0_Q0_4 : SectorVector := [(-1,
  [((47104 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-65536, [0, 1, 1, 3]),
   (196608, [0, 1, 2, 2]),
   ((1572864 : Rat)/5, [0, 5]),
   (491520, [1, 1, 1, 2]),
   (-393216, [1, 4]),
   (-1572864, [2, 3])]),
 (1,
  [((-47104 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (65536, [0, 1, 1, 3]),
   (-196608, [0, 1, 2, 2]),
   ((-1572864 : Rat)/5, [0, 5]),
   (491520, [1, 1, 1, 2]),
   (-393216, [1, 4]),
   (-1572864, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_4_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_4)) skA_E0_Q0_4 := by decide +kernel

def skA_E0_Q0_5 : SectorVector := [(-1,
  [((1036288 : Rat)/135, [0, 1, 1, 1, 1, 1]),
   ((-360448 : Rat)/27, [0, 1, 1, 3]),
   ((2883584 : Rat)/9, [0, 1, 2, 2]),
   ((11534336 : Rat)/45, [0, 5]),
   ((14417920 : Rat)/27, [1, 1, 1, 2]),
   ((-5767168 : Rat)/9, [1, 4]),
   ((-11534336 : Rat)/27, [2, 3])]),
 (1,
  [((-1036288 : Rat)/135, [0, 1, 1, 1, 1, 1]),
   ((360448 : Rat)/27, [0, 1, 1, 3]),
   ((-2883584 : Rat)/9, [0, 1, 2, 2]),
   ((-11534336 : Rat)/45, [0, 5]),
   ((14417920 : Rat)/27, [1, 1, 1, 2]),
   ((-5767168 : Rat)/9, [1, 4]),
   ((-11534336 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_5_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_5)) skA_E0_Q0_5 := by decide +kernel

def skA_E0_Q0_6 : SectorVector := [(-1,
  [((-2315264 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((1556480 : Rat)/3, [0, 1, 1, 3]),
   (466944, [0, 1, 2, 2]),
   ((9961472 : Rat)/5, [0, 5]),
   ((4358144 : Rat)/3, [1, 1, 1, 2]),
   (-7471104, [1, 4]),
   ((-12451840 : Rat)/3, [2, 3])]),
 (1,
  [((2315264 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((-1556480 : Rat)/3, [0, 1, 1, 3]),
   (-466944, [0, 1, 2, 2]),
   ((-9961472 : Rat)/5, [0, 5]),
   ((4358144 : Rat)/3, [1, 1, 1, 2]),
   (-7471104, [1, 4]),
   ((-12451840 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_6_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_6)) skA_E0_Q0_6 := by decide +kernel

def skA_E0_Q0_7 : SectorVector := [(-1,
  [((28288 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((-212992 : Rat)/7, [0, 1, 1, 3]),
   ((-958464 : Rat)/7, [0, 1, 2, 2]),
   ((-2555904 : Rat)/35, [0, 5]),
   (-106496, [1, 1, 1, 2]),
   ((1916928 : Rat)/7, [1, 4]),
   ((3407872 : Rat)/7, [2, 3])]),
 (1,
  [((-28288 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((212992 : Rat)/7, [0, 1, 1, 3]),
   ((958464 : Rat)/7, [0, 1, 2, 2]),
   ((2555904 : Rat)/35, [0, 5]),
   (-106496, [1, 1, 1, 2]),
   ((1916928 : Rat)/7, [1, 4]),
   ((3407872 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_7_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_7)) skA_E0_Q0_7 := by decide +kernel

def skA_E0_Q0_8 : SectorVector := [(-1,
  [(-135168, [0, 1, 1, 1, 1, 1]),
   (983040, [0, 1, 1, 3]),
   (-491520, [0, 1, 2, 2]),
   (786432, [0, 5]),
   (-3932160, [1, 4])]),
 (1,
  [(135168, [0, 1, 1, 1, 1, 1]),
   (-983040, [0, 1, 1, 3]),
   (491520, [0, 1, 2, 2]),
   (-786432, [0, 5]),
   (-3932160, [1, 4])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_8_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_8)) skA_E0_Q0_8 := by decide +kernel

def skA_E0_Q0_9 : SectorVector := [(-1,
  [(135168, [0, 1, 1, 1, 1, 1]),
   (-983040, [0, 1, 1, 3]),
   (-983040, [0, 1, 2, 2]),
   (-786432, [0, 5]),
   (245760, [1, 1, 1, 2]),
   (3932160, [1, 4]),
   (3932160, [2, 3])]),
 (1,
  [(-135168, [0, 1, 1, 1, 1, 1]),
   (983040, [0, 1, 1, 3]),
   (983040, [0, 1, 2, 2]),
   (786432, [0, 5]),
   (245760, [1, 1, 1, 2]),
   (3932160, [1, 4]),
   (3932160, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_9_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_9)) skA_E0_Q0_9 := by decide +kernel

def skA_E0_Q0_10 : SectorVector := [(-1,
  [((687104 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-624640, [0, 1, 1, 3]),
   (-1998848, [0, 1, 2, 2]),
   ((-1499136 : Rat)/5, [0, 5]),
   ((999424 : Rat)/3, [1, 1, 1, 2]),
   (3997696, [1, 4]),
   ((9994240 : Rat)/3, [2, 3])]),
 (1,
  [((-687104 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (624640, [0, 1, 1, 3]),
   (1998848, [0, 1, 2, 2]),
   ((1499136 : Rat)/5, [0, 5]),
   ((999424 : Rat)/3, [1, 1, 1, 2]),
   (3997696, [1, 4]),
   ((9994240 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_10_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_10)) skA_E0_Q0_10 := by decide +kernel

def skA_E0_Q0_11 : SectorVector := [(-1,
  [(67584, [0, 1, 1, 1, 1, 1]),
   (-491520, [0, 1, 1, 3]),
   (-983040, [0, 1, 2, 2]),
   (-393216, [0, 5]),
   (163840, [1, 1, 1, 2]),
   (2621440, [2, 3])]),
 (1,
  [(-67584, [0, 1, 1, 1, 1, 1]),
   (491520, [0, 1, 1, 3]),
   (983040, [0, 1, 2, 2]),
   (393216, [0, 5]),
   (163840, [1, 1, 1, 2]),
   (2621440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_11_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_11)) skA_E0_Q0_11 := by decide +kernel

def skA_E0_Q0_12 : SectorVector := [(-1,
  [((415744 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-1306624, [0, 1, 1, 3]),
   (-222720, [0, 1, 2, 2]),
   ((-1069056 : Rat)/5, [0, 5]),
   (1098752, [1, 1, 1, 2]),
   (3563520, [1, 4]),
   (1900544, [2, 3])]),
 (1,
  [((-415744 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (1306624, [0, 1, 1, 3]),
   (222720, [0, 1, 2, 2]),
   ((1069056 : Rat)/5, [0, 5]),
   (1098752, [1, 1, 1, 2]),
   (3563520, [1, 4]),
   (1900544, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_12_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_12)) skA_E0_Q0_12 := by decide +kernel

def skA_E0_Q0_13 : SectorVector := [(-1,
  [(78848, [0, 1, 1, 1, 1, 1]),
   (-774400, [0, 1, 1, 3]),
   (-844800, [0, 1, 2, 2]),
   (-540672, [0, 5]),
   (1562880, [1, 1, 1, 2]),
   (1689600, [1, 4]),
   (1689600, [2, 3])]),
 (1,
  [(-78848, [0, 1, 1, 1, 1, 1]),
   (774400, [0, 1, 1, 3]),
   (844800, [0, 1, 2, 2]),
   (540672, [0, 5]),
   (1562880, [1, 1, 1, 2]),
   (1689600, [1, 4]),
   (1689600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_13_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_13)) skA_E0_Q0_13 := by decide +kernel

def skA_E0_Q0_14 : SectorVector := [(-1,
  [((57344 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((112640 : Rat)/81, [0, 1, 1, 3]),
   ((-409600 : Rat)/27, [0, 1, 2, 2]),
   ((-131072 : Rat)/27, [0, 5]),
   ((1515520 : Rat)/81, [1, 1, 1, 2]),
   ((819200 : Rat)/27, [1, 4]),
   ((-327680 : Rat)/81, [2, 3])]),
 (1,
  [((-57344 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-112640 : Rat)/81, [0, 1, 1, 3]),
   ((409600 : Rat)/27, [0, 1, 2, 2]),
   ((131072 : Rat)/27, [0, 5]),
   ((1515520 : Rat)/81, [1, 1, 1, 2]),
   ((819200 : Rat)/27, [1, 4]),
   ((-327680 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_14_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_14)) skA_E0_Q0_14 := by decide +kernel

def skA_E0_Q0_15 : SectorVector := [(-1,
  [((-498176 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((7828480 : Rat)/9, [0, 1, 1, 3]),
   ((3558400 : Rat)/3, [0, 1, 2, 2]),
   ((1138688 : Rat)/3, [0, 5]),
   ((-13166080 : Rat)/9, [1, 1, 1, 2]),
   ((-7116800 : Rat)/3, [1, 4]),
   ((-22773760 : Rat)/9, [2, 3])]),
 (1,
  [((498176 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-7828480 : Rat)/9, [0, 1, 1, 3]),
   ((-3558400 : Rat)/3, [0, 1, 2, 2]),
   ((-1138688 : Rat)/3, [0, 5]),
   ((-13166080 : Rat)/9, [1, 1, 1, 2]),
   ((-7116800 : Rat)/3, [1, 4]),
   ((-22773760 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_15_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_15)) skA_E0_Q0_15 := by decide +kernel

def skA_E0_Q0_16 : SectorVector := [(-1,
  [(4096, [0, 1, 1, 1, 1, 1]),
   (87040, [0, 1, 1, 3]),
   (-11520, [0, 1, 2, 2]),
   (24576, [0, 5]),
   (-56320, [1, 1, 1, 2]),
   (-92160, [1, 4]),
   (-40960, [2, 3])]),
 (1,
  [(-4096, [0, 1, 1, 1, 1, 1]),
   (-87040, [0, 1, 1, 3]),
   (11520, [0, 1, 2, 2]),
   (-24576, [0, 5]),
   (-56320, [1, 1, 1, 2]),
   (-92160, [1, 4]),
   (-40960, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_16_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_16)) skA_E0_Q0_16 := by decide +kernel

def skA_E0_Q0_17 : SectorVector := [(-1,
  [((106496 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((565760 : Rat)/3, [0, 1, 1, 3]),
   (99840, [0, 1, 2, 2]),
   (212992, [0, 5]),
   ((-2928640 : Rat)/3, [1, 1, 1, 2]),
   (-1597440, [1, 4]),
   ((-532480 : Rat)/3, [2, 3])]),
 (1,
  [((-106496 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-565760 : Rat)/3, [0, 1, 1, 3]),
   (-99840, [0, 1, 2, 2]),
   (-212992, [0, 5]),
   ((-2928640 : Rat)/3, [1, 1, 1, 2]),
   (-1597440, [1, 4]),
   ((-532480 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_17_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_17)) skA_E0_Q0_17 := by decide +kernel

def skA_E0_Q0_18 : SectorVector := [(-1,
  [(-6144, [0, 1, 1, 1, 1, 1]),
   (-130560, [0, 1, 1, 3]),
   (-69120, [0, 1, 2, 2]),
   (-36864, [0, 5]),
   (253440, [1, 1, 1, 2]),
   (276480, [1, 4]),
   (184320, [2, 3])]),
 (1,
  [(6144, [0, 1, 1, 1, 1, 1]),
   (130560, [0, 1, 1, 3]),
   (69120, [0, 1, 2, 2]),
   (36864, [0, 5]),
   (253440, [1, 1, 1, 2]),
   (276480, [1, 4]),
   (184320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_18_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_18)) skA_E0_Q0_18 := by decide +kernel

def skA_E0_Q0_19 : SectorVector := [(-1,
  [(-57344, [0, 1, 1, 1, 1, 1]),
   (-761600, [0, 1, 1, 3]),
   (-1290240, [0, 1, 2, 2]),
   (-344064, [0, 5]),
   (3153920, [1, 1, 1, 2]),
   (2580480, [1, 4]),
   (1433600, [2, 3])]),
 (1,
  [(57344, [0, 1, 1, 1, 1, 1]),
   (761600, [0, 1, 1, 3]),
   (1290240, [0, 1, 2, 2]),
   (344064, [0, 5]),
   (3153920, [1, 1, 1, 2]),
   (2580480, [1, 4]),
   (1433600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_19_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_19)) skA_E0_Q0_19 := by decide +kernel

def skA_E0_Q0_20 : SectorVector := [(-1,
  [(-74752, [0, 1, 1, 1, 1, 1]),
   (-1588480, [0, 1, 1, 3]),
   (-1681920, [0, 1, 2, 2]),
   (-448512, [0, 5]),
   (4111360, [1, 1, 1, 2]),
   (1681920, [1, 4]),
   (2990080, [2, 3])]),
 (1,
  [(74752, [0, 1, 1, 1, 1, 1]),
   (1588480, [0, 1, 1, 3]),
   (1681920, [0, 1, 2, 2]),
   (448512, [0, 5]),
   (4111360, [1, 1, 1, 2]),
   (1681920, [1, 4]),
   (2990080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_20_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_20)) skA_E0_Q0_20 := by decide +kernel

def skA_E0_Q0_21 : SectorVector := [(-1,
  [((-989184 : Rat)/25, [0, 1, 1, 1, 1, 1]),
   ((-4204032 : Rat)/5, [0, 1, 1, 3]),
   ((-4451328 : Rat)/5, [0, 1, 2, 2]),
   ((1483776 : Rat)/25, [0, 5]),
   ((10881024 : Rat)/5, [1, 1, 1, 2]),
   ((8902656 : Rat)/5, [1, 4]),
   ((7913472 : Rat)/5, [2, 3])]),
 (1,
  [((989184 : Rat)/25, [0, 1, 1, 1, 1, 1]),
   ((4204032 : Rat)/5, [0, 1, 1, 3]),
   ((4451328 : Rat)/5, [0, 1, 2, 2]),
   ((-1483776 : Rat)/25, [0, 5]),
   ((10881024 : Rat)/5, [1, 1, 1, 2]),
   ((8902656 : Rat)/5, [1, 4]),
   ((7913472 : Rat)/5, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_21_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_21)) skA_E0_Q0_21 := by decide +kernel

def skA_E0_Q0_22 : SectorVector := [(-1,
  [(98304, [0, 1, 1, 1, 1, 1]), (307200, [0, 1, 1, 3]), (-107520, [0, 1, 2, 2]), (98304, [0, 5]), (-860160, [1, 4])]),
 (1,
  [(-98304, [0, 1, 1, 1, 1, 1]), (-307200, [0, 1, 1, 3]), (107520, [0, 1, 2, 2]), (-98304, [0, 5]), (-860160, [1, 4])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_22_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_22)) skA_E0_Q0_22 := by decide +kernel

def skA_E0_Q0_23 : SectorVector := [(-1,
  [((-1013760 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-5068800 : Rat)/7, [0, 1, 1, 3]),
   (-79200, [0, 1, 2, 2]),
   ((-1013760 : Rat)/7, [0, 5]),
   ((8448000 : Rat)/7, [1, 1, 1, 2]),
   (1267200, [1, 4]),
   ((3379200 : Rat)/7, [2, 3])]),
 (1,
  [((1013760 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((5068800 : Rat)/7, [0, 1, 1, 3]),
   (79200, [0, 1, 2, 2]),
   ((1013760 : Rat)/7, [0, 5]),
   ((8448000 : Rat)/7, [1, 1, 1, 2]),
   (1267200, [1, 4]),
   ((3379200 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_23_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_23)) skA_E0_Q0_23 := by decide +kernel

def skA_E0_Q0_24 : SectorVector := [(-1,
  [(-319488, [0, 1, 1, 1, 1, 1]),
   (-998400, [0, 1, 1, 3]),
   (-698880, [0, 1, 2, 2]),
   (-319488, [0, 5]),
   (3993600, [1, 1, 1, 2]),
   (2795520, [1, 4]),
   (998400, [2, 3])]),
 (1,
  [(319488, [0, 1, 1, 1, 1, 1]),
   (998400, [0, 1, 1, 3]),
   (698880, [0, 1, 2, 2]),
   (319488, [0, 5]),
   (3993600, [1, 1, 1, 2]),
   (2795520, [1, 4]),
   (998400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_24_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_24)) skA_E0_Q0_24 := by decide +kernel

def skA_E0_Q0_25 : SectorVector := [(-1,
  [((-1603584 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-1603584, [0, 1, 1, 3]),
   (-701568, [0, 1, 2, 2]),
   ((-601344 : Rat)/5, [0, 5]),
   (4008960, [1, 1, 1, 2]),
   (1403136, [1, 4]),
   (1603584, [2, 3])]),
 (1,
  [((1603584 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (1603584, [0, 1, 1, 3]),
   (701568, [0, 1, 2, 2]),
   ((601344 : Rat)/5, [0, 5]),
   (4008960, [1, 1, 1, 2]),
   (1403136, [1, 4]),
   (1603584, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_25_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_25)) skA_E0_Q0_25 := by decide +kernel

def skA_E0_Q0_26 : SectorVector := [(-1,
  [((-507904 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-126976, [0, 1, 1, 3]),
   (-444416, [0, 1, 2, 2]),
   ((-190464 : Rat)/5, [0, 5]),
   ((5079040 : Rat)/3, [1, 1, 1, 2]),
   (888832, [1, 4]),
   ((507904 : Rat)/3, [2, 3])]),
 (1,
  [((507904 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (126976, [0, 1, 1, 3]),
   (444416, [0, 1, 2, 2]),
   ((190464 : Rat)/5, [0, 5]),
   ((5079040 : Rat)/3, [1, 1, 1, 2]),
   (888832, [1, 4]),
   ((507904 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_26_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_26)) skA_E0_Q0_26 := by decide +kernel

def skA_E0_Q0_27 : SectorVector := [(-1,
  [(-86016, [0, 1, 1, 1, 1, 1]),
   (-268800, [0, 1, 1, 3]),
   (-376320, [0, 1, 2, 2]),
   (-86016, [0, 5]),
   (1433600, [1, 1, 1, 2]),
   (358400, [2, 3])]),
 (1,
  [(86016, [0, 1, 1, 1, 1, 1]),
   (268800, [0, 1, 1, 3]),
   (376320, [0, 1, 2, 2]),
   (86016, [0, 5]),
   (1433600, [1, 1, 1, 2]),
   (358400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_27_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_27)) skA_E0_Q0_27 := by decide +kernel

def skA_E0_Q0_28 : SectorVector := [(-1,
  [((1783296 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((8916480 : Rat)/11, [0, 1, 1, 3]),
   ((7801920 : Rat)/11, [0, 1, 2, 2]),
   ((1783296 : Rat)/11, [0, 5]),
   ((-29721600 : Rat)/11, [1, 1, 1, 2]),
   ((-15603840 : Rat)/11, [1, 4]),
   ((-11888640 : Rat)/11, [2, 3])]),
 (1,
  [((-1783296 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((-8916480 : Rat)/11, [0, 1, 1, 3]),
   ((-7801920 : Rat)/11, [0, 1, 2, 2]),
   ((-1783296 : Rat)/11, [0, 5]),
   ((-29721600 : Rat)/11, [1, 1, 1, 2]),
   ((-15603840 : Rat)/11, [1, 4]),
   ((-11888640 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_28_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_28)) skA_E0_Q0_28 := by decide +kernel

def skA_E0_Q0_29 : SectorVector := [(-1,
  [((131072 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((65536 : Rat)/3, [0, 1, 1, 3]),
   (-2048, [0, 1, 2, 2]),
   ((16384 : Rat)/5, [0, 5]),
   ((131072 : Rat)/3, [1, 1, 1, 2]),
   (-32768, [1, 4]),
   ((32768 : Rat)/3, [2, 3])]),
 (1,
  [((-131072 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((-65536 : Rat)/3, [0, 1, 1, 3]),
   (2048, [0, 1, 2, 2]),
   ((-16384 : Rat)/5, [0, 5]),
   ((131072 : Rat)/3, [1, 1, 1, 2]),
   (-32768, [1, 4]),
   ((32768 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_29_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_29)) skA_E0_Q0_29 := by decide +kernel

def skA_E0_Q0_30 : SectorVector := [(-1,
  [((-204800 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-512000 : Rat)/3, [0, 1, 1, 3]),
   (16000, [0, 1, 2, 2]),
   (-25600, [0, 5]),
   ((512000 : Rat)/3, [1, 1, 1, 2]),
   (256000, [1, 4]),
   ((128000 : Rat)/3, [2, 3])]),
 (1,
  [((204800 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((512000 : Rat)/3, [0, 1, 1, 3]),
   (-16000, [0, 1, 2, 2]),
   (25600, [0, 5]),
   ((512000 : Rat)/3, [1, 1, 1, 2]),
   (256000, [1, 4]),
   ((128000 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_30_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_30)) skA_E0_Q0_30 := by decide +kernel

def skA_E0_Q0_31 : SectorVector := [(-1,
  [((-704512 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-220160, [0, 1, 1, 3]),
   (-33024, [0, 1, 2, 2]),
   ((-99072 : Rat)/5, [0, 5]),
   (704512, [1, 1, 1, 2]),
   (528384, [1, 4]),
   (110080, [2, 3])]),
 (1,
  [((704512 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (220160, [0, 1, 1, 3]),
   (33024, [0, 1, 2, 2]),
   ((99072 : Rat)/5, [0, 5]),
   (704512, [1, 1, 1, 2]),
   (528384, [1, 4]),
   (110080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_31_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_31)) skA_E0_Q0_31 := by decide +kernel

def skA_E0_Q0_32 : SectorVector := [(-1,
  [(-61440, [0, 1, 1, 1, 1, 1]),
   (-153600, [0, 1, 1, 3]),
   (-14400, [0, 1, 2, 2]),
   (-23040, [0, 5]),
   (307200, [1, 1, 1, 2]),
   (76800, [2, 3])]),
 (1,
  [(61440, [0, 1, 1, 1, 1, 1]),
   (153600, [0, 1, 1, 3]),
   (14400, [0, 1, 2, 2]),
   (23040, [0, 5]),
   (307200, [1, 1, 1, 2]),
   (76800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_32_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_32)) skA_E0_Q0_32 := by decide +kernel

def skA_E0_Q0_33 : SectorVector := [(-1,
  [(-65536, [0, 1, 1, 1, 1, 1]),
   (-40960, [0, 1, 1, 3]),
   (-61440, [0, 1, 2, 2]),
   (-24576, [0, 5]),
   (491520, [1, 1, 1, 2]),
   (122880, [1, 4]),
   (30720, [2, 3])]),
 (1,
  [(65536, [0, 1, 1, 1, 1, 1]),
   (40960, [0, 1, 1, 3]),
   (61440, [0, 1, 2, 2]),
   (24576, [0, 5]),
   (491520, [1, 1, 1, 2]),
   (122880, [1, 4]),
   (30720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_33_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_33)) skA_E0_Q0_33 := by decide +kernel

def skA_E0_Q0_34 : SectorVector := [(-1,
  [((423936 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (211968, [0, 1, 1, 3]),
   (79488, [0, 1, 2, 2]),
   ((158976 : Rat)/5, [0, 5]),
   (-635904, [1, 1, 1, 2]),
   (-317952, [1, 4]),
   (-158976, [2, 3])]),
 (1,
  [((-423936 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-211968, [0, 1, 1, 3]),
   (-79488, [0, 1, 2, 2]),
   ((-158976 : Rat)/5, [0, 5]),
   (-635904, [1, 1, 1, 2]),
   (-317952, [1, 4]),
   (-158976, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_34_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_34)) skA_E0_Q0_34 := by decide +kernel

def skA_E0_Q0_35 : SectorVector := [(-1,
  [((-180224 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((225280 : Rat)/81, [0, 1, 1, 3]),
   ((-112640 : Rat)/27, [0, 1, 2, 2]),
   ((-22528 : Rat)/27, [0, 5]),
   ((1802240 : Rat)/81, [1, 1, 1, 2]),
   ((225280 : Rat)/27, [1, 4]),
   ((-225280 : Rat)/81, [2, 3])]),
 (1,
  [((180224 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-225280 : Rat)/81, [0, 1, 1, 3]),
   ((112640 : Rat)/27, [0, 1, 2, 2]),
   ((22528 : Rat)/27, [0, 5]),
   ((1802240 : Rat)/81, [1, 1, 1, 2]),
   ((225280 : Rat)/27, [1, 4]),
   ((-225280 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_35_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_35)) skA_E0_Q0_35 := by decide +kernel

def skA_E0_Q0_36 : SectorVector := [(-1,
  [((-151552 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-236800 : Rat)/9, [0, 1, 1, 3]),
   ((-94720 : Rat)/3, [0, 1, 2, 2]),
   ((-18944 : Rat)/3, [0, 5]),
   ((1515520 : Rat)/9, [1, 1, 1, 2]),
   ((189440 : Rat)/3, [1, 4]),
   ((236800 : Rat)/9, [2, 3])]),
 (1,
  [((151552 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((236800 : Rat)/9, [0, 1, 1, 3]),
   ((94720 : Rat)/3, [0, 1, 2, 2]),
   ((18944 : Rat)/3, [0, 5]),
   ((1515520 : Rat)/9, [1, 1, 1, 2]),
   ((189440 : Rat)/3, [1, 4]),
   ((236800 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_36_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_36)) skA_E0_Q0_36 := by decide +kernel

def skA_E0_Q0_37 : SectorVector := [(-1,
  [(-58368, [0, 1, 1, 1, 1, 1]),
   (-145920, [0, 1, 1, 3]),
   (-109440, [0, 1, 2, 2]),
   (-21888, [0, 5]),
   (583680, [1, 1, 1, 2]),
   (109440, [1, 4]),
   (145920, [2, 3])]),
 (1,
  [(58368, [0, 1, 1, 1, 1, 1]),
   (145920, [0, 1, 1, 3]),
   (109440, [0, 1, 2, 2]),
   (21888, [0, 5]),
   (583680, [1, 1, 1, 2]),
   (109440, [1, 4]),
   (145920, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_37_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_37)) skA_E0_Q0_37 := by decide +kernel

def skA_E0_Q0_38 : SectorVector := [(-1,
  [((-380928 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-190464, [0, 1, 1, 3]),
   (-142848, [0, 1, 2, 2]),
   ((-53568 : Rat)/5, [0, 5]),
   (761856, [1, 1, 1, 2]),
   (285696, [1, 4]),
   (190464, [2, 3])]),
 (1,
  [((380928 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (190464, [0, 1, 1, 3]),
   (142848, [0, 1, 2, 2]),
   ((53568 : Rat)/5, [0, 5]),
   (761856, [1, 1, 1, 2]),
   (285696, [1, 4]),
   (190464, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_38_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_38)) skA_E0_Q0_38 := by decide +kernel

def skA_E0_Q0_39 : SectorVector := [(-1,
  [((-121856 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-304640 : Rat)/3, [0, 1, 1, 3]),
   (-76160, [0, 1, 2, 2]),
   (-15232, [0, 5]),
   ((1218560 : Rat)/3, [1, 1, 1, 2]),
   (152320, [1, 4]),
   ((304640 : Rat)/3, [2, 3])]),
 (1,
  [((121856 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((304640 : Rat)/3, [0, 1, 1, 3]),
   (76160, [0, 1, 2, 2]),
   (15232, [0, 5]),
   ((1218560 : Rat)/3, [1, 1, 1, 2]),
   (152320, [1, 4]),
   ((304640 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q0_39_cert : VectorCertificate (Tpow 0 (aLeft false (6 : ℤ) skM_E0_39)) skA_E0_Q0_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_0_join : VectorCertificate ([skA_E0_Q0_0, skA_E0_Q0_1, skA_E0_Q0_2, skA_E0_Q0_3, skA_E0_Q0_4, skA_E0_Q0_5, skA_E0_Q0_6, skA_E0_Q0_7, skA_E0_Q0_8, skA_E0_Q0_9, skA_E0_Q0_10, skA_E0_Q0_11, skA_E0_Q0_12, skA_E0_Q0_13, skA_E0_Q0_14, skA_E0_Q0_15, skA_E0_Q0_16, skA_E0_Q0_17, skA_E0_Q0_18, skA_E0_Q0_19, skA_E0_Q0_20, skA_E0_Q0_21, skA_E0_Q0_22, skA_E0_Q0_23, skA_E0_Q0_24, skA_E0_Q0_25, skA_E0_Q0_26, skA_E0_Q0_27, skA_E0_Q0_28, skA_E0_Q0_29, skA_E0_Q0_30, skA_E0_Q0_31, skA_E0_Q0_32, skA_E0_Q0_33, skA_E0_Q0_34, skA_E0_Q0_35, skA_E0_Q0_36, skA_E0_Q0_37, skA_E0_Q0_38, skA_E0_Q0_39] : List SectorVector).flatten skQ_E0_0 := by decide +kernel

theorem skQ_E0_0_val : evaluate skQ_E0_0 = evaluate (OrbSgl.vTerm false skY_E0 0 0) :=
  vTerm_of_chunks false skY_E0 0 0 (6 : ℤ) (by norm_num) skM_E0 [skA_E0_Q0_0, skA_E0_Q0_1, skA_E0_Q0_2, skA_E0_Q0_3, skA_E0_Q0_4, skA_E0_Q0_5, skA_E0_Q0_6, skA_E0_Q0_7, skA_E0_Q0_8, skA_E0_Q0_9, skA_E0_Q0_10, skA_E0_Q0_11, skA_E0_Q0_12, skA_E0_Q0_13, skA_E0_Q0_14, skA_E0_Q0_15, skA_E0_Q0_16, skA_E0_Q0_17, skA_E0_Q0_18, skA_E0_Q0_19, skA_E0_Q0_20, skA_E0_Q0_21, skA_E0_Q0_22, skA_E0_Q0_23, skA_E0_Q0_24, skA_E0_Q0_25, skA_E0_Q0_26, skA_E0_Q0_27, skA_E0_Q0_28, skA_E0_Q0_29, skA_E0_Q0_30, skA_E0_Q0_31, skA_E0_Q0_32, skA_E0_Q0_33, skA_E0_Q0_34, skA_E0_Q0_35, skA_E0_Q0_36, skA_E0_Q0_37, skA_E0_Q0_38, skA_E0_Q0_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q0_0_cert (List.Forall₂.cons skA_E0_Q0_1_cert (List.Forall₂.cons skA_E0_Q0_2_cert (List.Forall₂.cons skA_E0_Q0_3_cert (List.Forall₂.cons skA_E0_Q0_4_cert (List.Forall₂.cons skA_E0_Q0_5_cert (List.Forall₂.cons skA_E0_Q0_6_cert (List.Forall₂.cons skA_E0_Q0_7_cert (List.Forall₂.cons skA_E0_Q0_8_cert (List.Forall₂.cons skA_E0_Q0_9_cert (List.Forall₂.cons skA_E0_Q0_10_cert (List.Forall₂.cons skA_E0_Q0_11_cert (List.Forall₂.cons skA_E0_Q0_12_cert (List.Forall₂.cons skA_E0_Q0_13_cert (List.Forall₂.cons skA_E0_Q0_14_cert (List.Forall₂.cons skA_E0_Q0_15_cert (List.Forall₂.cons skA_E0_Q0_16_cert (List.Forall₂.cons skA_E0_Q0_17_cert (List.Forall₂.cons skA_E0_Q0_18_cert (List.Forall₂.cons skA_E0_Q0_19_cert (List.Forall₂.cons skA_E0_Q0_20_cert (List.Forall₂.cons skA_E0_Q0_21_cert (List.Forall₂.cons skA_E0_Q0_22_cert (List.Forall₂.cons skA_E0_Q0_23_cert (List.Forall₂.cons skA_E0_Q0_24_cert (List.Forall₂.cons skA_E0_Q0_25_cert (List.Forall₂.cons skA_E0_Q0_26_cert (List.Forall₂.cons skA_E0_Q0_27_cert (List.Forall₂.cons skA_E0_Q0_28_cert (List.Forall₂.cons skA_E0_Q0_29_cert (List.Forall₂.cons skA_E0_Q0_30_cert (List.Forall₂.cons skA_E0_Q0_31_cert (List.Forall₂.cons skA_E0_Q0_32_cert (List.Forall₂.cons skA_E0_Q0_33_cert (List.Forall₂.cons skA_E0_Q0_34_cert (List.Forall₂.cons skA_E0_Q0_35_cert (List.Forall₂.cons skA_E0_Q0_36_cert (List.Forall₂.cons skA_E0_Q0_37_cert (List.Forall₂.cons skA_E0_Q0_38_cert (List.Forall₂.cons skA_E0_Q0_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_0 skQ_E0_0_join

def skA_E0_Q1_0 : SectorVector := [(1,
  [((318767104 : Rat)/31185, [0, 1, 1, 1, 1, 1]),
   ((3489660928 : Rat)/31185, [0, 1, 1, 3]),
   ((-268435456 : Rat)/2079, [0, 1, 2, 2]),
   ((-1073741824 : Rat)/10395, [0, 5]),
   ((-1946157056 : Rat)/31185, [1, 1, 1, 2]),
   ((2147483648 : Rat)/10395, [1, 4]),
   ((-8589934592 : Rat)/31185, [2, 3])]),
 (-1,
  [((-318767104 : Rat)/31185, [0, 1, 1, 1, 1, 1]),
   ((-3489660928 : Rat)/31185, [0, 1, 1, 3]),
   ((268435456 : Rat)/2079, [0, 1, 2, 2]),
   ((1073741824 : Rat)/10395, [0, 5]),
   ((-1946157056 : Rat)/31185, [1, 1, 1, 2]),
   ((2147483648 : Rat)/10395, [1, 4]),
   ((-8589934592 : Rat)/31185, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_0_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_0)) skA_E0_Q1_0 := by decide +kernel

def skA_E0_Q1_1 : SectorVector := [(1,
  [((-13631488 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((71303168 : Rat)/81, [0, 1, 1, 3]),
   ((-16777216 : Rat)/27, [0, 1, 2, 2]),
   ((-33554432 : Rat)/27, [0, 5]),
   ((146800640 : Rat)/81, [1, 1, 1, 2]),
   ((-46137344 : Rat)/27, [1, 4]),
   ((-381681664 : Rat)/81, [2, 3])]),
 (-1,
  [((13631488 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-71303168 : Rat)/81, [0, 1, 1, 3]),
   ((16777216 : Rat)/27, [0, 1, 2, 2]),
   ((33554432 : Rat)/27, [0, 5]),
   ((146800640 : Rat)/81, [1, 1, 1, 2]),
   ((-46137344 : Rat)/27, [1, 4]),
   ((-381681664 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_1_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_1)) skA_E0_Q1_1 := by decide +kernel

def skA_E0_Q1_2 : SectorVector := [(1,
  [((-3145728 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((8388608 : Rat)/7, [0, 1, 1, 3]),
   ((4194304 : Rat)/7, [0, 1, 2, 2]),
   ((-33554432 : Rat)/7, [0, 5]),
   ((20971520 : Rat)/7, [1, 1, 1, 2]),
   ((-67108864 : Rat)/7, [1, 4]),
   ((-16777216 : Rat)/7, [2, 3])]),
 (-1,
  [((3145728 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-8388608 : Rat)/7, [0, 1, 1, 3]),
   ((-4194304 : Rat)/7, [0, 1, 2, 2]),
   ((33554432 : Rat)/7, [0, 5]),
   ((20971520 : Rat)/7, [1, 1, 1, 2]),
   ((-67108864 : Rat)/7, [1, 4]),
   ((-16777216 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_2_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_2)) skA_E0_Q1_2 := by decide +kernel

def skA_E0_Q1_3 : SectorVector := [(1,
  [((32768 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((-262144 : Rat)/15, [0, 1, 1, 3]),
   (262144, [0, 1, 2, 2]),
   ((2097152 : Rat)/5, [0, 5]),
   ((-9306112 : Rat)/15, [1, 1, 1, 2]),
   ((6291456 : Rat)/5, [1, 4]),
   ((27262976 : Rat)/15, [2, 3])]),
 (-1,
  [((-32768 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((262144 : Rat)/15, [0, 1, 1, 3]),
   (-262144, [0, 1, 2, 2]),
   ((-2097152 : Rat)/5, [0, 5]),
   ((-9306112 : Rat)/15, [1, 1, 1, 2]),
   ((6291456 : Rat)/5, [1, 4]),
   ((27262976 : Rat)/15, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_3_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_3)) skA_E0_Q1_3 := by decide +kernel

def skA_E0_Q1_4 : SectorVector := [(1,
  [(155648, [0, 1, 1, 1, 1, 1]),
   (-901120, [0, 1, 1, 3]),
   (-638976, [0, 1, 2, 2]),
   (-786432, [0, 5]),
   (1212416, [1, 1, 1, 2]),
   (-4718592, [1, 4]),
   (-4194304, [2, 3])]),
 (-1,
  [(-155648, [0, 1, 1, 1, 1, 1]),
   (901120, [0, 1, 1, 3]),
   (638976, [0, 1, 2, 2]),
   (786432, [0, 5]),
   (1212416, [1, 1, 1, 2]),
   (-4718592, [1, 4]),
   (-4194304, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_4_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_4)) skA_E0_Q1_4 := by decide +kernel

def skA_E0_Q1_5 : SectorVector := [(1,
  [((3424256 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-1441792 : Rat)/27, [0, 1, 1, 3]),
   ((-10092544 : Rat)/9, [0, 1, 2, 2]),
   ((-11534336 : Rat)/9, [0, 5]),
   ((30998528 : Rat)/27, [1, 1, 1, 2]),
   ((-28835840 : Rat)/9, [1, 4]),
   ((-144179200 : Rat)/27, [2, 3])]),
 (-1,
  [((-3424256 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((1441792 : Rat)/27, [0, 1, 1, 3]),
   ((10092544 : Rat)/9, [0, 1, 2, 2]),
   ((11534336 : Rat)/9, [0, 5]),
   ((30998528 : Rat)/27, [1, 1, 1, 2]),
   ((-28835840 : Rat)/9, [1, 4]),
   ((-144179200 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_5_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_5)) skA_E0_Q1_5 := by decide +kernel

def skA_E0_Q1_6 : SectorVector := [(1,
  [(1712128, [0, 1, 1, 1, 1, 1]),
   (-7471104, [0, 1, 1, 3]),
   (-2490368, [0, 1, 2, 2]),
   (-9961472, [0, 5]),
   (1867776, [1, 1, 1, 2]),
   (-38600704, [1, 4]),
   (-11206656, [2, 3])]),
 (-1,
  [(-1712128, [0, 1, 1, 1, 1, 1]),
   (7471104, [0, 1, 1, 3]),
   (2490368, [0, 1, 2, 2]),
   (9961472, [0, 5]),
   (1867776, [1, 1, 1, 2]),
   (-38600704, [1, 4]),
   (-11206656, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_6_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_6)) skA_E0_Q1_6 := by decide +kernel

def skA_E0_Q1_7 : SectorVector := [(1,
  [((-439296 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((3194880 : Rat)/7, [0, 1, 1, 3]),
   ((3194880 : Rat)/7, [0, 1, 2, 2]),
   ((2555904 : Rat)/7, [0, 5]),
   ((798720 : Rat)/7, [1, 1, 1, 2]),
   ((12779520 : Rat)/7, [1, 4]),
   ((12779520 : Rat)/7, [2, 3])]),
 (-1,
  [((439296 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-3194880 : Rat)/7, [0, 1, 1, 3]),
   ((-3194880 : Rat)/7, [0, 1, 2, 2]),
   ((-2555904 : Rat)/7, [0, 5]),
   ((798720 : Rat)/7, [1, 1, 1, 2]),
   ((12779520 : Rat)/7, [1, 4]),
   ((12779520 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_7_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_7)) skA_E0_Q1_7 := by decide +kernel

def skA_E0_Q1_8 : SectorVector := [(1,
  [(593920, [0, 1, 1, 1, 1, 1]),
   (-5242880, [0, 1, 1, 3]),
   (983040, [0, 1, 2, 2]),
   (-3932160, [0, 5]),
   (2375680, [1, 1, 1, 2]),
   (-23592960, [1, 4]),
   (-1310720, [2, 3])]),
 (-1,
  [(-593920, [0, 1, 1, 1, 1, 1]),
   (5242880, [0, 1, 1, 3]),
   (-983040, [0, 1, 2, 2]),
   (3932160, [0, 5]),
   (2375680, [1, 1, 1, 2]),
   (-23592960, [1, 4]),
   (-1310720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_8_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_8)) skA_E0_Q1_8 := by decide +kernel

def skA_E0_Q1_9 : SectorVector := [(1,
  [(-593920, [0, 1, 1, 1, 1, 1]),
   (7454720, [0, 1, 1, 3]),
   (4177920, [0, 1, 2, 2]),
   (3932160, [0, 5]),
   (6471680, [1, 1, 1, 2]),
   (23592960, [1, 4]),
   (13107200, [2, 3])]),
 (-1,
  [(593920, [0, 1, 1, 1, 1, 1]),
   (-7454720, [0, 1, 1, 3]),
   (-4177920, [0, 1, 2, 2]),
   (-3932160, [0, 5]),
   (6471680, [1, 1, 1, 2]),
   (23592960, [1, 4]),
   (13107200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_9_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_9)) skA_E0_Q1_9 := by decide +kernel

def skA_E0_Q1_10 : SectorVector := [(1,
  [((-1811456 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((18989056 : Rat)/3, [0, 1, 1, 3]),
   (6995968, [0, 1, 2, 2]),
   (3997696, [0, 5]),
   ((28733440 : Rat)/3, [1, 1, 1, 2]),
   (17989632, [1, 4]),
   ((57966592 : Rat)/3, [2, 3])]),
 (-1,
  [((1811456 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-18989056 : Rat)/3, [0, 1, 1, 3]),
   (-6995968, [0, 1, 2, 2]),
   (-3997696, [0, 5]),
   ((28733440 : Rat)/3, [1, 1, 1, 2]),
   (17989632, [1, 4]),
   ((57966592 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_10_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_10)) skA_E0_Q1_10 := by decide +kernel

def skA_E0_Q1_11 : SectorVector := [(1,
  [(-296960, [0, 1, 1, 1, 1, 1]),
   (4096000, [0, 1, 1, 3]),
   (3440640, [0, 1, 2, 2]),
   (4710400, [1, 1, 1, 2]),
   (7864320, [1, 4]),
   (10485760, [2, 3])]),
 (-1,
  [(296960, [0, 1, 1, 1, 1, 1]),
   (-4096000, [0, 1, 1, 3]),
   (-3440640, [0, 1, 2, 2]),
   (4710400, [1, 1, 1, 2]),
   (7864320, [1, 4]),
   (10485760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_11_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_11)) skA_E0_Q1_11 := by decide +kernel

def skA_E0_Q1_12 : SectorVector := [(1,
  [(118784, [0, 1, 1, 1, 1, 1]),
   (6711296, [0, 1, 1, 3]),
   (2316288, [0, 1, 2, 2]),
   (2850816, [0, 5]),
   (8314880, [1, 1, 1, 2]),
   (19955712, [1, 4]),
   (6176768, [2, 3])]),
 (-1,
  [(-118784, [0, 1, 1, 1, 1, 1]),
   (-6711296, [0, 1, 1, 3]),
   (-2316288, [0, 1, 2, 2]),
   (-2850816, [0, 5]),
   (8314880, [1, 1, 1, 2]),
   (19955712, [1, 4]),
   (6176768, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_12_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_12)) skA_E0_Q1_12 := by decide +kernel

def skA_E0_Q1_13 : SectorVector := [(1,
  [(112640, [0, 1, 1, 1, 1, 1]),
   (5603840, [0, 1, 1, 3]),
   (4139520, [0, 1, 2, 2]),
   (1351680, [0, 5]),
   (11601920, [1, 1, 1, 2]),
   (11151360, [1, 4]),
   (8222720, [2, 3])]),
 (-1,
  [(-112640, [0, 1, 1, 1, 1, 1]),
   (-5603840, [0, 1, 1, 3]),
   (-4139520, [0, 1, 2, 2]),
   (-1351680, [0, 5]),
   (11601920, [1, 1, 1, 2]),
   (11151360, [1, 4]),
   (8222720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_13_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_13)) skA_E0_Q1_13 := by decide +kernel

def skA_E0_Q1_14 : SectorVector := [(1,
  [((81920 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((2293760 : Rat)/81, [0, 1, 1, 3]),
   ((1556480 : Rat)/27, [0, 1, 2, 2]),
   ((655360 : Rat)/27, [0, 5]),
   ((11141120 : Rat)/81, [1, 1, 1, 2]),
   ((901120 : Rat)/27, [1, 4]),
   ((7454720 : Rat)/81, [2, 3])]),
 (-1,
  [((-81920 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-2293760 : Rat)/81, [0, 1, 1, 3]),
   ((-1556480 : Rat)/27, [0, 1, 2, 2]),
   ((-655360 : Rat)/27, [0, 5]),
   ((11141120 : Rat)/81, [1, 1, 1, 2]),
   ((901120 : Rat)/27, [1, 4]),
   ((7454720 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_14_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_14)) skA_E0_Q1_14 := by decide +kernel

def skA_E0_Q1_15 : SectorVector := [(1,
  [((-711680 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-51952640 : Rat)/9, [0, 1, 1, 3]),
   ((-13521920 : Rat)/3, [0, 1, 2, 2]),
   ((-5693440 : Rat)/3, [0, 5]),
   ((-96788480 : Rat)/9, [1, 1, 1, 2]),
   ((-39854080 : Rat)/3, [1, 4]),
   ((-96788480 : Rat)/9, [2, 3])]),
 (-1,
  [((711680 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((51952640 : Rat)/9, [0, 1, 1, 3]),
   ((13521920 : Rat)/3, [0, 1, 2, 2]),
   ((5693440 : Rat)/3, [0, 5]),
   ((-96788480 : Rat)/9, [1, 1, 1, 2]),
   ((-39854080 : Rat)/3, [1, 4]),
   ((-96788480 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_15_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_15)) skA_E0_Q1_15 := by decide +kernel

def skA_E0_Q1_16 : SectorVector := [(1,
  [(-61440, [0, 1, 1, 1, 1, 1]),
   (-311040, [0, 1, 1, 3]),
   (-49920, [0, 1, 2, 2]),
   (-61440, [0, 5]),
   (-506880, [1, 1, 1, 2]),
   (-860160, [1, 4]),
   (-184320, [2, 3])]),
 (-1,
  [(61440, [0, 1, 1, 1, 1, 1]),
   (311040, [0, 1, 1, 3]),
   (49920, [0, 1, 2, 2]),
   (61440, [0, 5]),
   (-506880, [1, 1, 1, 2]),
   (-860160, [1, 4]),
   (-184320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_16_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_16)) skA_E0_Q1_16 := by decide +kernel

def skA_E0_Q1_17 : SectorVector := [(1,
  [(-532480, [0, 1, 1, 1, 1, 1]),
   (-1664000, [0, 1, 1, 3]),
   (-1264640, [0, 1, 2, 2]),
   (-1064960, [0, 5]),
   (-6656000, [1, 1, 1, 2]),
   (-3727360, [1, 4]),
   (-1064960, [2, 3])]),
 (-1,
  [(532480, [0, 1, 1, 1, 1, 1]),
   (1664000, [0, 1, 1, 3]),
   (1264640, [0, 1, 2, 2]),
   (1064960, [0, 5]),
   (-6656000, [1, 1, 1, 2]),
   (-3727360, [1, 4]),
   (-1064960, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_17_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_17)) skA_E0_Q1_17 := by decide +kernel

def skA_E0_Q1_18 : SectorVector := [(1,
  [(92160, [0, 1, 1, 1, 1, 1]),
   (662400, [0, 1, 1, 3]),
   (385920, [0, 1, 2, 2]),
   (184320, [0, 5]),
   (1543680, [1, 1, 1, 2]),
   (1474560, [1, 4]),
   (737280, [2, 3])]),
 (-1,
  [(-92160, [0, 1, 1, 1, 1, 1]),
   (-662400, [0, 1, 1, 3]),
   (-385920, [0, 1, 2, 2]),
   (-184320, [0, 5]),
   (1543680, [1, 1, 1, 2]),
   (1474560, [1, 4]),
   (737280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_18_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_18)) skA_E0_Q1_18 := by decide +kernel

def skA_E0_Q1_19 : SectorVector := [(1,
  [(860160, [0, 1, 1, 1, 1, 1]),
   (5806080, [0, 1, 1, 3]),
   (5376000, [0, 1, 2, 2]),
   (1720320, [0, 5]),
   (18063360, [1, 1, 1, 2]),
   (9891840, [1, 4]),
   (9031680, [2, 3])]),
 (-1,
  [(-860160, [0, 1, 1, 1, 1, 1]),
   (-5806080, [0, 1, 1, 3]),
   (-5376000, [0, 1, 2, 2]),
   (-1720320, [0, 5]),
   (18063360, [1, 1, 1, 2]),
   (9891840, [1, 4]),
   (9031680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_19_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_19)) skA_E0_Q1_19 := by decide +kernel

def skA_E0_Q1_20 : SectorVector := [(1,
  [(1121280, [0, 1, 1, 1, 1, 1]),
   (9250560, [0, 1, 1, 3]),
   (7008000, [0, 1, 2, 2]),
   (1121280, [0, 5]),
   (23546880, [1, 1, 1, 2]),
   (15697920, [1, 4]),
   (13455360, [2, 3])]),
 (-1,
  [(-1121280, [0, 1, 1, 1, 1, 1]),
   (-9250560, [0, 1, 1, 3]),
   (-7008000, [0, 1, 2, 2]),
   (-1121280, [0, 5]),
   (23546880, [1, 1, 1, 2]),
   (15697920, [1, 4]),
   (13455360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_20_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_20)) skA_E0_Q1_20 := by decide +kernel

def skA_E0_Q1_21 : SectorVector := [(1,
  [((2967552 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((24482304 : Rat)/5, [0, 1, 1, 3]),
   (3709440, [0, 1, 2, 2]),
   ((5935104 : Rat)/5, [0, 5]),
   ((62318592 : Rat)/5, [1, 1, 1, 2]),
   ((47480832 : Rat)/5, [1, 4]),
   ((35610624 : Rat)/5, [2, 3])]),
 (-1,
  [((-2967552 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((-24482304 : Rat)/5, [0, 1, 1, 3]),
   (-3709440, [0, 1, 2, 2]),
   ((-5935104 : Rat)/5, [0, 5]),
   ((62318592 : Rat)/5, [1, 1, 1, 2]),
   ((47480832 : Rat)/5, [1, 4]),
   ((35610624 : Rat)/5, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_21_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_21)) skA_E0_Q1_21 := by decide +kernel

def skA_E0_Q1_22 : SectorVector := [(1,
  [(-655360, [0, 1, 1, 1, 1, 1]),
   (-716800, [0, 1, 1, 3]),
   (122880, [0, 1, 2, 2]),
   (-491520, [0, 5]),
   (-2621440, [1, 1, 1, 2]),
   (-3133440, [1, 4]),
   (-225280, [2, 3])]),
 (-1,
  [(655360, [0, 1, 1, 1, 1, 1]),
   (716800, [0, 1, 1, 3]),
   (-122880, [0, 1, 2, 2]),
   (491520, [0, 5]),
   (-2621440, [1, 1, 1, 2]),
   (-3133440, [1, 4]),
   (-225280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_22_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_22)) skA_E0_Q1_22 := by decide +kernel

def skA_E0_Q1_23 : SectorVector := [(1,
  [((6758400 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((19430400 : Rat)/7, [0, 1, 1, 3]),
   ((8236800 : Rat)/7, [0, 1, 2, 2]),
   ((5068800 : Rat)/7, [0, 5]),
   ((57446400 : Rat)/7, [1, 1, 1, 2]),
   ((45619200 : Rat)/7, [1, 4]),
   ((14361600 : Rat)/7, [2, 3])]),
 (-1,
  [((-6758400 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-19430400 : Rat)/7, [0, 1, 1, 3]),
   ((-8236800 : Rat)/7, [0, 1, 2, 2]),
   ((-5068800 : Rat)/7, [0, 5]),
   ((57446400 : Rat)/7, [1, 1, 1, 2]),
   ((45619200 : Rat)/7, [1, 4]),
   ((14361600 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_23_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_23)) skA_E0_Q1_23 := by decide +kernel

def skA_E0_Q1_24 : SectorVector := [(1,
  [(2129920, [0, 1, 1, 1, 1, 1]),
   (5923840, [0, 1, 1, 3]),
   (4392960, [0, 1, 2, 2]),
   (1597440, [0, 5]),
   (22896640, [1, 1, 1, 2]),
   (10183680, [1, 4]),
   (5524480, [2, 3])]),
 (-1,
  [(-2129920, [0, 1, 1, 1, 1, 1]),
   (-5923840, [0, 1, 1, 3]),
   (-4392960, [0, 1, 2, 2]),
   (-1597440, [0, 5]),
   (22896640, [1, 1, 1, 2]),
   (10183680, [1, 4]),
   (5524480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_24_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_24)) skA_E0_Q1_24 := by decide +kernel

def skA_E0_Q1_25 : SectorVector := [(1,
  [(2138112, [0, 1, 1, 1, 1, 1]),
   (7349760, [0, 1, 1, 3]),
   (4409856, [0, 1, 2, 2]),
   (801792, [0, 5]),
   (22984704, [1, 1, 1, 2]),
   (12828672, [1, 4]),
   (6948864, [2, 3])]),
 (-1,
  [(-2138112, [0, 1, 1, 1, 1, 1]),
   (-7349760, [0, 1, 1, 3]),
   (-4409856, [0, 1, 2, 2]),
   (-801792, [0, 5]),
   (22984704, [1, 1, 1, 2]),
   (12828672, [1, 4]),
   (6948864, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_25_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_25)) skA_E0_Q1_25 := by decide +kernel

def skA_E0_Q1_26 : SectorVector := [(1,
  [((2031616 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((5459968 : Rat)/3, [0, 1, 1, 3]),
   (2031616, [0, 1, 2, 2]),
   (507904, [0, 5]),
   ((26411008 : Rat)/3, [1, 1, 1, 2]),
   (1904640, [1, 4]),
   ((6983680 : Rat)/3, [2, 3])]),
 (-1,
  [((-2031616 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-5459968 : Rat)/3, [0, 1, 1, 3]),
   (-2031616, [0, 1, 2, 2]),
   (-507904, [0, 5]),
   ((26411008 : Rat)/3, [1, 1, 1, 2]),
   (1904640, [1, 4]),
   ((6983680 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_26_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_26)) skA_E0_Q1_26 := by decide +kernel

def skA_E0_Q1_27 : SectorVector := [(1,
  [(573440, [0, 1, 1, 1, 1, 1]),
   (1917440, [0, 1, 1, 3]),
   (1720320, [0, 1, 2, 2]),
   (7454720, [1, 1, 1, 2]),
   (1881600, [1, 4]),
   (2347520, [2, 3])]),
 (-1,
  [(-573440, [0, 1, 1, 1, 1, 1]),
   (-1917440, [0, 1, 1, 3]),
   (-1720320, [0, 1, 2, 2]),
   (7454720, [1, 1, 1, 2]),
   (1881600, [1, 4]),
   (2347520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_27_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_27)) skA_E0_Q1_27 := by decide +kernel

def skA_E0_Q1_28 : SectorVector := [(1,
  [((-11888640 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((-47554560 : Rat)/11, [0, 1, 1, 3]),
   ((-35665920 : Rat)/11, [0, 1, 2, 2]),
   ((-8916480 : Rat)/11, [0, 5]),
   ((-154552320 : Rat)/11, [1, 1, 1, 2]),
   ((-80248320 : Rat)/11, [1, 4]),
   ((-56471040 : Rat)/11, [2, 3])]),
 (-1,
  [((11888640 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((47554560 : Rat)/11, [0, 1, 1, 3]),
   ((35665920 : Rat)/11, [0, 1, 2, 2]),
   ((8916480 : Rat)/11, [0, 5]),
   ((-154552320 : Rat)/11, [1, 1, 1, 2]),
   ((-80248320 : Rat)/11, [1, 4]),
   ((-56471040 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_28_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_28)) skA_E0_Q1_28 := by decide +kernel

def skA_E0_Q1_29 : SectorVector := [(1,
  [((-131072 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-32768 : Rat)/3, [0, 1, 1, 3]),
   (34816, [0, 1, 2, 2]),
   (-16384, [0, 5]),
   ((-131072 : Rat)/3, [1, 1, 1, 2]),
   (-163840, [1, 4]),
   ((-106496 : Rat)/3, [2, 3])]),
 (-1,
  [((131072 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((32768 : Rat)/3, [0, 1, 1, 3]),
   (-34816, [0, 1, 2, 2]),
   (16384, [0, 5]),
   ((-131072 : Rat)/3, [1, 1, 1, 2]),
   (-163840, [1, 4]),
   ((-106496 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_29_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_29)) skA_E0_Q1_29 := by decide +kernel

def skA_E0_Q1_30 : SectorVector := [(1,
  [((1024000 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((1408000 : Rat)/3, [0, 1, 1, 3]),
   (112000, [0, 1, 2, 2]),
   (128000, [0, 5]),
   ((5632000 : Rat)/3, [1, 1, 1, 2]),
   (1280000, [1, 4]),
   ((832000 : Rat)/3, [2, 3])]),
 (-1,
  [((-1024000 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-1408000 : Rat)/3, [0, 1, 1, 3]),
   (-112000, [0, 1, 2, 2]),
   (-128000, [0, 5]),
   ((5632000 : Rat)/3, [1, 1, 1, 2]),
   (1280000, [1, 4]),
   ((832000 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_30_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_30)) skA_E0_Q1_30 := by decide +kernel

def skA_E0_Q1_31 : SectorVector := [(1,
  [(704512, [0, 1, 1, 1, 1, 1]),
   (968704, [0, 1, 1, 3]),
   (561408, [0, 1, 2, 2]),
   (264192, [0, 5]),
   (4931584, [1, 1, 1, 2]),
   (1849344, [1, 4]),
   (572416, [2, 3])]),
 (-1,
  [(-704512, [0, 1, 1, 1, 1, 1]),
   (-968704, [0, 1, 1, 3]),
   (-561408, [0, 1, 2, 2]),
   (-264192, [0, 5]),
   (4931584, [1, 1, 1, 2]),
   (1849344, [1, 4]),
   (572416, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_31_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_31)) skA_E0_Q1_31 := by decide +kernel

def skA_E0_Q1_32 : SectorVector := [(1,
  [(307200, [0, 1, 1, 1, 1, 1]),
   (537600, [0, 1, 1, 3]),
   (244800, [0, 1, 2, 2]),
   (2150400, [1, 1, 1, 2]),
   (921600, [1, 4]),
   (364800, [2, 3])]),
 (-1,
  [(-307200, [0, 1, 1, 1, 1, 1]),
   (-537600, [0, 1, 1, 3]),
   (-244800, [0, 1, 2, 2]),
   (2150400, [1, 1, 1, 2]),
   (921600, [1, 4]),
   (364800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_32_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_32)) skA_E0_Q1_32 := by decide +kernel

def skA_E0_Q1_33 : SectorVector := [(1,
  [(327680, [0, 1, 1, 1, 1, 1]),
   (450560, [0, 1, 1, 3]),
   (430080, [0, 1, 2, 2]),
   (61440, [0, 5]),
   (2785280, [1, 1, 1, 2]),
   (368640, [1, 4]),
   (327680, [2, 3])]),
 (-1,
  [(-327680, [0, 1, 1, 1, 1, 1]),
   (-450560, [0, 1, 1, 3]),
   (-430080, [0, 1, 2, 2]),
   (-61440, [0, 5]),
   (2785280, [1, 1, 1, 2]),
   (368640, [1, 4]),
   (327680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_33_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_33)) skA_E0_Q1_33 := by decide +kernel

def skA_E0_Q1_34 : SectorVector := [(1,
  [(-423936, [0, 1, 1, 1, 1, 1]),
   (-900864, [0, 1, 1, 3]),
   (-556416, [0, 1, 2, 2]),
   (-158976, [0, 5]),
   (-3603456, [1, 1, 1, 2]),
   (-1589760, [1, 4]),
   (-741888, [2, 3])]),
 (-1,
  [(423936, [0, 1, 1, 1, 1, 1]),
   (900864, [0, 1, 1, 3]),
   (556416, [0, 1, 2, 2]),
   (158976, [0, 5]),
   (-3603456, [1, 1, 1, 2]),
   (-1589760, [1, 4]),
   (-741888, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_34_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_34)) skA_E0_Q1_34 := by decide +kernel

def skA_E0_Q1_35 : SectorVector := [(1,
  [((901120 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((901120 : Rat)/81, [0, 1, 1, 3]),
   ((563200 : Rat)/27, [0, 1, 2, 2]),
   ((112640 : Rat)/27, [0, 5]),
   ((9011200 : Rat)/81, [1, 1, 1, 2]),
   ((-225280 : Rat)/27, [1, 4]),
   ((901120 : Rat)/81, [2, 3])]),
 (-1,
  [((-901120 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-901120 : Rat)/81, [0, 1, 1, 3]),
   ((-563200 : Rat)/27, [0, 1, 2, 2]),
   ((-112640 : Rat)/27, [0, 5]),
   ((9011200 : Rat)/81, [1, 1, 1, 2]),
   ((-225280 : Rat)/27, [1, 4]),
   ((901120 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_35_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_35)) skA_E0_Q1_35 := by decide +kernel

def skA_E0_Q1_36 : SectorVector := [(1,
  [((757760 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((1610240 : Rat)/9, [0, 1, 1, 3]),
   ((473600 : Rat)/3, [0, 1, 2, 2]),
   ((94720 : Rat)/3, [0, 5]),
   ((7577600 : Rat)/9, [1, 1, 1, 2]),
   ((663040 : Rat)/3, [1, 4]),
   ((1610240 : Rat)/9, [2, 3])]),
 (-1,
  [((-757760 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-1610240 : Rat)/9, [0, 1, 1, 3]),
   ((-473600 : Rat)/3, [0, 1, 2, 2]),
   ((-94720 : Rat)/3, [0, 5]),
   ((7577600 : Rat)/9, [1, 1, 1, 2]),
   ((663040 : Rat)/3, [1, 4]),
   ((1610240 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_36_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_36)) skA_E0_Q1_36 := by decide +kernel

def skA_E0_Q1_37 : SectorVector := [(1,
  [(291840, [0, 1, 1, 1, 1, 1]),
   (729600, [0, 1, 1, 3]),
   (547200, [0, 1, 2, 2]),
   (54720, [0, 5]),
   (2918400, [1, 1, 1, 2]),
   (984960, [1, 4]),
   (729600, [2, 3])]),
 (-1,
  [(-291840, [0, 1, 1, 1, 1, 1]),
   (-729600, [0, 1, 1, 3]),
   (-547200, [0, 1, 2, 2]),
   (-54720, [0, 5]),
   (2918400, [1, 1, 1, 2]),
   (984960, [1, 4]),
   (729600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_37_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_37)) skA_E0_Q1_37 := by decide +kernel

def skA_E0_Q1_38 : SectorVector := [(1,
  [(380928, [0, 1, 1, 1, 1, 1]),
   (952320, [0, 1, 1, 3]),
   (714240, [0, 1, 2, 2]),
   (142848, [0, 5]),
   (3809280, [1, 1, 1, 2]),
   (1428480, [1, 4]),
   (952320, [2, 3])]),
 (-1,
  [(-380928, [0, 1, 1, 1, 1, 1]),
   (-952320, [0, 1, 1, 3]),
   (-714240, [0, 1, 2, 2]),
   (-142848, [0, 5]),
   (3809280, [1, 1, 1, 2]),
   (1428480, [1, 4]),
   (952320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_38_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_38)) skA_E0_Q1_38 := by decide +kernel

def skA_E0_Q1_39 : SectorVector := [(1,
  [((609280 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((1523200 : Rat)/3, [0, 1, 1, 3]),
   (380800, [0, 1, 2, 2]),
   (76160, [0, 5]),
   ((6092800 : Rat)/3, [1, 1, 1, 2]),
   (761600, [1, 4]),
   ((1523200 : Rat)/3, [2, 3])]),
 (-1,
  [((-609280 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-1523200 : Rat)/3, [0, 1, 1, 3]),
   (-380800, [0, 1, 2, 2]),
   (-76160, [0, 5]),
   ((6092800 : Rat)/3, [1, 1, 1, 2]),
   (761600, [1, 4]),
   ((1523200 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q1_39_cert : VectorCertificate (Tpow 1 (aLeft false (7 : ℤ) skM_E0_39)) skA_E0_Q1_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_1_join : VectorCertificate ([skA_E0_Q1_0, skA_E0_Q1_1, skA_E0_Q1_2, skA_E0_Q1_3, skA_E0_Q1_4, skA_E0_Q1_5, skA_E0_Q1_6, skA_E0_Q1_7, skA_E0_Q1_8, skA_E0_Q1_9, skA_E0_Q1_10, skA_E0_Q1_11, skA_E0_Q1_12, skA_E0_Q1_13, skA_E0_Q1_14, skA_E0_Q1_15, skA_E0_Q1_16, skA_E0_Q1_17, skA_E0_Q1_18, skA_E0_Q1_19, skA_E0_Q1_20, skA_E0_Q1_21, skA_E0_Q1_22, skA_E0_Q1_23, skA_E0_Q1_24, skA_E0_Q1_25, skA_E0_Q1_26, skA_E0_Q1_27, skA_E0_Q1_28, skA_E0_Q1_29, skA_E0_Q1_30, skA_E0_Q1_31, skA_E0_Q1_32, skA_E0_Q1_33, skA_E0_Q1_34, skA_E0_Q1_35, skA_E0_Q1_36, skA_E0_Q1_37, skA_E0_Q1_38, skA_E0_Q1_39] : List SectorVector).flatten skQ_E0_1 := by decide +kernel

theorem skQ_E0_1_val : evaluate skQ_E0_1 = evaluate (OrbSgl.vTerm false skY_E0 0 1) :=
  vTerm_of_chunks false skY_E0 0 1 (7 : ℤ) (by norm_num) skM_E0 [skA_E0_Q1_0, skA_E0_Q1_1, skA_E0_Q1_2, skA_E0_Q1_3, skA_E0_Q1_4, skA_E0_Q1_5, skA_E0_Q1_6, skA_E0_Q1_7, skA_E0_Q1_8, skA_E0_Q1_9, skA_E0_Q1_10, skA_E0_Q1_11, skA_E0_Q1_12, skA_E0_Q1_13, skA_E0_Q1_14, skA_E0_Q1_15, skA_E0_Q1_16, skA_E0_Q1_17, skA_E0_Q1_18, skA_E0_Q1_19, skA_E0_Q1_20, skA_E0_Q1_21, skA_E0_Q1_22, skA_E0_Q1_23, skA_E0_Q1_24, skA_E0_Q1_25, skA_E0_Q1_26, skA_E0_Q1_27, skA_E0_Q1_28, skA_E0_Q1_29, skA_E0_Q1_30, skA_E0_Q1_31, skA_E0_Q1_32, skA_E0_Q1_33, skA_E0_Q1_34, skA_E0_Q1_35, skA_E0_Q1_36, skA_E0_Q1_37, skA_E0_Q1_38, skA_E0_Q1_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q1_0_cert (List.Forall₂.cons skA_E0_Q1_1_cert (List.Forall₂.cons skA_E0_Q1_2_cert (List.Forall₂.cons skA_E0_Q1_3_cert (List.Forall₂.cons skA_E0_Q1_4_cert (List.Forall₂.cons skA_E0_Q1_5_cert (List.Forall₂.cons skA_E0_Q1_6_cert (List.Forall₂.cons skA_E0_Q1_7_cert (List.Forall₂.cons skA_E0_Q1_8_cert (List.Forall₂.cons skA_E0_Q1_9_cert (List.Forall₂.cons skA_E0_Q1_10_cert (List.Forall₂.cons skA_E0_Q1_11_cert (List.Forall₂.cons skA_E0_Q1_12_cert (List.Forall₂.cons skA_E0_Q1_13_cert (List.Forall₂.cons skA_E0_Q1_14_cert (List.Forall₂.cons skA_E0_Q1_15_cert (List.Forall₂.cons skA_E0_Q1_16_cert (List.Forall₂.cons skA_E0_Q1_17_cert (List.Forall₂.cons skA_E0_Q1_18_cert (List.Forall₂.cons skA_E0_Q1_19_cert (List.Forall₂.cons skA_E0_Q1_20_cert (List.Forall₂.cons skA_E0_Q1_21_cert (List.Forall₂.cons skA_E0_Q1_22_cert (List.Forall₂.cons skA_E0_Q1_23_cert (List.Forall₂.cons skA_E0_Q1_24_cert (List.Forall₂.cons skA_E0_Q1_25_cert (List.Forall₂.cons skA_E0_Q1_26_cert (List.Forall₂.cons skA_E0_Q1_27_cert (List.Forall₂.cons skA_E0_Q1_28_cert (List.Forall₂.cons skA_E0_Q1_29_cert (List.Forall₂.cons skA_E0_Q1_30_cert (List.Forall₂.cons skA_E0_Q1_31_cert (List.Forall₂.cons skA_E0_Q1_32_cert (List.Forall₂.cons skA_E0_Q1_33_cert (List.Forall₂.cons skA_E0_Q1_34_cert (List.Forall₂.cons skA_E0_Q1_35_cert (List.Forall₂.cons skA_E0_Q1_36_cert (List.Forall₂.cons skA_E0_Q1_37_cert (List.Forall₂.cons skA_E0_Q1_38_cert (List.Forall₂.cons skA_E0_Q1_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_1 skQ_E0_1_join

def skA_E0_Q2_0 : SectorVector := [(-1,
  [((536870912 : Rat)/4455, [0, 1, 1, 1, 1, 1]),
   ((-14361296896 : Rat)/31185, [0, 1, 1, 3]),
   ((-5502926848 : Rat)/10395, [0, 1, 2, 2]),
   ((4294967296 : Rat)/10395, [0, 5]),
   ((25232932864 : Rat)/31185, [1, 1, 1, 2]),
   ((-4294967296 : Rat)/10395, [1, 4]),
   ((4294967296 : Rat)/4455, [2, 3])]),
 (1,
  [((-536870912 : Rat)/4455, [0, 1, 1, 1, 1, 1]),
   ((14361296896 : Rat)/31185, [0, 1, 1, 3]),
   ((5502926848 : Rat)/10395, [0, 1, 2, 2]),
   ((-4294967296 : Rat)/10395, [0, 5]),
   ((25232932864 : Rat)/31185, [1, 1, 1, 2]),
   ((-4294967296 : Rat)/10395, [1, 4]),
   ((4294967296 : Rat)/4455, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_0_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_0)) skA_E0_Q2_0 := by decide +kernel

def skA_E0_Q2_1 : SectorVector := [(-1,
  [((16777216 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-20971520 : Rat)/81, [0, 1, 1, 3]),
   ((-46137344 : Rat)/27, [0, 1, 2, 2]),
   ((83886080 : Rat)/27, [0, 5]),
   ((285212672 : Rat)/81, [1, 1, 1, 2]),
   ((-234881024 : Rat)/27, [1, 4]),
   ((134217728 : Rat)/81, [2, 3])]),
 (1,
  [((-16777216 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((20971520 : Rat)/81, [0, 1, 1, 3]),
   ((46137344 : Rat)/27, [0, 1, 2, 2]),
   ((-83886080 : Rat)/27, [0, 5]),
   ((285212672 : Rat)/81, [1, 1, 1, 2]),
   ((-234881024 : Rat)/27, [1, 4]),
   ((134217728 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_1_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_1)) skA_E0_Q2_1 := by decide +kernel

def skA_E0_Q2_2 : SectorVector := [(-1,
  [((-33554432 : Rat)/21, [0, 1, 1, 1, 1, 1]),
   ((243269632 : Rat)/21, [0, 1, 1, 3]),
   ((-8388608 : Rat)/7, [0, 1, 2, 2]),
   ((134217728 : Rat)/7, [0, 5]),
   ((33554432 : Rat)/3, [1, 1, 1, 2]),
   ((-536870912 : Rat)/7, [1, 4]),
   ((-268435456 : Rat)/21, [2, 3])]),
 (1,
  [((33554432 : Rat)/21, [0, 1, 1, 1, 1, 1]),
   ((-243269632 : Rat)/21, [0, 1, 1, 3]),
   ((8388608 : Rat)/7, [0, 1, 2, 2]),
   ((-134217728 : Rat)/7, [0, 5]),
   ((33554432 : Rat)/3, [1, 1, 1, 2]),
   ((-536870912 : Rat)/7, [1, 4]),
   ((-268435456 : Rat)/21, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_2_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_2)) skA_E0_Q2_2 := by decide +kernel

def skA_E0_Q2_3 : SectorVector := [(-1,
  [((4456448 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((-26017792 : Rat)/15, [0, 1, 1, 3]),
   ((-2031616 : Rat)/5, [0, 1, 2, 2]),
   ((-8388608 : Rat)/5, [0, 5]),
   ((-6029312 : Rat)/15, [1, 1, 1, 2]),
   ((39845888 : Rat)/5, [1, 4]),
   ((35651584 : Rat)/15, [2, 3])]),
 (1,
  [((-4456448 : Rat)/15, [0, 1, 1, 1, 1, 1]),
   ((26017792 : Rat)/15, [0, 1, 1, 3]),
   ((2031616 : Rat)/5, [0, 1, 2, 2]),
   ((8388608 : Rat)/5, [0, 5]),
   ((-6029312 : Rat)/15, [1, 1, 1, 2]),
   ((39845888 : Rat)/5, [1, 4]),
   ((35651584 : Rat)/15, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_3_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_3)) skA_E0_Q2_3 := by decide +kernel

def skA_E0_Q2_4 : SectorVector := [(-1,
  [(-1310720, [0, 1, 1, 1, 1, 1]),
   (7929856, [0, 1, 1, 3]),
   (2555904, [0, 1, 2, 2]),
   (6291456, [0, 5]),
   (-262144, [1, 1, 1, 2]),
   (-32243712, [1, 4]),
   (-11272192, [2, 3])]),
 (1,
  [(1310720, [0, 1, 1, 1, 1, 1]),
   (-7929856, [0, 1, 1, 3]),
   (-2555904, [0, 1, 2, 2]),
   (-6291456, [0, 5]),
   (-262144, [1, 1, 1, 2]),
   (-32243712, [1, 4]),
   (-11272192, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_4_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_4)) skA_E0_Q2_4 := by decide +kernel

def skA_E0_Q2_5 : SectorVector := [(-1,
  [((-28835840 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((139853824 : Rat)/27, [0, 1, 1, 3]),
   ((27394048 : Rat)/9, [0, 1, 2, 2]),
   ((11534336 : Rat)/9, [0, 5]),
   ((-74973184 : Rat)/27, [1, 1, 1, 2]),
   ((-115343360 : Rat)/9, [1, 4]),
   ((-230686720 : Rat)/27, [2, 3])]),
 (1,
  [((28835840 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-139853824 : Rat)/27, [0, 1, 1, 3]),
   ((-27394048 : Rat)/9, [0, 1, 2, 2]),
   ((-11534336 : Rat)/9, [0, 5]),
   ((-74973184 : Rat)/27, [1, 1, 1, 2]),
   ((-115343360 : Rat)/9, [1, 4]),
   ((-230686720 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_5_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_5)) skA_E0_Q2_5 := by decide +kernel

def skA_E0_Q2_6 : SectorVector := [(-1,
  [((-17432576 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((126386176 : Rat)/3, [0, 1, 1, 3]),
   (18055168, [0, 1, 2, 2]),
   (24903680, [0, 5]),
   ((-57278464 : Rat)/3, [1, 1, 1, 2]),
   (-144441344, [1, 4]),
   ((-184287232 : Rat)/3, [2, 3])]),
 (1,
  [((17432576 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-126386176 : Rat)/3, [0, 1, 1, 3]),
   (-18055168, [0, 1, 2, 2]),
   (-24903680, [0, 5]),
   ((-57278464 : Rat)/3, [1, 1, 1, 2]),
   (-144441344, [1, 4]),
   ((-184287232 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_6_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_6)) skA_E0_Q2_6 := by decide +kernel

def skA_E0_Q2_7 : SectorVector := [(-1,
  [(212992, [0, 1, 1, 1, 1, 1]),
   ((-21032960 : Rat)/7, [0, 1, 1, 3]),
   ((-10383360 : Rat)/7, [0, 1, 2, 2]),
   ((-10223616 : Rat)/7, [0, 5]),
   ((20234240 : Rat)/7, [1, 1, 1, 2]),
   ((63897600 : Rat)/7, [1, 4]),
   (4259840, [2, 3])]),
 (1,
  [(-212992, [0, 1, 1, 1, 1, 1]),
   ((21032960 : Rat)/7, [0, 1, 1, 3]),
   ((10383360 : Rat)/7, [0, 1, 2, 2]),
   ((10223616 : Rat)/7, [0, 5]),
   ((20234240 : Rat)/7, [1, 1, 1, 2]),
   ((63897600 : Rat)/7, [1, 4]),
   (4259840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_7_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_7)) skA_E0_Q2_7 := by decide +kernel

def skA_E0_Q2_8 : SectorVector := [(-1,
  [(655360, [0, 1, 1, 1, 1, 1]),
   (10977280, [0, 1, 1, 3]),
   (491520, [0, 1, 2, 2]),
   (15728640, [0, 5]),
   (-4587520, [1, 1, 1, 2]),
   (-62914560, [1, 4]),
   (-10485760, [2, 3])]),
 (1,
  [(-655360, [0, 1, 1, 1, 1, 1]),
   (-10977280, [0, 1, 1, 3]),
   (-491520, [0, 1, 2, 2]),
   (-15728640, [0, 5]),
   (-4587520, [1, 1, 1, 2]),
   (-62914560, [1, 4]),
   (-10485760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_8_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_8)) skA_E0_Q2_8 := by decide +kernel

def skA_E0_Q2_9 : SectorVector := [(-1,
  [(-655360, [0, 1, 1, 1, 1, 1]),
   (-34570240, [0, 1, 1, 3]),
   (-18186240, [0, 1, 2, 2]),
   (-15728640, [0, 5]),
   (51773440, [1, 1, 1, 2]),
   (98304000, [1, 4]),
   (45875200, [2, 3])]),
 (1,
  [(655360, [0, 1, 1, 1, 1, 1]),
   (34570240, [0, 1, 1, 3]),
   (18186240, [0, 1, 2, 2]),
   (15728640, [0, 5]),
   (51773440, [1, 1, 1, 2]),
   (98304000, [1, 4]),
   (45875200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_9_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_9)) skA_E0_Q2_9 := by decide +kernel

def skA_E0_Q2_10 : SectorVector := [(-1,
  [((-1998848 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-117432320 : Rat)/3, [0, 1, 1, 3]),
   (-24485888, [0, 1, 2, 2]),
   (-9994240, [0, 5]),
   ((205881344 : Rat)/3, [1, 1, 1, 2]),
   (87949312, [1, 4]),
   ((163905536 : Rat)/3, [2, 3])]),
 (1,
  [((1998848 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((117432320 : Rat)/3, [0, 1, 1, 3]),
   (24485888, [0, 1, 2, 2]),
   (9994240, [0, 5]),
   ((205881344 : Rat)/3, [1, 1, 1, 2]),
   (87949312, [1, 4]),
   ((163905536 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_10_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_10)) skA_E0_Q2_10 := by decide +kernel

def skA_E0_Q2_11 : SectorVector := [(-1,
  [(-327680, [0, 1, 1, 1, 1, 1]),
   (-21217280, [0, 1, 1, 3]),
   (-12042240, [0, 1, 2, 2]),
   (-7864320, [0, 5]),
   (33751040, [1, 1, 1, 2]),
   (55050240, [1, 4]),
   (28835840, [2, 3])]),
 (1,
  [(327680, [0, 1, 1, 1, 1, 1]),
   (21217280, [0, 1, 1, 3]),
   (12042240, [0, 1, 2, 2]),
   (7864320, [0, 5]),
   (33751040, [1, 1, 1, 2]),
   (55050240, [1, 4]),
   (28835840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_11_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_11)) skA_E0_Q2_11 := by decide +kernel

def skA_E0_Q2_12 : SectorVector := [(-1,
  [(-4395008, [0, 1, 1, 1, 1, 1]),
   (-25152512, [0, 1, 1, 3]),
   (-13986816, [0, 1, 2, 2]),
   (-11403264, [0, 5]),
   (59273216, [1, 1, 1, 2]),
   (66994176, [1, 4]),
   (28983296, [2, 3])]),
 (1,
  [(4395008, [0, 1, 1, 1, 1, 1]),
   (25152512, [0, 1, 1, 3]),
   (13986816, [0, 1, 2, 2]),
   (11403264, [0, 5]),
   (59273216, [1, 1, 1, 2]),
   (66994176, [1, 4]),
   (28983296, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_12_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_12)) skA_E0_Q2_12 := by decide +kernel

def skA_E0_Q2_13 : SectorVector := [(-1,
  [(-4167680, [0, 1, 1, 1, 1, 1]),
   (-27906560, [0, 1, 1, 3]),
   (-18332160, [0, 1, 2, 2]),
   (-6758400, [0, 5]),
   (69724160, [1, 1, 1, 2]),
   (57446400, [1, 4]),
   (34918400, [2, 3])]),
 (1,
  [(4167680, [0, 1, 1, 1, 1, 1]),
   (27906560, [0, 1, 1, 3]),
   (18332160, [0, 1, 2, 2]),
   (6758400, [0, 5]),
   (69724160, [1, 1, 1, 2]),
   (57446400, [1, 4]),
   (34918400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_13_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_13)) skA_E0_Q2_13 := by decide +kernel

def skA_E0_Q2_14 : SectorVector := [(-1,
  [((-3031040 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-21278720 : Rat)/81, [0, 1, 1, 3]),
   ((-5672960 : Rat)/27, [0, 1, 2, 2]),
   ((327680 : Rat)/27, [0, 5]),
   ((60538880 : Rat)/81, [1, 1, 1, 2]),
   ((8519680 : Rat)/27, [1, 4]),
   ((28835840 : Rat)/81, [2, 3])]),
 (1,
  [((3031040 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((21278720 : Rat)/81, [0, 1, 1, 3]),
   ((5672960 : Rat)/27, [0, 1, 2, 2]),
   ((-327680 : Rat)/27, [0, 5]),
   ((60538880 : Rat)/81, [1, 1, 1, 2]),
   ((8519680 : Rat)/27, [1, 4]),
   ((28835840 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_14_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_14)) skA_E0_Q2_14 := by decide +kernel

def skA_E0_Q2_15 : SectorVector := [(-1,
  [((26332160 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((236099840 : Rat)/9, [0, 1, 1, 3]),
   ((49283840 : Rat)/3, [0, 1, 2, 2]),
   ((22773760 : Rat)/3, [0, 5]),
   ((-525931520 : Rat)/9, [1, 1, 1, 2]),
   ((-176496640 : Rat)/3, [1, 4]),
   ((-301752320 : Rat)/9, [2, 3])]),
 (1,
  [((-26332160 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-236099840 : Rat)/9, [0, 1, 1, 3]),
   ((-49283840 : Rat)/3, [0, 1, 2, 2]),
   ((-22773760 : Rat)/3, [0, 5]),
   ((-525931520 : Rat)/9, [1, 1, 1, 2]),
   ((-176496640 : Rat)/3, [1, 4]),
   ((-301752320 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_15_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_15)) skA_E0_Q2_15 := by decide +kernel

def skA_E0_Q2_16 : SectorVector := [(-1,
  [(450560, [0, 1, 1, 1, 1, 1]),
   (1034240, [0, 1, 1, 3]),
   (614400, [0, 1, 2, 2]),
   (491520, [0, 5]),
   (-3891200, [1, 1, 1, 2]),
   (-2519040, [1, 4]),
   (-880640, [2, 3])]),
 (1,
  [(-450560, [0, 1, 1, 1, 1, 1]),
   (-1034240, [0, 1, 1, 3]),
   (-614400, [0, 1, 2, 2]),
   (-491520, [0, 5]),
   (-3891200, [1, 1, 1, 2]),
   (-2519040, [1, 4]),
   (-880640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_16_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_16)) skA_E0_Q2_16 := by decide +kernel

def skA_E0_Q2_17 : SectorVector := [(-1,
  [((11714560 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((30085120 : Rat)/3, [0, 1, 1, 3]),
   (7720960, [0, 1, 2, 2]),
   (1064960, [0, 5]),
   ((-120340480 : Rat)/3, [1, 1, 1, 2]),
   (-13844480, [1, 4]),
   ((-30883840 : Rat)/3, [2, 3])]),
 (1,
  [((-11714560 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-30085120 : Rat)/3, [0, 1, 1, 3]),
   (-7720960, [0, 1, 2, 2]),
   (-1064960, [0, 5]),
   ((-120340480 : Rat)/3, [1, 1, 1, 2]),
   (-13844480, [1, 4]),
   ((-30883840 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_17_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_17)) skA_E0_Q2_17 := by decide +kernel

def skA_E0_Q2_18 : SectorVector := [(-1,
  [(-675840, [0, 1, 1, 1, 1, 1]),
   (-2657280, [0, 1, 1, 3]),
   (-1751040, [0, 1, 2, 2]),
   (-737280, [0, 5]),
   (8048640, [1, 1, 1, 2]),
   (5437440, [1, 4]),
   (2979840, [2, 3])]),
 (1,
  [(675840, [0, 1, 1, 1, 1, 1]),
   (2657280, [0, 1, 1, 3]),
   (1751040, [0, 1, 2, 2]),
   (737280, [0, 5]),
   (8048640, [1, 1, 1, 2]),
   (5437440, [1, 4]),
   (2979840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_18_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_18)) skA_E0_Q2_18 := by decide +kernel

def skA_E0_Q2_19 : SectorVector := [(-1,
  [(-6307840, [0, 1, 1, 1, 1, 1]),
   (-28241920, [0, 1, 1, 3]),
   (-20213760, [0, 1, 2, 2]),
   (-4300800, [0, 5]),
   (85442560, [1, 1, 1, 2]),
   (48168960, [1, 4]),
   (33832960, [2, 3])]),
 (1,
  [(6307840, [0, 1, 1, 1, 1, 1]),
   (28241920, [0, 1, 1, 3]),
   (20213760, [0, 1, 2, 2]),
   (4300800, [0, 5]),
   (85442560, [1, 1, 1, 2]),
   (48168960, [1, 4]),
   (33832960, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_19_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_19)) skA_E0_Q2_19 := by decide +kernel

def skA_E0_Q2_20 : SectorVector := [(-1,
  [(-8222720, [0, 1, 1, 1, 1, 1]),
   (-39057920, [0, 1, 1, 3]),
   (-26350080, [0, 1, 2, 2]),
   (-8970240, [0, 5]),
   (111380480, [1, 1, 1, 2]),
   (76247040, [1, 4]),
   (46346240, [2, 3])]),
 (1,
  [(8222720, [0, 1, 1, 1, 1, 1]),
   (39057920, [0, 1, 1, 3]),
   (26350080, [0, 1, 2, 2]),
   (8970240, [0, 5]),
   (111380480, [1, 1, 1, 2]),
   (76247040, [1, 4]),
   (46346240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_20_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_20)) skA_E0_Q2_20 := by decide +kernel

def skA_E0_Q2_21 : SectorVector := [(-1,
  [((-21762048 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((-103369728 : Rat)/5, [0, 1, 1, 3]),
   ((-69737472 : Rat)/5, [0, 1, 2, 2]),
   ((-23740416 : Rat)/5, [0, 5]),
   ((294776832 : Rat)/5, [1, 1, 1, 2]),
   ((201793536 : Rat)/5, [1, 4]),
   ((122658816 : Rat)/5, [2, 3])]),
 (1,
  [((21762048 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   ((103369728 : Rat)/5, [0, 1, 1, 3]),
   ((69737472 : Rat)/5, [0, 1, 2, 2]),
   ((23740416 : Rat)/5, [0, 5]),
   ((294776832 : Rat)/5, [1, 1, 1, 2]),
   ((201793536 : Rat)/5, [1, 4]),
   ((122658816 : Rat)/5, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_21_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_21)) skA_E0_Q2_21 := by decide +kernel

def skA_E0_Q2_22 : SectorVector := [(-1,
  [(3276800, [0, 1, 1, 1, 1, 1]),
   (3276800, [0, 1, 1, 3]),
   (2457600, [0, 1, 2, 2]),
   (1228800, [0, 5]),
   (-22937600, [1, 1, 1, 2]),
   (-4915200, [1, 4]),
   (-819200, [2, 3])]),
 (1,
  [(-3276800, [0, 1, 1, 1, 1, 1]),
   (-3276800, [0, 1, 1, 3]),
   (-2457600, [0, 1, 2, 2]),
   (-1228800, [0, 5]),
   (-22937600, [1, 1, 1, 2]),
   (-4915200, [1, 4]),
   (-819200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_22_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_22)) skA_E0_Q2_22 := by decide +kernel

def skA_E0_Q2_23 : SectorVector := [(-1,
  [((-33792000 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-74342400 : Rat)/7, [0, 1, 1, 3]),
   ((-51955200 : Rat)/7, [0, 1, 2, 2]),
   ((-20275200 : Rat)/7, [0, 5]),
   (43929600, [1, 1, 1, 2]),
   ((134323200 : Rat)/7, [1, 4]),
   ((66739200 : Rat)/7, [2, 3])]),
 (1,
  [((33792000 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((74342400 : Rat)/7, [0, 1, 1, 3]),
   ((51955200 : Rat)/7, [0, 1, 2, 2]),
   ((20275200 : Rat)/7, [0, 5]),
   (43929600, [1, 1, 1, 2]),
   ((134323200 : Rat)/7, [1, 4]),
   ((66739200 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_23_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_23)) skA_E0_Q2_23 := by decide +kernel

def skA_E0_Q2_24 : SectorVector := [(-1,
  [(-10649600, [0, 1, 1, 1, 1, 1]),
   (-27422720, [0, 1, 1, 3]),
   (-20567040, [0, 1, 2, 2]),
   (-3993600, [0, 5]),
   (108093440, [1, 1, 1, 2]),
   (41134080, [1, 4]),
   (27822080, [2, 3])]),
 (1,
  [(10649600, [0, 1, 1, 1, 1, 1]),
   (27422720, [0, 1, 1, 3]),
   (20567040, [0, 1, 2, 2]),
   (3993600, [0, 5]),
   (108093440, [1, 1, 1, 2]),
   (41134080, [1, 4]),
   (27822080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_24_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_24)) skA_E0_Q2_24 := by decide +kernel

def skA_E0_Q2_25 : SectorVector := [(-1,
  [(-10690560, [0, 1, 1, 1, 1, 1]),
   (-29131776, [0, 1, 1, 3]),
   (-20646144, [0, 1, 2, 2]),
   (-6414336, [0, 5]),
   (108509184, [1, 1, 1, 2]),
   (50913792, [1, 4]),
   (29532672, [2, 3])]),
 (1,
  [(10690560, [0, 1, 1, 1, 1, 1]),
   (29131776, [0, 1, 1, 3]),
   (20646144, [0, 1, 2, 2]),
   (6414336, [0, 5]),
   (108509184, [1, 1, 1, 2]),
   (50913792, [1, 4]),
   (29532672, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_25_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_25)) skA_E0_Q2_25 := by decide +kernel

def skA_E0_Q2_26 : SectorVector := [(-1,
  [((-10158080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-29966336 : Rat)/3, [0, 1, 1, 3]),
   (-7872512, [0, 1, 2, 2]),
   (-507904, [0, 5]),
   ((113770496 : Rat)/3, [1, 1, 1, 2]),
   (12697600, [1, 4]),
   ((33013760 : Rat)/3, [2, 3])]),
 (1,
  [((10158080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((29966336 : Rat)/3, [0, 1, 1, 3]),
   (7872512, [0, 1, 2, 2]),
   (507904, [0, 5]),
   ((113770496 : Rat)/3, [1, 1, 1, 2]),
   (12697600, [1, 4]),
   ((33013760 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_26_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_26)) skA_E0_Q2_26 := by decide +kernel

def skA_E0_Q2_27 : SectorVector := [(-1,
  [(-2867200, [0, 1, 1, 1, 1, 1]),
   (-8888320, [0, 1, 1, 3]),
   (-6666240, [0, 1, 2, 2]),
   (-1075200, [0, 5]),
   (32112640, [1, 1, 1, 2]),
   (13332480, [1, 4]),
   (9748480, [2, 3])]),
 (1,
  [(2867200, [0, 1, 1, 1, 1, 1]),
   (8888320, [0, 1, 1, 3]),
   (6666240, [0, 1, 2, 2]),
   (1075200, [0, 5]),
   (32112640, [1, 1, 1, 2]),
   (13332480, [1, 4]),
   (9748480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_27_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_27)) skA_E0_Q2_27 := by decide +kernel

def skA_E0_Q2_28 : SectorVector := [(-1,
  [((59443200 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((193190400 : Rat)/11, [0, 1, 1, 3]),
   ((138205440 : Rat)/11, [0, 1, 2, 2]),
   ((35665920 : Rat)/11, [0, 5]),
   ((-665763840 : Rat)/11, [1, 1, 1, 2]),
   ((-329909760 : Rat)/11, [1, 4]),
   ((-211023360 : Rat)/11, [2, 3])]),
 (1,
  [((-59443200 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((-193190400 : Rat)/11, [0, 1, 1, 3]),
   ((-138205440 : Rat)/11, [0, 1, 2, 2]),
   ((-35665920 : Rat)/11, [0, 5]),
   ((-665763840 : Rat)/11, [1, 1, 1, 2]),
   ((-329909760 : Rat)/11, [1, 4]),
   ((-211023360 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_28_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_28)) skA_E0_Q2_28 := by decide +kernel

def skA_E0_Q2_29 : SectorVector := [(-1,
  [((524288 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((131072 : Rat)/3, [0, 1, 1, 3]),
   (32768, [0, 1, 2, 2]),
   (65536, [0, 5]),
   ((-2883584 : Rat)/3, [1, 1, 1, 2]),
   (-65536, [1, 4]),
   ((458752 : Rat)/3, [2, 3])]),
 (1,
  [((-524288 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-131072 : Rat)/3, [0, 1, 1, 3]),
   (-32768, [0, 1, 2, 2]),
   (-65536, [0, 5]),
   ((-2883584 : Rat)/3, [1, 1, 1, 2]),
   (-65536, [1, 4]),
   ((458752 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_29_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_29)) skA_E0_Q2_29 := by decide +kernel

def skA_E0_Q2_30 : SectorVector := [(-1,
  [((-4096000 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-5632000 : Rat)/3, [0, 1, 1, 3]),
   (-1408000, [0, 1, 2, 2]),
   (-512000, [0, 5]),
   ((31744000 : Rat)/3, [1, 1, 1, 2]),
   (2816000, [1, 4]),
   ((3328000 : Rat)/3, [2, 3])]),
 (1,
  [((4096000 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((5632000 : Rat)/3, [0, 1, 1, 3]),
   (1408000, [0, 1, 2, 2]),
   (512000, [0, 5]),
   ((31744000 : Rat)/3, [1, 1, 1, 2]),
   (2816000, [1, 4]),
   ((3328000 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_30_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_30)) skA_E0_Q2_30 := by decide +kernel

def skA_E0_Q2_31 : SectorVector := [(-1,
  [(-2818048, [0, 1, 1, 1, 1, 1]),
   (-4667392, [0, 1, 1, 3]),
   (-3698688, [0, 1, 2, 2]),
   (-660480, [0, 5]),
   (23953408, [1, 1, 1, 2]),
   (5812224, [1, 4]),
   (3610624, [2, 3])]),
 (1,
  [(2818048, [0, 1, 1, 1, 1, 1]),
   (4667392, [0, 1, 1, 3]),
   (3698688, [0, 1, 2, 2]),
   (660480, [0, 5]),
   (23953408, [1, 1, 1, 2]),
   (5812224, [1, 4]),
   (3610624, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_31_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_31)) skA_E0_Q2_31 := by decide +kernel

def skA_E0_Q2_32 : SectorVector := [(-1,
  [(-1228800, [0, 1, 1, 1, 1, 1]),
   (-2150400, [0, 1, 1, 3]),
   (-1612800, [0, 1, 2, 2]),
   (-460800, [0, 5]),
   (10444800, [1, 1, 1, 2]),
   (3225600, [1, 4]),
   (1689600, [2, 3])]),
 (1,
  [(1228800, [0, 1, 1, 1, 1, 1]),
   (2150400, [0, 1, 1, 3]),
   (1612800, [0, 1, 2, 2]),
   (460800, [0, 5]),
   (10444800, [1, 1, 1, 2]),
   (3225600, [1, 4]),
   (1689600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_32_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_32)) skA_E0_Q2_32 := by decide +kernel

def skA_E0_Q2_33 : SectorVector := [(-1,
  [(-1310720, [0, 1, 1, 1, 1, 1]),
   (-2539520, [0, 1, 1, 3]),
   (-2088960, [0, 1, 2, 2]),
   (-122880, [0, 5]),
   (12124160, [1, 1, 1, 2]),
   (2703360, [1, 4]),
   (2293760, [2, 3])]),
 (1,
  [(1310720, [0, 1, 1, 1, 1, 1]),
   (2539520, [0, 1, 1, 3]),
   (2088960, [0, 1, 2, 2]),
   (122880, [0, 5]),
   (12124160, [1, 1, 1, 2]),
   (2703360, [1, 4]),
   (2293760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_33_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_33)) skA_E0_Q2_33 := by decide +kernel

def skA_E0_Q2_34 : SectorVector := [(-1,
  [(1695744, [0, 1, 1, 1, 1, 1]),
   (3603456, [0, 1, 1, 3]),
   (2702592, [0, 1, 2, 2]),
   (635904, [0, 5]),
   (-15685632, [1, 1, 1, 2]),
   (-5405184, [1, 4]),
   (-3285504, [2, 3])]),
 (1,
  [(-1695744, [0, 1, 1, 1, 1, 1]),
   (-3603456, [0, 1, 1, 3]),
   (-2702592, [0, 1, 2, 2]),
   (-635904, [0, 5]),
   (-15685632, [1, 1, 1, 2]),
   (-5405184, [1, 4]),
   (-3285504, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_34_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_34)) skA_E0_Q2_34 := by decide +kernel

def skA_E0_Q2_35 : SectorVector := [(-1,
  [((-3604480 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((-7659520 : Rat)/81, [0, 1, 1, 3]),
   ((-2252800 : Rat)/27, [0, 1, 2, 2]),
   ((225280 : Rat)/27, [0, 5]),
   ((36044800 : Rat)/81, [1, 1, 1, 2]),
   ((1802240 : Rat)/27, [1, 4]),
   ((7659520 : Rat)/81, [2, 3])]),
 (1,
  [((3604480 : Rat)/81, [0, 1, 1, 1, 1, 1]),
   ((7659520 : Rat)/81, [0, 1, 1, 3]),
   ((2252800 : Rat)/27, [0, 1, 2, 2]),
   ((-225280 : Rat)/27, [0, 5]),
   ((36044800 : Rat)/81, [1, 1, 1, 2]),
   ((1802240 : Rat)/27, [1, 4]),
   ((7659520 : Rat)/81, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_35_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_35)) skA_E0_Q2_35 := by decide +kernel

def skA_E0_Q2_36 : SectorVector := [(-1,
  [((-3031040 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-7293440 : Rat)/9, [0, 1, 1, 3]),
   ((-1894400 : Rat)/3, [0, 1, 2, 2]),
   ((-236800 : Rat)/3, [0, 5]),
   ((30310400 : Rat)/9, [1, 1, 1, 2]),
   ((3220480 : Rat)/3, [1, 4]),
   ((7293440 : Rat)/9, [2, 3])]),
 (1,
  [((3031040 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((7293440 : Rat)/9, [0, 1, 1, 3]),
   ((1894400 : Rat)/3, [0, 1, 2, 2]),
   ((236800 : Rat)/3, [0, 5]),
   ((30310400 : Rat)/9, [1, 1, 1, 2]),
   ((3220480 : Rat)/3, [1, 4]),
   ((7293440 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_36_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_36)) skA_E0_Q2_36 := by decide +kernel

def skA_E0_Q2_37 : SectorVector := [(-1,
  [(-1167360, [0, 1, 1, 1, 1, 1]),
   (-2918400, [0, 1, 1, 3]),
   (-2188800, [0, 1, 2, 2]),
   (-437760, [0, 5]),
   (11673600, [1, 1, 1, 2]),
   (4377600, [1, 4]),
   (2918400, [2, 3])]),
 (1,
  [(1167360, [0, 1, 1, 1, 1, 1]),
   (2918400, [0, 1, 1, 3]),
   (2188800, [0, 1, 2, 2]),
   (437760, [0, 5]),
   (11673600, [1, 1, 1, 2]),
   (4377600, [1, 4]),
   (2918400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_37_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_37)) skA_E0_Q2_37 := by decide +kernel

def skA_E0_Q2_38 : SectorVector := [(-1,
  [(-1523712, [0, 1, 1, 1, 1, 1]),
   (-3809280, [0, 1, 1, 3]),
   (-2856960, [0, 1, 2, 2]),
   (-571392, [0, 5]),
   (15237120, [1, 1, 1, 2]),
   (5713920, [1, 4]),
   (3809280, [2, 3])]),
 (1,
  [(1523712, [0, 1, 1, 1, 1, 1]),
   (3809280, [0, 1, 1, 3]),
   (2856960, [0, 1, 2, 2]),
   (571392, [0, 5]),
   (15237120, [1, 1, 1, 2]),
   (5713920, [1, 4]),
   (3809280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_38_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_38)) skA_E0_Q2_38 := by decide +kernel

def skA_E0_Q2_39 : SectorVector := [(-1,
  [((-2437120 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-6092800 : Rat)/3, [0, 1, 1, 3]),
   (-1523200, [0, 1, 2, 2]),
   (-304640, [0, 5]),
   ((24371200 : Rat)/3, [1, 1, 1, 2]),
   (3046400, [1, 4]),
   ((6092800 : Rat)/3, [2, 3])]),
 (1,
  [((2437120 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((6092800 : Rat)/3, [0, 1, 1, 3]),
   (1523200, [0, 1, 2, 2]),
   (304640, [0, 5]),
   ((24371200 : Rat)/3, [1, 1, 1, 2]),
   (3046400, [1, 4]),
   ((6092800 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q2_39_cert : VectorCertificate (Tpow 2 (aLeft false (8 : ℤ) skM_E0_39)) skA_E0_Q2_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_2_join : VectorCertificate ([skA_E0_Q2_0, skA_E0_Q2_1, skA_E0_Q2_2, skA_E0_Q2_3, skA_E0_Q2_4, skA_E0_Q2_5, skA_E0_Q2_6, skA_E0_Q2_7, skA_E0_Q2_8, skA_E0_Q2_9, skA_E0_Q2_10, skA_E0_Q2_11, skA_E0_Q2_12, skA_E0_Q2_13, skA_E0_Q2_14, skA_E0_Q2_15, skA_E0_Q2_16, skA_E0_Q2_17, skA_E0_Q2_18, skA_E0_Q2_19, skA_E0_Q2_20, skA_E0_Q2_21, skA_E0_Q2_22, skA_E0_Q2_23, skA_E0_Q2_24, skA_E0_Q2_25, skA_E0_Q2_26, skA_E0_Q2_27, skA_E0_Q2_28, skA_E0_Q2_29, skA_E0_Q2_30, skA_E0_Q2_31, skA_E0_Q2_32, skA_E0_Q2_33, skA_E0_Q2_34, skA_E0_Q2_35, skA_E0_Q2_36, skA_E0_Q2_37, skA_E0_Q2_38, skA_E0_Q2_39] : List SectorVector).flatten skQ_E0_2 := by decide +kernel

theorem skQ_E0_2_val : evaluate skQ_E0_2 = evaluate (OrbSgl.vTerm false skY_E0 0 2) :=
  vTerm_of_chunks false skY_E0 0 2 (8 : ℤ) (by norm_num) skM_E0 [skA_E0_Q2_0, skA_E0_Q2_1, skA_E0_Q2_2, skA_E0_Q2_3, skA_E0_Q2_4, skA_E0_Q2_5, skA_E0_Q2_6, skA_E0_Q2_7, skA_E0_Q2_8, skA_E0_Q2_9, skA_E0_Q2_10, skA_E0_Q2_11, skA_E0_Q2_12, skA_E0_Q2_13, skA_E0_Q2_14, skA_E0_Q2_15, skA_E0_Q2_16, skA_E0_Q2_17, skA_E0_Q2_18, skA_E0_Q2_19, skA_E0_Q2_20, skA_E0_Q2_21, skA_E0_Q2_22, skA_E0_Q2_23, skA_E0_Q2_24, skA_E0_Q2_25, skA_E0_Q2_26, skA_E0_Q2_27, skA_E0_Q2_28, skA_E0_Q2_29, skA_E0_Q2_30, skA_E0_Q2_31, skA_E0_Q2_32, skA_E0_Q2_33, skA_E0_Q2_34, skA_E0_Q2_35, skA_E0_Q2_36, skA_E0_Q2_37, skA_E0_Q2_38, skA_E0_Q2_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q2_0_cert (List.Forall₂.cons skA_E0_Q2_1_cert (List.Forall₂.cons skA_E0_Q2_2_cert (List.Forall₂.cons skA_E0_Q2_3_cert (List.Forall₂.cons skA_E0_Q2_4_cert (List.Forall₂.cons skA_E0_Q2_5_cert (List.Forall₂.cons skA_E0_Q2_6_cert (List.Forall₂.cons skA_E0_Q2_7_cert (List.Forall₂.cons skA_E0_Q2_8_cert (List.Forall₂.cons skA_E0_Q2_9_cert (List.Forall₂.cons skA_E0_Q2_10_cert (List.Forall₂.cons skA_E0_Q2_11_cert (List.Forall₂.cons skA_E0_Q2_12_cert (List.Forall₂.cons skA_E0_Q2_13_cert (List.Forall₂.cons skA_E0_Q2_14_cert (List.Forall₂.cons skA_E0_Q2_15_cert (List.Forall₂.cons skA_E0_Q2_16_cert (List.Forall₂.cons skA_E0_Q2_17_cert (List.Forall₂.cons skA_E0_Q2_18_cert (List.Forall₂.cons skA_E0_Q2_19_cert (List.Forall₂.cons skA_E0_Q2_20_cert (List.Forall₂.cons skA_E0_Q2_21_cert (List.Forall₂.cons skA_E0_Q2_22_cert (List.Forall₂.cons skA_E0_Q2_23_cert (List.Forall₂.cons skA_E0_Q2_24_cert (List.Forall₂.cons skA_E0_Q2_25_cert (List.Forall₂.cons skA_E0_Q2_26_cert (List.Forall₂.cons skA_E0_Q2_27_cert (List.Forall₂.cons skA_E0_Q2_28_cert (List.Forall₂.cons skA_E0_Q2_29_cert (List.Forall₂.cons skA_E0_Q2_30_cert (List.Forall₂.cons skA_E0_Q2_31_cert (List.Forall₂.cons skA_E0_Q2_32_cert (List.Forall₂.cons skA_E0_Q2_33_cert (List.Forall₂.cons skA_E0_Q2_34_cert (List.Forall₂.cons skA_E0_Q2_35_cert (List.Forall₂.cons skA_E0_Q2_36_cert (List.Forall₂.cons skA_E0_Q2_37_cert (List.Forall₂.cons skA_E0_Q2_38_cert (List.Forall₂.cons skA_E0_Q2_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_2 skQ_E0_2_join

def skA_E0_Q3_0 : SectorVector := [(1,
  [((-2147483648 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((-536870912 : Rat)/189, [0, 1, 1, 3]),
   ((-1073741824 : Rat)/693, [0, 1, 2, 2]),
   ((-4294967296 : Rat)/3465, [0, 5]),
   ((-10737418240 : Rat)/2079, [1, 1, 1, 2]),
   ((-5368709120 : Rat)/693, [1, 4]),
   ((-1073741824 : Rat)/297, [2, 3])]),
 (-1,
  [((2147483648 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((536870912 : Rat)/189, [0, 1, 1, 3]),
   ((1073741824 : Rat)/693, [0, 1, 2, 2]),
   ((4294967296 : Rat)/3465, [0, 5]),
   ((-10737418240 : Rat)/2079, [1, 1, 1, 2]),
   ((-5368709120 : Rat)/693, [1, 4]),
   ((-1073741824 : Rat)/297, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_0_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_0)) skA_E0_Q3_0 := by decide +kernel

def skA_E0_Q3_1 : SectorVector := [(1,
  [((134217728 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-570425344 : Rat)/27, [0, 1, 1, 3]),
   ((-67108864 : Rat)/9, [0, 1, 2, 2]),
   ((-134217728 : Rat)/9, [0, 5]),
   ((134217728 : Rat)/27, [1, 1, 1, 2]),
   ((-738197504 : Rat)/9, [1, 4]),
   ((-872415232 : Rat)/27, [2, 3])]),
 (-1,
  [((-134217728 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((570425344 : Rat)/27, [0, 1, 1, 3]),
   ((67108864 : Rat)/9, [0, 1, 2, 2]),
   ((134217728 : Rat)/9, [0, 5]),
   ((134217728 : Rat)/27, [1, 1, 1, 2]),
   ((-738197504 : Rat)/9, [1, 4]),
   ((-872415232 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_1_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_1)) skA_E0_Q3_1 := by decide +kernel

def skA_E0_Q3_2 : SectorVector := [(1,
  [((134217728 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-167772160 : Rat)/7, [0, 1, 1, 3]),
   ((-201326592 : Rat)/7, [0, 5]),
   ((671088640 : Rat)/7, [1, 1, 1, 2]),
   ((-1006632960 : Rat)/7, [1, 4]),
   ((-335544320 : Rat)/7, [2, 3])]),
 (-1,
  [((-134217728 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((167772160 : Rat)/7, [0, 1, 1, 3]),
   ((201326592 : Rat)/7, [0, 5]),
   ((671088640 : Rat)/7, [1, 1, 1, 2]),
   ((-1006632960 : Rat)/7, [1, 4]),
   ((-335544320 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_2_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_2)) skA_E0_Q3_2 := by decide +kernel

def skA_E0_Q3_3 : SectorVector := [(1,
  [((-6291456 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (7864320, [0, 1, 1, 3]),
   (3145728, [0, 1, 2, 2]),
   ((25165824 : Rat)/5, [0, 5]),
   (2097152, [1, 1, 1, 2]),
   (28311552, [1, 4]),
   (11534336, [2, 3])]),
 (-1,
  [((6291456 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-7864320, [0, 1, 1, 3]),
   (-3145728, [0, 1, 2, 2]),
   ((-25165824 : Rat)/5, [0, 5]),
   (2097152, [1, 1, 1, 2]),
   (28311552, [1, 4]),
   (11534336, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_3_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_3)) skA_E0_Q3_3 := by decide +kernel

def skA_E0_Q3_4 : SectorVector := [(1,
  [(1572864, [0, 1, 1, 1, 1, 1]),
   (-25559040, [0, 1, 1, 3]),
   (-11796480, [0, 1, 2, 2]),
   (-14155776, [0, 5]),
   (-23592960, [1, 1, 1, 2]),
   (-82575360, [1, 4]),
   (-35389440, [2, 3])]),
 (-1,
  [(-1572864, [0, 1, 1, 1, 1, 1]),
   (25559040, [0, 1, 1, 3]),
   (11796480, [0, 1, 2, 2]),
   (14155776, [0, 5]),
   (-23592960, [1, 1, 1, 2]),
   (-82575360, [1, 4]),
   (-35389440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_4_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_4)) skA_E0_Q3_4 := by decide +kernel

def skA_E0_Q3_5 : SectorVector := [(1,
  [((11534336 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-256638976 : Rat)/9, [0, 1, 1, 3]),
   ((-40370176 : Rat)/3, [0, 1, 2, 2]),
   ((-46137344 : Rat)/3, [0, 5]),
   ((-265289728 : Rat)/9, [1, 1, 1, 2]),
   ((-271056896 : Rat)/3, [1, 4]),
   ((-351797248 : Rat)/9, [2, 3])]),
 (-1,
  [((-11534336 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((256638976 : Rat)/9, [0, 1, 1, 3]),
   ((40370176 : Rat)/3, [0, 1, 2, 2]),
   ((46137344 : Rat)/3, [0, 5]),
   ((-265289728 : Rat)/9, [1, 1, 1, 2]),
   ((-271056896 : Rat)/3, [1, 4]),
   ((-351797248 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_5_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_5)) skA_E0_Q3_5 := by decide +kernel

def skA_E0_Q3_6 : SectorVector := [(1,
  [(-19922944, [0, 1, 1, 1, 1, 1]),
   (-154402816, [0, 1, 1, 3]),
   (-89653248, [0, 1, 2, 2]),
   (-59768832, [0, 5]),
   (-338690048, [1, 1, 1, 2]),
   (-388497408, [1, 4]),
   (-189267968, [2, 3])]),
 (-1,
  [(19922944, [0, 1, 1, 1, 1, 1]),
   (154402816, [0, 1, 1, 3]),
   (89653248, [0, 1, 2, 2]),
   (59768832, [0, 5]),
   (-338690048, [1, 1, 1, 2]),
   (-388497408, [1, 4]),
   (-189267968, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_6_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_6)) skA_E0_Q3_6 := by decide +kernel

def skA_E0_Q3_7 : SectorVector := [(1,
  [((5111808 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((70287360 : Rat)/7, [0, 1, 1, 3]),
   ((38338560 : Rat)/7, [0, 1, 2, 2]),
   ((30670848 : Rat)/7, [0, 5]),
   ((127795200 : Rat)/7, [1, 1, 1, 2]),
   ((191692800 : Rat)/7, [1, 4]),
   (12779520, [2, 3])]),
 (-1,
  [((-5111808 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-70287360 : Rat)/7, [0, 1, 1, 3]),
   ((-38338560 : Rat)/7, [0, 1, 2, 2]),
   ((-30670848 : Rat)/7, [0, 5]),
   ((127795200 : Rat)/7, [1, 1, 1, 2]),
   ((191692800 : Rat)/7, [1, 4]),
   (12779520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_7_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_7)) skA_E0_Q3_7 := by decide +kernel

def skA_E0_Q3_8 : SectorVector := [(1,
  [(-23592960, [0, 1, 1, 1, 1, 1]),
   (-41287680, [0, 1, 1, 3]),
   (-35389440, [0, 1, 2, 2]),
   (-212336640, [1, 1, 1, 2]),
   (-35389440, [1, 4]),
   (-35389440, [2, 3])]),
 (-1,
  [(23592960, [0, 1, 1, 1, 1, 1]),
   (41287680, [0, 1, 1, 3]),
   (35389440, [0, 1, 2, 2]),
   (-212336640, [1, 1, 1, 2]),
   (-35389440, [1, 4]),
   (-35389440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_8_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_8)) skA_E0_Q3_8 := by decide +kernel

def skA_E0_Q3_9 : SectorVector := [(1,
  [(23592960, [0, 1, 1, 1, 1, 1]),
   (112066560, [0, 1, 1, 3]),
   (70778880, [0, 1, 2, 2]),
   (35389440, [0, 5]),
   (306708480, [1, 1, 1, 2]),
   (247726080, [1, 4]),
   (129761280, [2, 3])]),
 (-1,
  [(-23592960, [0, 1, 1, 1, 1, 1]),
   (-112066560, [0, 1, 1, 3]),
   (-70778880, [0, 1, 2, 2]),
   (-35389440, [0, 5]),
   (306708480, [1, 1, 1, 2]),
   (247726080, [1, 4]),
   (129761280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_9_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_9)) skA_E0_Q3_9 := by decide +kernel

def skA_E0_Q3_10 : SectorVector := [(1,
  [(23986176, [0, 1, 1, 1, 1, 1]),
   (137920512, [0, 1, 1, 3]),
   (83951616, [0, 1, 2, 2]),
   (47972352, [0, 5]),
   (343801856, [1, 1, 1, 2]),
   (323813376, [1, 4]),
   (163905536, [2, 3])]),
 (-1,
  [(-23986176, [0, 1, 1, 1, 1, 1]),
   (-137920512, [0, 1, 1, 3]),
   (-83951616, [0, 1, 2, 2]),
   (-47972352, [0, 5]),
   (343801856, [1, 1, 1, 2]),
   (323813376, [1, 4]),
   (163905536, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_10_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_10)) skA_E0_Q3_10 := by decide +kernel

def skA_E0_Q3_11 : SectorVector := [(1,
  [(11796480, [0, 1, 1, 1, 1, 1]),
   (67829760, [0, 1, 1, 3]),
   (41287680, [0, 1, 2, 2]),
   (23592960, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (159252480, [1, 4]),
   (80609280, [2, 3])]),
 (-1,
  [(-11796480, [0, 1, 1, 1, 1, 1]),
   (-67829760, [0, 1, 1, 3]),
   (-41287680, [0, 1, 2, 2]),
   (-23592960, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (159252480, [1, 4]),
   (80609280, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_11_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_11)) skA_E0_Q3_11 := by decide +kernel

def skA_E0_Q3_12 : SectorVector := [(1,
  [(31358976, [0, 1, 1, 1, 1, 1]),
   (89088000, [0, 1, 1, 3]),
   (64143360, [0, 1, 2, 2]),
   (17104896, [0, 5]),
   (327843840, [1, 1, 1, 2]),
   (149667840, [1, 4]),
   (92651520, [2, 3])]),
 (-1,
  [(-31358976, [0, 1, 1, 1, 1, 1]),
   (-89088000, [0, 1, 1, 3]),
   (-64143360, [0, 1, 2, 2]),
   (-17104896, [0, 5]),
   (327843840, [1, 1, 1, 2]),
   (149667840, [1, 4]),
   (92651520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_12_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_12)) skA_E0_Q3_12 := by decide +kernel

def skA_E0_Q3_13 : SectorVector := [(1,
  [(29736960, [0, 1, 1, 1, 1, 1]),
   (100700160, [0, 1, 1, 3]),
   (68935680, [0, 1, 2, 2]),
   (24330240, [0, 5]),
   (332513280, [1, 1, 1, 2]),
   (190586880, [1, 4]),
   (109486080, [2, 3])]),
 (-1,
  [(-29736960, [0, 1, 1, 1, 1, 1]),
   (-100700160, [0, 1, 1, 3]),
   (-68935680, [0, 1, 2, 2]),
   (-24330240, [0, 5]),
   (332513280, [1, 1, 1, 2]),
   (190586880, [1, 4]),
   (109486080, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_13_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_13)) skA_E0_Q3_13 := by decide +kernel

def skA_E0_Q3_14 : SectorVector := [(1,
  [((7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((28344320 : Rat)/27, [0, 1, 1, 3]),
   ((6225920 : Rat)/9, [0, 1, 2, 2]),
   ((2621440 : Rat)/9, [0, 5]),
   ((85852160 : Rat)/27, [1, 1, 1, 2]),
   ((19333120 : Rat)/9, [1, 4]),
   ((31784960 : Rat)/27, [2, 3])]),
 (-1,
  [((-7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-28344320 : Rat)/27, [0, 1, 1, 3]),
   ((-6225920 : Rat)/9, [0, 1, 2, 2]),
   ((-2621440 : Rat)/9, [0, 5]),
   ((85852160 : Rat)/27, [1, 1, 1, 2]),
   ((19333120 : Rat)/9, [1, 4]),
   ((31784960 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_14_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_14)) skA_E0_Q3_14 := by decide +kernel

def skA_E0_Q3_15 : SectorVector := [(1,
  [((-62627840 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-246241280 : Rat)/3, [0, 1, 1, 3]),
   (-54087680, [0, 1, 2, 2]),
   (-22773760, [0, 5]),
   ((-745840640 : Rat)/3, [1, 1, 1, 2]),
   (-167956480, [1, 4]),
   ((-276131840 : Rat)/3, [2, 3])]),
 (-1,
  [((62627840 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((246241280 : Rat)/3, [0, 1, 1, 3]),
   (54087680, [0, 1, 2, 2]),
   (22773760, [0, 5]),
   ((-745840640 : Rat)/3, [1, 1, 1, 2]),
   (-167956480, [1, 4]),
   ((-276131840 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_15_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_15)) skA_E0_Q3_15 := by decide +kernel

def skA_E0_Q3_16 : SectorVector := [(1,
  [(-2088960, [0, 1, 1, 1, 1, 1]),
   (-4392960, [0, 1, 1, 3]),
   (-3502080, [0, 1, 2, 2]),
   (-368640, [0, 5]),
   (-19783680, [1, 1, 1, 2]),
   (-5345280, [1, 4]),
   (-4116480, [2, 3])]),
 (-1,
  [(2088960, [0, 1, 1, 1, 1, 1]),
   (4392960, [0, 1, 1, 3]),
   (3502080, [0, 1, 2, 2]),
   (368640, [0, 5]),
   (-19783680, [1, 1, 1, 2]),
   (-5345280, [1, 4]),
   (-4116480, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_16_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_16)) skA_E0_Q3_16 := by decide +kernel

def skA_E0_Q3_17 : SectorVector := [(1,
  [(-18104320, [0, 1, 1, 1, 1, 1]),
   (-44462080, [0, 1, 1, 3]),
   (-33546240, [0, 1, 2, 2]),
   (-6389760, [0, 5]),
   (-179978240, [1, 1, 1, 2]),
   (-65495040, [1, 4]),
   (-44195840, [2, 3])]),
 (-1,
  [(18104320, [0, 1, 1, 1, 1, 1]),
   (44462080, [0, 1, 1, 3]),
   (33546240, [0, 1, 2, 2]),
   (6389760, [0, 5]),
   (-179978240, [1, 1, 1, 2]),
   (-65495040, [1, 4]),
   (-44195840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_17_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_17)) skA_E0_Q3_17 := by decide +kernel

def skA_E0_Q3_18 : SectorVector := [(1,
  [(3133440, [0, 1, 1, 1, 1, 1]),
   (8801280, [0, 1, 1, 3]),
   (6359040, [0, 1, 2, 2]),
   (1658880, [0, 5]),
   (32624640, [1, 1, 1, 2]),
   (14653440, [1, 4]),
   (9123840, [2, 3])]),
 (-1,
  [(-3133440, [0, 1, 1, 1, 1, 1]),
   (-8801280, [0, 1, 1, 3]),
   (-6359040, [0, 1, 2, 2]),
   (-1658880, [0, 5]),
   (32624640, [1, 1, 1, 2]),
   (14653440, [1, 4]),
   (9123840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_18_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_18)) skA_E0_Q3_18 := by decide +kernel

def skA_E0_Q3_19 : SectorVector := [(1,
  [(29245440, [0, 1, 1, 1, 1, 1]),
   (92467200, [0, 1, 1, 3]),
   (64512000, [0, 1, 2, 2]),
   (20643840, [0, 5]),
   (318259200, [1, 1, 1, 2]),
   (167731200, [1, 4]),
   (98918400, [2, 3])]),
 (-1,
  [(-29245440, [0, 1, 1, 1, 1, 1]),
   (-92467200, [0, 1, 1, 3]),
   (-64512000, [0, 1, 2, 2]),
   (-20643840, [0, 5]),
   (318259200, [1, 1, 1, 2]),
   (167731200, [1, 4]),
   (98918400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_19_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_19)) skA_E0_Q3_19 := by decide +kernel

def skA_E0_Q3_20 : SectorVector := [(1,
  [(38123520, [0, 1, 1, 1, 1, 1]),
   (120537600, [0, 1, 1, 3]),
   (84096000, [0, 1, 2, 2]),
   (26910720, [0, 5]),
   (414873600, [1, 1, 1, 2]),
   (218649600, [1, 4]),
   (128947200, [2, 3])]),
 (-1,
  [(-38123520, [0, 1, 1, 1, 1, 1]),
   (-120537600, [0, 1, 1, 3]),
   (-84096000, [0, 1, 2, 2]),
   (-26910720, [0, 5]),
   (414873600, [1, 1, 1, 2]),
   (218649600, [1, 4]),
   (128947200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_20_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_20)) skA_E0_Q3_20 := by decide +kernel

def skA_E0_Q3_21 : SectorVector := [(1,
  [((100896768 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (63802368, [0, 1, 1, 3]),
   (44513280, [0, 1, 2, 2]),
   ((71221248 : Rat)/5, [0, 5]),
   (219598848, [1, 1, 1, 2]),
   (115734528, [1, 4]),
   (68253696, [2, 3])]),
 (-1,
  [((-100896768 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-63802368, [0, 1, 1, 3]),
   (-44513280, [0, 1, 2, 2]),
   ((-71221248 : Rat)/5, [0, 5]),
   (219598848, [1, 1, 1, 2]),
   (115734528, [1, 4]),
   (68253696, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_21_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_21)) skA_E0_Q3_21 := by decide +kernel

def skA_E0_Q3_22 : SectorVector := [(1,
  [(-11796480, [0, 1, 1, 1, 1, 1]),
   (-20643840, [0, 1, 1, 3]),
   (-17694720, [0, 1, 2, 2]),
   (-106168320, [1, 1, 1, 2]),
   (-17694720, [1, 4]),
   (-17694720, [2, 3])]),
 (-1,
  [(11796480, [0, 1, 1, 1, 1, 1]),
   (20643840, [0, 1, 1, 3]),
   (17694720, [0, 1, 2, 2]),
   (-106168320, [1, 1, 1, 2]),
   (-17694720, [1, 4]),
   (-17694720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_22_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_22)) skA_E0_Q3_22 := by decide +kernel

def skA_E0_Q3_23 : SectorVector := [(1,
  [((121651200 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((273715200 : Rat)/7, [0, 1, 1, 3]),
   (30412800, [0, 1, 2, 2]),
   ((30412800 : Rat)/7, [0, 5]),
   ((1175961600 : Rat)/7, [1, 1, 1, 2]),
   ((364953600 : Rat)/7, [1, 4]),
   ((263577600 : Rat)/7, [2, 3])]),
 (-1,
  [((-121651200 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-273715200 : Rat)/7, [0, 1, 1, 3]),
   (-30412800, [0, 1, 2, 2]),
   ((-30412800 : Rat)/7, [0, 5]),
   ((1175961600 : Rat)/7, [1, 1, 1, 2]),
   ((364953600 : Rat)/7, [1, 4]),
   ((263577600 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_23_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_23)) skA_E0_Q3_23 := by decide +kernel

def skA_E0_Q3_24 : SectorVector := [(1,
  [(38338560, [0, 1, 1, 1, 1, 1]),
   (95846400, [0, 1, 1, 3]),
   (71884800, [0, 1, 2, 2]),
   (14376960, [0, 5]),
   (383385600, [1, 1, 1, 2]),
   (143769600, [1, 4]),
   (95846400, [2, 3])]),
 (-1,
  [(-38338560, [0, 1, 1, 1, 1, 1]),
   (-95846400, [0, 1, 1, 3]),
   (-71884800, [0, 1, 2, 2]),
   (-14376960, [0, 5]),
   (383385600, [1, 1, 1, 2]),
   (143769600, [1, 4]),
   (95846400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_24_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_24)) skA_E0_Q3_24 := by decide +kernel

def skA_E0_Q3_25 : SectorVector := [(1,
  [(38486016, [0, 1, 1, 1, 1, 1]),
   (96215040, [0, 1, 1, 3]),
   (72161280, [0, 1, 2, 2]),
   (14432256, [0, 5]),
   (384860160, [1, 1, 1, 2]),
   (144322560, [1, 4]),
   (96215040, [2, 3])]),
 (-1,
  [(-38486016, [0, 1, 1, 1, 1, 1]),
   (-96215040, [0, 1, 1, 3]),
   (-72161280, [0, 1, 2, 2]),
   (-14432256, [0, 5]),
   (384860160, [1, 1, 1, 2]),
   (144322560, [1, 4]),
   (96215040, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_25_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_25)) skA_E0_Q3_25 := by decide +kernel

def skA_E0_Q3_26 : SectorVector := [(1,
  [(12189696, [0, 1, 1, 1, 1, 1]),
   (33521664, [0, 1, 1, 3]),
   (24379392, [0, 1, 2, 2]),
   (6094848, [0, 5]),
   (125960192, [1, 1, 1, 2]),
   (54853632, [1, 4]),
   (34537472, [2, 3])]),
 (-1,
  [(-12189696, [0, 1, 1, 1, 1, 1]),
   (-33521664, [0, 1, 1, 3]),
   (-24379392, [0, 1, 2, 2]),
   (-6094848, [0, 5]),
   (125960192, [1, 1, 1, 2]),
   (54853632, [1, 4]),
   (34537472, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_26_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_26)) skA_E0_Q3_26 := by decide +kernel

def skA_E0_Q3_27 : SectorVector := [(1,
  [(10321920, [0, 1, 1, 1, 1, 1]),
   (28385280, [0, 1, 1, 3]),
   (20643840, [0, 1, 2, 2]),
   (5160960, [0, 5]),
   (106659840, [1, 1, 1, 2]),
   (46448640, [1, 4]),
   (29245440, [2, 3])]),
 (-1,
  [(-10321920, [0, 1, 1, 1, 1, 1]),
   (-28385280, [0, 1, 1, 3]),
   (-20643840, [0, 1, 2, 2]),
   (-5160960, [0, 5]),
   (106659840, [1, 1, 1, 2]),
   (46448640, [1, 4]),
   (29245440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_27_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_27)) skA_E0_Q3_27 := by decide +kernel

def skA_E0_Q3_28 : SectorVector := [(1,
  [((-213995520 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   (-53498880, [0, 1, 1, 3]),
   ((-427991040 : Rat)/11, [0, 1, 2, 2]),
   ((-106997760 : Rat)/11, [0, 5]),
   ((-2211287040 : Rat)/11, [1, 1, 1, 2]),
   ((-962979840 : Rat)/11, [1, 4]),
   ((-606320640 : Rat)/11, [2, 3])]),
 (-1,
  [((213995520 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   (53498880, [0, 1, 1, 3]),
   ((427991040 : Rat)/11, [0, 1, 2, 2]),
   ((106997760 : Rat)/11, [0, 5]),
   ((-2211287040 : Rat)/11, [1, 1, 1, 2]),
   ((-962979840 : Rat)/11, [1, 4]),
   ((-606320640 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_28_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_28)) skA_E0_Q3_28 := by decide +kernel

def skA_E0_Q3_29 : SectorVector := [(1,
  [(-524288, [0, 1, 1, 1, 1, 1]),
   (-720896, [0, 1, 1, 3]),
   (-688128, [0, 1, 2, 2]),
   (98304, [0, 5]),
   (-4456448, [1, 1, 1, 2]),
   (-196608, [1, 4]),
   (-524288, [2, 3])]),
 (-1,
  [(524288, [0, 1, 1, 1, 1, 1]),
   (720896, [0, 1, 1, 3]),
   (688128, [0, 1, 2, 2]),
   (-98304, [0, 5]),
   (-4456448, [1, 1, 1, 2]),
   (-196608, [1, 4]),
   (-524288, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_29_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_29)) skA_E0_Q3_29 := by decide +kernel

def skA_E0_Q3_30 : SectorVector := [(1,
  [(4096000, [0, 1, 1, 1, 1, 1]),
   (7936000, [0, 1, 1, 3]),
   (6528000, [0, 1, 2, 2]),
   (384000, [0, 5]),
   (37888000, [1, 1, 1, 2]),
   (8448000, [1, 4]),
   (7168000, [2, 3])]),
 (-1,
  [(-4096000, [0, 1, 1, 1, 1, 1]),
   (-7936000, [0, 1, 1, 3]),
   (-6528000, [0, 1, 2, 2]),
   (-384000, [0, 5]),
   (37888000, [1, 1, 1, 2]),
   (8448000, [1, 4]),
   (7168000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_30_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_30)) skA_E0_Q3_30 := by decide +kernel

def skA_E0_Q3_31 : SectorVector := [(1,
  [(8454144, [0, 1, 1, 1, 1, 1]),
   (17965056, [0, 1, 1, 3]),
   (14266368, [0, 1, 2, 2]),
   (1585152, [0, 5]),
   (80314368, [1, 1, 1, 2]),
   (22192128, [1, 4]),
   (16908288, [2, 3])]),
 (-1,
  [(-8454144, [0, 1, 1, 1, 1, 1]),
   (-17965056, [0, 1, 1, 3]),
   (-14266368, [0, 1, 2, 2]),
   (-1585152, [0, 5]),
   (80314368, [1, 1, 1, 2]),
   (22192128, [1, 4]),
   (16908288, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_31_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_31)) skA_E0_Q3_31 := by decide +kernel

def skA_E0_Q3_32 : SectorVector := [(1,
  [(3686400, [0, 1, 1, 1, 1, 1]),
   (7833600, [0, 1, 1, 3]),
   (6220800, [0, 1, 2, 2]),
   (691200, [0, 5]),
   (35020800, [1, 1, 1, 2]),
   (9676800, [1, 4]),
   (7372800, [2, 3])]),
 (-1,
  [(-3686400, [0, 1, 1, 1, 1, 1]),
   (-7833600, [0, 1, 1, 3]),
   (-6220800, [0, 1, 2, 2]),
   (-691200, [0, 5]),
   (35020800, [1, 1, 1, 2]),
   (9676800, [1, 4]),
   (7372800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_32_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_32)) skA_E0_Q3_32 := by decide +kernel

def skA_E0_Q3_33 : SectorVector := [(1,
  [(3932160, [0, 1, 1, 1, 1, 1]),
   (9093120, [0, 1, 1, 3]),
   (7004160, [0, 1, 2, 2]),
   (1105920, [0, 5]),
   (38338560, [1, 1, 1, 2]),
   (12533760, [1, 4]),
   (8847360, [2, 3])]),
 (-1,
  [(-3932160, [0, 1, 1, 1, 1, 1]),
   (-9093120, [0, 1, 1, 3]),
   (-7004160, [0, 1, 2, 2]),
   (-1105920, [0, 5]),
   (38338560, [1, 1, 1, 2]),
   (12533760, [1, 4]),
   (8847360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_33_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_33)) skA_E0_Q3_33 := by decide +kernel

def skA_E0_Q3_34 : SectorVector := [(1,
  [(-5087232, [0, 1, 1, 1, 1, 1]),
   (-11764224, [0, 1, 1, 3]),
   (-9061632, [0, 1, 2, 2]),
   (-1430784, [0, 5]),
   (-49600512, [1, 1, 1, 2]),
   (-16215552, [1, 4]),
   (-11446272, [2, 3])]),
 (-1,
  [(5087232, [0, 1, 1, 1, 1, 1]),
   (11764224, [0, 1, 1, 3]),
   (9061632, [0, 1, 2, 2]),
   (1430784, [0, 5]),
   (-49600512, [1, 1, 1, 2]),
   (-16215552, [1, 4]),
   (-11446272, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_34_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_34)) skA_E0_Q3_34 := by decide +kernel

def skA_E0_Q3_35 : SectorVector := [(1,
  [((3604480 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((9011200 : Rat)/27, [0, 1, 1, 3]),
   ((2252800 : Rat)/9, [0, 1, 2, 2]),
   ((450560 : Rat)/9, [0, 5]),
   ((36044800 : Rat)/27, [1, 1, 1, 2]),
   ((4505600 : Rat)/9, [1, 4]),
   ((9011200 : Rat)/27, [2, 3])]),
 (-1,
  [((-3604480 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-9011200 : Rat)/27, [0, 1, 1, 3]),
   ((-2252800 : Rat)/9, [0, 1, 2, 2]),
   ((-450560 : Rat)/9, [0, 5]),
   ((36044800 : Rat)/27, [1, 1, 1, 2]),
   ((4505600 : Rat)/9, [1, 4]),
   ((9011200 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_35_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_35)) skA_E0_Q3_35 := by decide +kernel

def skA_E0_Q3_36 : SectorVector := [(1,
  [((3031040 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((7577600 : Rat)/3, [0, 1, 1, 3]),
   (1894400, [0, 1, 2, 2]),
   (378880, [0, 5]),
   ((30310400 : Rat)/3, [1, 1, 1, 2]),
   (3788800, [1, 4]),
   ((7577600 : Rat)/3, [2, 3])]),
 (-1,
  [((-3031040 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-7577600 : Rat)/3, [0, 1, 1, 3]),
   (-1894400, [0, 1, 2, 2]),
   (-378880, [0, 5]),
   ((30310400 : Rat)/3, [1, 1, 1, 2]),
   (3788800, [1, 4]),
   ((7577600 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_36_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_36)) skA_E0_Q3_36 := by decide +kernel

def skA_E0_Q3_37 : SectorVector := [(1,
  [(3502080, [0, 1, 1, 1, 1, 1]),
   (8755200, [0, 1, 1, 3]),
   (6566400, [0, 1, 2, 2]),
   (1313280, [0, 5]),
   (35020800, [1, 1, 1, 2]),
   (13132800, [1, 4]),
   (8755200, [2, 3])]),
 (-1,
  [(-3502080, [0, 1, 1, 1, 1, 1]),
   (-8755200, [0, 1, 1, 3]),
   (-6566400, [0, 1, 2, 2]),
   (-1313280, [0, 5]),
   (35020800, [1, 1, 1, 2]),
   (13132800, [1, 4]),
   (8755200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_37_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_37)) skA_E0_Q3_37 := by decide +kernel

def skA_E0_Q3_38 : SectorVector := [(1,
  [(4571136, [0, 1, 1, 1, 1, 1]),
   (11427840, [0, 1, 1, 3]),
   (8570880, [0, 1, 2, 2]),
   (1714176, [0, 5]),
   (45711360, [1, 1, 1, 2]),
   (17141760, [1, 4]),
   (11427840, [2, 3])]),
 (-1,
  [(-4571136, [0, 1, 1, 1, 1, 1]),
   (-11427840, [0, 1, 1, 3]),
   (-8570880, [0, 1, 2, 2]),
   (-1714176, [0, 5]),
   (45711360, [1, 1, 1, 2]),
   (17141760, [1, 4]),
   (11427840, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_38_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_38)) skA_E0_Q3_38 := by decide +kernel

def skA_E0_Q3_39 : SectorVector := [(1,
  [(2437120, [0, 1, 1, 1, 1, 1]),
   (6092800, [0, 1, 1, 3]),
   (4569600, [0, 1, 2, 2]),
   (913920, [0, 5]),
   (24371200, [1, 1, 1, 2]),
   (9139200, [1, 4]),
   (6092800, [2, 3])]),
 (-1,
  [(-2437120, [0, 1, 1, 1, 1, 1]),
   (-6092800, [0, 1, 1, 3]),
   (-4569600, [0, 1, 2, 2]),
   (-913920, [0, 5]),
   (24371200, [1, 1, 1, 2]),
   (9139200, [1, 4]),
   (6092800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q3_39_cert : VectorCertificate (Tpow 3 (aLeft false (9 : ℤ) skM_E0_39)) skA_E0_Q3_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_3_join : VectorCertificate ([skA_E0_Q3_0, skA_E0_Q3_1, skA_E0_Q3_2, skA_E0_Q3_3, skA_E0_Q3_4, skA_E0_Q3_5, skA_E0_Q3_6, skA_E0_Q3_7, skA_E0_Q3_8, skA_E0_Q3_9, skA_E0_Q3_10, skA_E0_Q3_11, skA_E0_Q3_12, skA_E0_Q3_13, skA_E0_Q3_14, skA_E0_Q3_15, skA_E0_Q3_16, skA_E0_Q3_17, skA_E0_Q3_18, skA_E0_Q3_19, skA_E0_Q3_20, skA_E0_Q3_21, skA_E0_Q3_22, skA_E0_Q3_23, skA_E0_Q3_24, skA_E0_Q3_25, skA_E0_Q3_26, skA_E0_Q3_27, skA_E0_Q3_28, skA_E0_Q3_29, skA_E0_Q3_30, skA_E0_Q3_31, skA_E0_Q3_32, skA_E0_Q3_33, skA_E0_Q3_34, skA_E0_Q3_35, skA_E0_Q3_36, skA_E0_Q3_37, skA_E0_Q3_38, skA_E0_Q3_39] : List SectorVector).flatten skQ_E0_3 := by decide +kernel

theorem skQ_E0_3_val : evaluate skQ_E0_3 = evaluate (OrbSgl.vTerm false skY_E0 0 3) :=
  vTerm_of_chunks false skY_E0 0 3 (9 : ℤ) (by norm_num) skM_E0 [skA_E0_Q3_0, skA_E0_Q3_1, skA_E0_Q3_2, skA_E0_Q3_3, skA_E0_Q3_4, skA_E0_Q3_5, skA_E0_Q3_6, skA_E0_Q3_7, skA_E0_Q3_8, skA_E0_Q3_9, skA_E0_Q3_10, skA_E0_Q3_11, skA_E0_Q3_12, skA_E0_Q3_13, skA_E0_Q3_14, skA_E0_Q3_15, skA_E0_Q3_16, skA_E0_Q3_17, skA_E0_Q3_18, skA_E0_Q3_19, skA_E0_Q3_20, skA_E0_Q3_21, skA_E0_Q3_22, skA_E0_Q3_23, skA_E0_Q3_24, skA_E0_Q3_25, skA_E0_Q3_26, skA_E0_Q3_27, skA_E0_Q3_28, skA_E0_Q3_29, skA_E0_Q3_30, skA_E0_Q3_31, skA_E0_Q3_32, skA_E0_Q3_33, skA_E0_Q3_34, skA_E0_Q3_35, skA_E0_Q3_36, skA_E0_Q3_37, skA_E0_Q3_38, skA_E0_Q3_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q3_0_cert (List.Forall₂.cons skA_E0_Q3_1_cert (List.Forall₂.cons skA_E0_Q3_2_cert (List.Forall₂.cons skA_E0_Q3_3_cert (List.Forall₂.cons skA_E0_Q3_4_cert (List.Forall₂.cons skA_E0_Q3_5_cert (List.Forall₂.cons skA_E0_Q3_6_cert (List.Forall₂.cons skA_E0_Q3_7_cert (List.Forall₂.cons skA_E0_Q3_8_cert (List.Forall₂.cons skA_E0_Q3_9_cert (List.Forall₂.cons skA_E0_Q3_10_cert (List.Forall₂.cons skA_E0_Q3_11_cert (List.Forall₂.cons skA_E0_Q3_12_cert (List.Forall₂.cons skA_E0_Q3_13_cert (List.Forall₂.cons skA_E0_Q3_14_cert (List.Forall₂.cons skA_E0_Q3_15_cert (List.Forall₂.cons skA_E0_Q3_16_cert (List.Forall₂.cons skA_E0_Q3_17_cert (List.Forall₂.cons skA_E0_Q3_18_cert (List.Forall₂.cons skA_E0_Q3_19_cert (List.Forall₂.cons skA_E0_Q3_20_cert (List.Forall₂.cons skA_E0_Q3_21_cert (List.Forall₂.cons skA_E0_Q3_22_cert (List.Forall₂.cons skA_E0_Q3_23_cert (List.Forall₂.cons skA_E0_Q3_24_cert (List.Forall₂.cons skA_E0_Q3_25_cert (List.Forall₂.cons skA_E0_Q3_26_cert (List.Forall₂.cons skA_E0_Q3_27_cert (List.Forall₂.cons skA_E0_Q3_28_cert (List.Forall₂.cons skA_E0_Q3_29_cert (List.Forall₂.cons skA_E0_Q3_30_cert (List.Forall₂.cons skA_E0_Q3_31_cert (List.Forall₂.cons skA_E0_Q3_32_cert (List.Forall₂.cons skA_E0_Q3_33_cert (List.Forall₂.cons skA_E0_Q3_34_cert (List.Forall₂.cons skA_E0_Q3_35_cert (List.Forall₂.cons skA_E0_Q3_36_cert (List.Forall₂.cons skA_E0_Q3_37_cert (List.Forall₂.cons skA_E0_Q3_38_cert (List.Forall₂.cons skA_E0_Q3_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_3 skQ_E0_3_join

def skA_E0_Q4_0 : SectorVector := [(-1,
  [((-34359738368 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((-17179869184 : Rat)/2079, [0, 1, 1, 3]),
   ((-4294967296 : Rat)/693, [0, 1, 2, 2]),
   ((-4294967296 : Rat)/3465, [0, 5]),
   ((68719476736 : Rat)/2079, [1, 1, 1, 2]),
   ((8589934592 : Rat)/693, [1, 4]),
   ((17179869184 : Rat)/2079, [2, 3])]),
 (1,
  [((34359738368 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((17179869184 : Rat)/2079, [0, 1, 1, 3]),
   ((4294967296 : Rat)/693, [0, 1, 2, 2]),
   ((4294967296 : Rat)/3465, [0, 5]),
   ((68719476736 : Rat)/2079, [1, 1, 1, 2]),
   ((8589934592 : Rat)/693, [1, 4]),
   ((17179869184 : Rat)/2079, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_0_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_0)) skA_E0_Q4_0 := by decide +kernel

def skA_E0_Q4_1 : SectorVector := [(-1,
  [((-268435456 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-671088640 : Rat)/27, [0, 1, 1, 3]),
   ((-167772160 : Rat)/9, [0, 1, 2, 2]),
   ((-33554432 : Rat)/9, [0, 5]),
   ((2684354560 : Rat)/27, [1, 1, 1, 2]),
   ((335544320 : Rat)/9, [1, 4]),
   ((671088640 : Rat)/27, [2, 3])]),
 (1,
  [((268435456 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((671088640 : Rat)/27, [0, 1, 1, 3]),
   ((167772160 : Rat)/9, [0, 1, 2, 2]),
   ((33554432 : Rat)/9, [0, 5]),
   ((2684354560 : Rat)/27, [1, 1, 1, 2]),
   ((335544320 : Rat)/9, [1, 4]),
   ((671088640 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_1_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_1)) skA_E0_Q4_1 := by decide +kernel

def skA_E0_Q4_2 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_2_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_2)) skA_E0_Q4_2 := by decide +kernel

def skA_E0_Q4_3 : SectorVector := [(-1,
  [((-16777216 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-8388608, [0, 1, 1, 3]),
   (-6291456, [0, 1, 2, 2]),
   ((-6291456 : Rat)/5, [0, 5]),
   (33554432, [1, 1, 1, 2]),
   (12582912, [1, 4]),
   (8388608, [2, 3])]),
 (1,
  [((16777216 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (8388608, [0, 1, 1, 3]),
   (6291456, [0, 1, 2, 2]),
   ((6291456 : Rat)/5, [0, 5]),
   (33554432, [1, 1, 1, 2]),
   (12582912, [1, 4]),
   (8388608, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_3_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_3)) skA_E0_Q4_3 := by decide +kernel

def skA_E0_Q4_4 : SectorVector := [(-1,
  [(25165824, [0, 1, 1, 1, 1, 1]),
   (62914560, [0, 1, 1, 3]),
   (47185920, [0, 1, 2, 2]),
   (9437184, [0, 5]),
   (-251658240, [1, 1, 1, 2]),
   (-94371840, [1, 4]),
   (-62914560, [2, 3])]),
 (1,
  [(-25165824, [0, 1, 1, 1, 1, 1]),
   (-62914560, [0, 1, 1, 3]),
   (-47185920, [0, 1, 2, 2]),
   (-9437184, [0, 5]),
   (-251658240, [1, 1, 1, 2]),
   (-94371840, [1, 4]),
   (-62914560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_4_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_4)) skA_E0_Q4_4 := by decide +kernel

def skA_E0_Q4_5 : SectorVector := [(-1,
  [((184549376 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((461373440 : Rat)/9, [0, 1, 1, 3]),
   ((115343360 : Rat)/3, [0, 1, 2, 2]),
   ((23068672 : Rat)/3, [0, 5]),
   ((-1845493760 : Rat)/9, [1, 1, 1, 2]),
   ((-230686720 : Rat)/3, [1, 4]),
   ((-461373440 : Rat)/9, [2, 3])]),
 (1,
  [((-184549376 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-461373440 : Rat)/9, [0, 1, 1, 3]),
   ((-115343360 : Rat)/3, [0, 1, 2, 2]),
   ((-23068672 : Rat)/3, [0, 5]),
   ((-1845493760 : Rat)/9, [1, 1, 1, 2]),
   ((-230686720 : Rat)/3, [1, 4]),
   ((-461373440 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_5_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_5)) skA_E0_Q4_5 := by decide +kernel

def skA_E0_Q4_6 : SectorVector := [(-1,
  [(239075328, [0, 1, 1, 1, 1, 1]),
   (597688320, [0, 1, 1, 3]),
   (448266240, [0, 1, 2, 2]),
   (89653248, [0, 5]),
   (-2390753280, [1, 1, 1, 2]),
   (-896532480, [1, 4]),
   (-597688320, [2, 3])]),
 (1,
  [(-239075328, [0, 1, 1, 1, 1, 1]),
   (-597688320, [0, 1, 1, 3]),
   (-448266240, [0, 1, 2, 2]),
   (-89653248, [0, 5]),
   (-2390753280, [1, 1, 1, 2]),
   (-896532480, [1, 4]),
   (-597688320, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_6_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_6)) skA_E0_Q4_6 := by decide +kernel

def skA_E0_Q4_7 : SectorVector := [(-1,
  [((-61341696 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-153354240 : Rat)/7, [0, 1, 1, 3]),
   ((-115015680 : Rat)/7, [0, 1, 2, 2]),
   ((-23003136 : Rat)/7, [0, 5]),
   ((613416960 : Rat)/7, [1, 1, 1, 2]),
   ((230031360 : Rat)/7, [1, 4]),
   ((153354240 : Rat)/7, [2, 3])]),
 (1,
  [((61341696 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((153354240 : Rat)/7, [0, 1, 1, 3]),
   ((115015680 : Rat)/7, [0, 1, 2, 2]),
   ((23003136 : Rat)/7, [0, 5]),
   ((613416960 : Rat)/7, [1, 1, 1, 2]),
   ((230031360 : Rat)/7, [1, 4]),
   ((153354240 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_7_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_7)) skA_E0_Q4_7 := by decide +kernel

def skA_E0_Q4_8 : SectorVector := [(-1,
  [(125829120, [0, 1, 1, 1, 1, 1]),
   (314572800, [0, 1, 1, 3]),
   (235929600, [0, 1, 2, 2]),
   (47185920, [0, 5]),
   (-1258291200, [1, 1, 1, 2]),
   (-471859200, [1, 4]),
   (-314572800, [2, 3])]),
 (1,
  [(-125829120, [0, 1, 1, 1, 1, 1]),
   (-314572800, [0, 1, 1, 3]),
   (-235929600, [0, 1, 2, 2]),
   (-47185920, [0, 5]),
   (-1258291200, [1, 1, 1, 2]),
   (-471859200, [1, 4]),
   (-314572800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_8_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_8)) skA_E0_Q4_8 := by decide +kernel

def skA_E0_Q4_9 : SectorVector := [(-1,
  [(-125829120, [0, 1, 1, 1, 1, 1]),
   (-314572800, [0, 1, 1, 3]),
   (-235929600, [0, 1, 2, 2]),
   (-47185920, [0, 5]),
   (1258291200, [1, 1, 1, 2]),
   (471859200, [1, 4]),
   (314572800, [2, 3])]),
 (1,
  [(125829120, [0, 1, 1, 1, 1, 1]),
   (314572800, [0, 1, 1, 3]),
   (235929600, [0, 1, 2, 2]),
   (47185920, [0, 5]),
   (1258291200, [1, 1, 1, 2]),
   (471859200, [1, 4]),
   (314572800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_9_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_9)) skA_E0_Q4_9 := by decide +kernel

def skA_E0_Q4_10 : SectorVector := [(-1,
  [(-127926272, [0, 1, 1, 1, 1, 1]),
   (-319815680, [0, 1, 1, 3]),
   (-239861760, [0, 1, 2, 2]),
   (-47972352, [0, 5]),
   (1279262720, [1, 1, 1, 2]),
   (479723520, [1, 4]),
   (319815680, [2, 3])]),
 (1,
  [(127926272, [0, 1, 1, 1, 1, 1]),
   (319815680, [0, 1, 1, 3]),
   (239861760, [0, 1, 2, 2]),
   (47972352, [0, 5]),
   (1279262720, [1, 1, 1, 2]),
   (479723520, [1, 4]),
   (319815680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_10_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_10)) skA_E0_Q4_10 := by decide +kernel

def skA_E0_Q4_11 : SectorVector := [(-1,
  [(-62914560, [0, 1, 1, 1, 1, 1]),
   (-157286400, [0, 1, 1, 3]),
   (-117964800, [0, 1, 2, 2]),
   (-23592960, [0, 5]),
   (629145600, [1, 1, 1, 2]),
   (235929600, [1, 4]),
   (157286400, [2, 3])]),
 (1,
  [(62914560, [0, 1, 1, 1, 1, 1]),
   (157286400, [0, 1, 1, 3]),
   (117964800, [0, 1, 2, 2]),
   (23592960, [0, 5]),
   (629145600, [1, 1, 1, 2]),
   (235929600, [1, 4]),
   (157286400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_11_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_11)) skA_E0_Q4_11 := by decide +kernel

def skA_E0_Q4_12 : SectorVector := [(-1,
  [(-114032640, [0, 1, 1, 1, 1, 1]),
   (-285081600, [0, 1, 1, 3]),
   (-213811200, [0, 1, 2, 2]),
   (-42762240, [0, 5]),
   (1140326400, [1, 1, 1, 2]),
   (427622400, [1, 4]),
   (285081600, [2, 3])]),
 (1,
  [(114032640, [0, 1, 1, 1, 1, 1]),
   (285081600, [0, 1, 1, 3]),
   (213811200, [0, 1, 2, 2]),
   (42762240, [0, 5]),
   (1140326400, [1, 1, 1, 2]),
   (427622400, [1, 4]),
   (285081600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_12_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_12)) skA_E0_Q4_12 := by decide +kernel

def skA_E0_Q4_13 : SectorVector := [(-1,
  [(-108134400, [0, 1, 1, 1, 1, 1]),
   (-270336000, [0, 1, 1, 3]),
   (-202752000, [0, 1, 2, 2]),
   (-40550400, [0, 5]),
   (1081344000, [1, 1, 1, 2]),
   (405504000, [1, 4]),
   (270336000, [2, 3])]),
 (1,
  [(108134400, [0, 1, 1, 1, 1, 1]),
   (270336000, [0, 1, 1, 3]),
   (202752000, [0, 1, 2, 2]),
   (40550400, [0, 5]),
   (1081344000, [1, 1, 1, 2]),
   (405504000, [1, 4]),
   (270336000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_13_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_13)) skA_E0_Q4_13 := by decide +kernel

def skA_E0_Q4_14 : SectorVector := [(-1,
  [((-26214400 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-65536000 : Rat)/27, [0, 1, 1, 3]),
   ((-16384000 : Rat)/9, [0, 1, 2, 2]),
   ((-3276800 : Rat)/9, [0, 5]),
   ((262144000 : Rat)/27, [1, 1, 1, 2]),
   ((32768000 : Rat)/9, [1, 4]),
   ((65536000 : Rat)/27, [2, 3])]),
 (1,
  [((26214400 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((65536000 : Rat)/27, [0, 1, 1, 3]),
   ((16384000 : Rat)/9, [0, 1, 2, 2]),
   ((3276800 : Rat)/9, [0, 5]),
   ((262144000 : Rat)/27, [1, 1, 1, 2]),
   ((32768000 : Rat)/9, [1, 4]),
   ((65536000 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_14_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_14)) skA_E0_Q4_14 := by decide +kernel

def skA_E0_Q4_15 : SectorVector := [(-1,
  [((227737600 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((569344000 : Rat)/3, [0, 1, 1, 3]),
   (142336000, [0, 1, 2, 2]),
   (28467200, [0, 5]),
   ((-2277376000 : Rat)/3, [1, 1, 1, 2]),
   (-284672000, [1, 4]),
   ((-569344000 : Rat)/3, [2, 3])]),
 (1,
  [((-227737600 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-569344000 : Rat)/3, [0, 1, 1, 3]),
   (-142336000, [0, 1, 2, 2]),
   (-28467200, [0, 5]),
   ((-2277376000 : Rat)/3, [1, 1, 1, 2]),
   (-284672000, [1, 4]),
   ((-569344000 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_15_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_15)) skA_E0_Q4_15 := by decide +kernel

def skA_E0_Q4_16 : SectorVector := [(-1,
  [(5898240, [0, 1, 1, 1, 1, 1]),
   (14745600, [0, 1, 1, 3]),
   (11059200, [0, 1, 2, 2]),
   (2211840, [0, 5]),
   (-58982400, [1, 1, 1, 2]),
   (-22118400, [1, 4]),
   (-14745600, [2, 3])]),
 (1,
  [(-5898240, [0, 1, 1, 1, 1, 1]),
   (-14745600, [0, 1, 1, 3]),
   (-11059200, [0, 1, 2, 2]),
   (-2211840, [0, 5]),
   (-58982400, [1, 1, 1, 2]),
   (-22118400, [1, 4]),
   (-14745600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_16_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_16)) skA_E0_Q4_16 := by decide +kernel

def skA_E0_Q4_17 : SectorVector := [(-1,
  [(51118080, [0, 1, 1, 1, 1, 1]),
   (127795200, [0, 1, 1, 3]),
   (95846400, [0, 1, 2, 2]),
   (19169280, [0, 5]),
   (-511180800, [1, 1, 1, 2]),
   (-191692800, [1, 4]),
   (-127795200, [2, 3])]),
 (1,
  [(-51118080, [0, 1, 1, 1, 1, 1]),
   (-127795200, [0, 1, 1, 3]),
   (-95846400, [0, 1, 2, 2]),
   (-19169280, [0, 5]),
   (-511180800, [1, 1, 1, 2]),
   (-191692800, [1, 4]),
   (-127795200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_17_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_17)) skA_E0_Q4_17 := by decide +kernel

def skA_E0_Q4_18 : SectorVector := [(-1,
  [(-8847360, [0, 1, 1, 1, 1, 1]),
   (-22118400, [0, 1, 1, 3]),
   (-16588800, [0, 1, 2, 2]),
   (-3317760, [0, 5]),
   (88473600, [1, 1, 1, 2]),
   (33177600, [1, 4]),
   (22118400, [2, 3])]),
 (1,
  [(8847360, [0, 1, 1, 1, 1, 1]),
   (22118400, [0, 1, 1, 3]),
   (16588800, [0, 1, 2, 2]),
   (3317760, [0, 5]),
   (88473600, [1, 1, 1, 2]),
   (33177600, [1, 4]),
   (22118400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_18_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_18)) skA_E0_Q4_18 := by decide +kernel

def skA_E0_Q4_19 : SectorVector := [(-1,
  [(-82575360, [0, 1, 1, 1, 1, 1]),
   (-206438400, [0, 1, 1, 3]),
   (-154828800, [0, 1, 2, 2]),
   (-30965760, [0, 5]),
   (825753600, [1, 1, 1, 2]),
   (309657600, [1, 4]),
   (206438400, [2, 3])]),
 (1,
  [(82575360, [0, 1, 1, 1, 1, 1]),
   (206438400, [0, 1, 1, 3]),
   (154828800, [0, 1, 2, 2]),
   (30965760, [0, 5]),
   (825753600, [1, 1, 1, 2]),
   (309657600, [1, 4]),
   (206438400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_19_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_19)) skA_E0_Q4_19 := by decide +kernel

def skA_E0_Q4_20 : SectorVector := [(-1,
  [(-107642880, [0, 1, 1, 1, 1, 1]),
   (-269107200, [0, 1, 1, 3]),
   (-201830400, [0, 1, 2, 2]),
   (-40366080, [0, 5]),
   (1076428800, [1, 1, 1, 2]),
   (403660800, [1, 4]),
   (269107200, [2, 3])]),
 (1,
  [(107642880, [0, 1, 1, 1, 1, 1]),
   (269107200, [0, 1, 1, 3]),
   (201830400, [0, 1, 2, 2]),
   (40366080, [0, 5]),
   (1076428800, [1, 1, 1, 2]),
   (403660800, [1, 4]),
   (269107200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_20_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_20)) skA_E0_Q4_20 := by decide +kernel

def skA_E0_Q4_21 : SectorVector := [(-1,
  [((-284884992 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-142442496, [0, 1, 1, 3]),
   (-106831872, [0, 1, 2, 2]),
   ((-106831872 : Rat)/5, [0, 5]),
   (569769984, [1, 1, 1, 2]),
   (213663744, [1, 4]),
   (142442496, [2, 3])]),
 (1,
  [((284884992 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (142442496, [0, 1, 1, 3]),
   (106831872, [0, 1, 2, 2]),
   ((106831872 : Rat)/5, [0, 5]),
   (569769984, [1, 1, 1, 2]),
   (213663744, [1, 4]),
   (142442496, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_21_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_21)) skA_E0_Q4_21 := by decide +kernel

def skA_E0_Q4_22 : SectorVector := [(-1,
  [(27525120, [0, 1, 1, 1, 1, 1]),
   (68812800, [0, 1, 1, 3]),
   (51609600, [0, 1, 2, 2]),
   (10321920, [0, 5]),
   (-275251200, [1, 1, 1, 2]),
   (-103219200, [1, 4]),
   (-68812800, [2, 3])]),
 (1,
  [(-27525120, [0, 1, 1, 1, 1, 1]),
   (-68812800, [0, 1, 1, 3]),
   (-51609600, [0, 1, 2, 2]),
   (-10321920, [0, 5]),
   (-275251200, [1, 1, 1, 2]),
   (-103219200, [1, 4]),
   (-68812800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_22_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_22)) skA_E0_Q4_22 := by decide +kernel

def skA_E0_Q4_23 : SectorVector := [(-1,
  [(-40550400, [0, 1, 1, 1, 1, 1]),
   (-101376000, [0, 1, 1, 3]),
   (-76032000, [0, 1, 2, 2]),
   (-15206400, [0, 5]),
   (405504000, [1, 1, 1, 2]),
   (152064000, [1, 4]),
   (101376000, [2, 3])]),
 (1,
  [(40550400, [0, 1, 1, 1, 1, 1]),
   (101376000, [0, 1, 1, 3]),
   (76032000, [0, 1, 2, 2]),
   (15206400, [0, 5]),
   (405504000, [1, 1, 1, 2]),
   (152064000, [1, 4]),
   (101376000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_23_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_23)) skA_E0_Q4_23 := by decide +kernel

def skA_E0_Q4_24 : SectorVector := [(-1,
  [(-89456640, [0, 1, 1, 1, 1, 1]),
   (-223641600, [0, 1, 1, 3]),
   (-167731200, [0, 1, 2, 2]),
   (-33546240, [0, 5]),
   (894566400, [1, 1, 1, 2]),
   (335462400, [1, 4]),
   (223641600, [2, 3])]),
 (1,
  [(89456640, [0, 1, 1, 1, 1, 1]),
   (223641600, [0, 1, 1, 3]),
   (167731200, [0, 1, 2, 2]),
   (33546240, [0, 5]),
   (894566400, [1, 1, 1, 2]),
   (335462400, [1, 4]),
   (223641600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_24_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_24)) skA_E0_Q4_24 := by decide +kernel

def skA_E0_Q4_25 : SectorVector := [(-1,
  [(-89800704, [0, 1, 1, 1, 1, 1]),
   (-224501760, [0, 1, 1, 3]),
   (-168376320, [0, 1, 2, 2]),
   (-33675264, [0, 5]),
   (898007040, [1, 1, 1, 2]),
   (336752640, [1, 4]),
   (224501760, [2, 3])]),
 (1,
  [(89800704, [0, 1, 1, 1, 1, 1]),
   (224501760, [0, 1, 1, 3]),
   (168376320, [0, 1, 2, 2]),
   (33675264, [0, 5]),
   (898007040, [1, 1, 1, 2]),
   (336752640, [1, 4]),
   (224501760, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_25_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_25)) skA_E0_Q4_25 := by decide +kernel

def skA_E0_Q4_26 : SectorVector := [(-1,
  [(-28442624, [0, 1, 1, 1, 1, 1]),
   (-71106560, [0, 1, 1, 3]),
   (-53329920, [0, 1, 2, 2]),
   (-10665984, [0, 5]),
   (284426240, [1, 1, 1, 2]),
   (106659840, [1, 4]),
   (71106560, [2, 3])]),
 (1,
  [(28442624, [0, 1, 1, 1, 1, 1]),
   (71106560, [0, 1, 1, 3]),
   (53329920, [0, 1, 2, 2]),
   (10665984, [0, 5]),
   (284426240, [1, 1, 1, 2]),
   (106659840, [1, 4]),
   (71106560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_26_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_26)) skA_E0_Q4_26 := by decide +kernel

def skA_E0_Q4_27 : SectorVector := [(-1,
  [(-24084480, [0, 1, 1, 1, 1, 1]),
   (-60211200, [0, 1, 1, 3]),
   (-45158400, [0, 1, 2, 2]),
   (-9031680, [0, 5]),
   (240844800, [1, 1, 1, 2]),
   (90316800, [1, 4]),
   (60211200, [2, 3])]),
 (1,
  [(24084480, [0, 1, 1, 1, 1, 1]),
   (60211200, [0, 1, 1, 3]),
   (45158400, [0, 1, 2, 2]),
   (9031680, [0, 5]),
   (240844800, [1, 1, 1, 2]),
   (90316800, [1, 4]),
   (60211200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_27_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_27)) skA_E0_Q4_27 := by decide +kernel

def skA_E0_Q4_28 : SectorVector := [(-1,
  [((499322880 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((1248307200 : Rat)/11, [0, 1, 1, 3]),
   ((936230400 : Rat)/11, [0, 1, 2, 2]),
   ((187246080 : Rat)/11, [0, 5]),
   ((-4993228800 : Rat)/11, [1, 1, 1, 2]),
   ((-1872460800 : Rat)/11, [1, 4]),
   ((-1248307200 : Rat)/11, [2, 3])]),
 (1,
  [((-499322880 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((-1248307200 : Rat)/11, [0, 1, 1, 3]),
   ((-936230400 : Rat)/11, [0, 1, 2, 2]),
   ((-187246080 : Rat)/11, [0, 5]),
   ((-4993228800 : Rat)/11, [1, 1, 1, 2]),
   ((-1872460800 : Rat)/11, [1, 4]),
   ((-1248307200 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_28_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_28)) skA_E0_Q4_28 := by decide +kernel

def skA_E0_Q4_29 : SectorVector := [(-1,
  [(1048576, [0, 1, 1, 1, 1, 1]),
   (2621440, [0, 1, 1, 3]),
   (1966080, [0, 1, 2, 2]),
   (393216, [0, 5]),
   (-10485760, [1, 1, 1, 2]),
   (-3932160, [1, 4]),
   (-2621440, [2, 3])]),
 (1,
  [(-1048576, [0, 1, 1, 1, 1, 1]),
   (-2621440, [0, 1, 1, 3]),
   (-1966080, [0, 1, 2, 2]),
   (-393216, [0, 5]),
   (-10485760, [1, 1, 1, 2]),
   (-3932160, [1, 4]),
   (-2621440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_29_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_29)) skA_E0_Q4_29 := by decide +kernel

def skA_E0_Q4_30 : SectorVector := [(-1,
  [(-8192000, [0, 1, 1, 1, 1, 1]),
   (-20480000, [0, 1, 1, 3]),
   (-15360000, [0, 1, 2, 2]),
   (-3072000, [0, 5]),
   (81920000, [1, 1, 1, 2]),
   (30720000, [1, 4]),
   (20480000, [2, 3])]),
 (1,
  [(8192000, [0, 1, 1, 1, 1, 1]),
   (20480000, [0, 1, 1, 3]),
   (15360000, [0, 1, 2, 2]),
   (3072000, [0, 5]),
   (81920000, [1, 1, 1, 2]),
   (30720000, [1, 4]),
   (20480000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_30_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_30)) skA_E0_Q4_30 := by decide +kernel

def skA_E0_Q4_31 : SectorVector := [(-1,
  [(-16908288, [0, 1, 1, 1, 1, 1]),
   (-42270720, [0, 1, 1, 3]),
   (-31703040, [0, 1, 2, 2]),
   (-6340608, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (63406080, [1, 4]),
   (42270720, [2, 3])]),
 (1,
  [(16908288, [0, 1, 1, 1, 1, 1]),
   (42270720, [0, 1, 1, 3]),
   (31703040, [0, 1, 2, 2]),
   (6340608, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (63406080, [1, 4]),
   (42270720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_31_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_31)) skA_E0_Q4_31 := by decide +kernel

def skA_E0_Q4_32 : SectorVector := [(-1,
  [(-7372800, [0, 1, 1, 1, 1, 1]),
   (-18432000, [0, 1, 1, 3]),
   (-13824000, [0, 1, 2, 2]),
   (-2764800, [0, 5]),
   (73728000, [1, 1, 1, 2]),
   (27648000, [1, 4]),
   (18432000, [2, 3])]),
 (1,
  [(7372800, [0, 1, 1, 1, 1, 1]),
   (18432000, [0, 1, 1, 3]),
   (13824000, [0, 1, 2, 2]),
   (2764800, [0, 5]),
   (73728000, [1, 1, 1, 2]),
   (27648000, [1, 4]),
   (18432000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_32_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_32)) skA_E0_Q4_32 := by decide +kernel

def skA_E0_Q4_33 : SectorVector := [(-1,
  [(-7864320, [0, 1, 1, 1, 1, 1]),
   (-19660800, [0, 1, 1, 3]),
   (-14745600, [0, 1, 2, 2]),
   (-2949120, [0, 5]),
   (78643200, [1, 1, 1, 2]),
   (29491200, [1, 4]),
   (19660800, [2, 3])]),
 (1,
  [(7864320, [0, 1, 1, 1, 1, 1]),
   (19660800, [0, 1, 1, 3]),
   (14745600, [0, 1, 2, 2]),
   (2949120, [0, 5]),
   (78643200, [1, 1, 1, 2]),
   (29491200, [1, 4]),
   (19660800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_33_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_33)) skA_E0_Q4_33 := by decide +kernel

def skA_E0_Q4_34 : SectorVector := [(-1,
  [(10174464, [0, 1, 1, 1, 1, 1]),
   (25436160, [0, 1, 1, 3]),
   (19077120, [0, 1, 2, 2]),
   (3815424, [0, 5]),
   (-101744640, [1, 1, 1, 2]),
   (-38154240, [1, 4]),
   (-25436160, [2, 3])]),
 (1,
  [(-10174464, [0, 1, 1, 1, 1, 1]),
   (-25436160, [0, 1, 1, 3]),
   (-19077120, [0, 1, 2, 2]),
   (-3815424, [0, 5]),
   (-101744640, [1, 1, 1, 2]),
   (-38154240, [1, 4]),
   (-25436160, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_34_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_34)) skA_E0_Q4_34 := by decide +kernel

def skA_E0_Q4_35 : SectorVector := [(-1,
  [((-7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-18022400 : Rat)/27, [0, 1, 1, 3]),
   ((-4505600 : Rat)/9, [0, 1, 2, 2]),
   ((-901120 : Rat)/9, [0, 5]),
   ((72089600 : Rat)/27, [1, 1, 1, 2]),
   ((9011200 : Rat)/9, [1, 4]),
   ((18022400 : Rat)/27, [2, 3])]),
 (1,
  [((7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((18022400 : Rat)/27, [0, 1, 1, 3]),
   ((4505600 : Rat)/9, [0, 1, 2, 2]),
   ((901120 : Rat)/9, [0, 5]),
   ((72089600 : Rat)/27, [1, 1, 1, 2]),
   ((9011200 : Rat)/9, [1, 4]),
   ((18022400 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_35_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_35)) skA_E0_Q4_35 := by decide +kernel

def skA_E0_Q4_36 : SectorVector := [(-1,
  [((-6062080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-15155200 : Rat)/3, [0, 1, 1, 3]),
   (-3788800, [0, 1, 2, 2]),
   (-757760, [0, 5]),
   ((60620800 : Rat)/3, [1, 1, 1, 2]),
   (7577600, [1, 4]),
   ((15155200 : Rat)/3, [2, 3])]),
 (1,
  [((6062080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((15155200 : Rat)/3, [0, 1, 1, 3]),
   (3788800, [0, 1, 2, 2]),
   (757760, [0, 5]),
   ((60620800 : Rat)/3, [1, 1, 1, 2]),
   (7577600, [1, 4]),
   ((15155200 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_36_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_36)) skA_E0_Q4_36 := by decide +kernel

def skA_E0_Q4_37 : SectorVector := [(-1,
  [(-7004160, [0, 1, 1, 1, 1, 1]),
   (-17510400, [0, 1, 1, 3]),
   (-13132800, [0, 1, 2, 2]),
   (-2626560, [0, 5]),
   (70041600, [1, 1, 1, 2]),
   (26265600, [1, 4]),
   (17510400, [2, 3])]),
 (1,
  [(7004160, [0, 1, 1, 1, 1, 1]),
   (17510400, [0, 1, 1, 3]),
   (13132800, [0, 1, 2, 2]),
   (2626560, [0, 5]),
   (70041600, [1, 1, 1, 2]),
   (26265600, [1, 4]),
   (17510400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_37_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_37)) skA_E0_Q4_37 := by decide +kernel

def skA_E0_Q4_38 : SectorVector := [(-1,
  [(-9142272, [0, 1, 1, 1, 1, 1]),
   (-22855680, [0, 1, 1, 3]),
   (-17141760, [0, 1, 2, 2]),
   (-3428352, [0, 5]),
   (91422720, [1, 1, 1, 2]),
   (34283520, [1, 4]),
   (22855680, [2, 3])]),
 (1,
  [(9142272, [0, 1, 1, 1, 1, 1]),
   (22855680, [0, 1, 1, 3]),
   (17141760, [0, 1, 2, 2]),
   (3428352, [0, 5]),
   (91422720, [1, 1, 1, 2]),
   (34283520, [1, 4]),
   (22855680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_38_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_38)) skA_E0_Q4_38 := by decide +kernel

def skA_E0_Q4_39 : SectorVector := [(-1,
  [(-4874240, [0, 1, 1, 1, 1, 1]),
   (-12185600, [0, 1, 1, 3]),
   (-9139200, [0, 1, 2, 2]),
   (-1827840, [0, 5]),
   (48742400, [1, 1, 1, 2]),
   (18278400, [1, 4]),
   (12185600, [2, 3])]),
 (1,
  [(4874240, [0, 1, 1, 1, 1, 1]),
   (12185600, [0, 1, 1, 3]),
   (9139200, [0, 1, 2, 2]),
   (1827840, [0, 5]),
   (48742400, [1, 1, 1, 2]),
   (18278400, [1, 4]),
   (12185600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q4_39_cert : VectorCertificate (Tpow 4 (aLeft false (10 : ℤ) skM_E0_39)) skA_E0_Q4_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_4_join : VectorCertificate ([skA_E0_Q4_0, skA_E0_Q4_1, skA_E0_Q4_2, skA_E0_Q4_3, skA_E0_Q4_4, skA_E0_Q4_5, skA_E0_Q4_6, skA_E0_Q4_7, skA_E0_Q4_8, skA_E0_Q4_9, skA_E0_Q4_10, skA_E0_Q4_11, skA_E0_Q4_12, skA_E0_Q4_13, skA_E0_Q4_14, skA_E0_Q4_15, skA_E0_Q4_16, skA_E0_Q4_17, skA_E0_Q4_18, skA_E0_Q4_19, skA_E0_Q4_20, skA_E0_Q4_21, skA_E0_Q4_22, skA_E0_Q4_23, skA_E0_Q4_24, skA_E0_Q4_25, skA_E0_Q4_26, skA_E0_Q4_27, skA_E0_Q4_28, skA_E0_Q4_29, skA_E0_Q4_30, skA_E0_Q4_31, skA_E0_Q4_32, skA_E0_Q4_33, skA_E0_Q4_34, skA_E0_Q4_35, skA_E0_Q4_36, skA_E0_Q4_37, skA_E0_Q4_38, skA_E0_Q4_39] : List SectorVector).flatten skQ_E0_4 := by decide +kernel

theorem skQ_E0_4_val : evaluate skQ_E0_4 = evaluate (OrbSgl.vTerm false skY_E0 0 4) :=
  vTerm_of_chunks false skY_E0 0 4 (10 : ℤ) (by norm_num) skM_E0 [skA_E0_Q4_0, skA_E0_Q4_1, skA_E0_Q4_2, skA_E0_Q4_3, skA_E0_Q4_4, skA_E0_Q4_5, skA_E0_Q4_6, skA_E0_Q4_7, skA_E0_Q4_8, skA_E0_Q4_9, skA_E0_Q4_10, skA_E0_Q4_11, skA_E0_Q4_12, skA_E0_Q4_13, skA_E0_Q4_14, skA_E0_Q4_15, skA_E0_Q4_16, skA_E0_Q4_17, skA_E0_Q4_18, skA_E0_Q4_19, skA_E0_Q4_20, skA_E0_Q4_21, skA_E0_Q4_22, skA_E0_Q4_23, skA_E0_Q4_24, skA_E0_Q4_25, skA_E0_Q4_26, skA_E0_Q4_27, skA_E0_Q4_28, skA_E0_Q4_29, skA_E0_Q4_30, skA_E0_Q4_31, skA_E0_Q4_32, skA_E0_Q4_33, skA_E0_Q4_34, skA_E0_Q4_35, skA_E0_Q4_36, skA_E0_Q4_37, skA_E0_Q4_38, skA_E0_Q4_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q4_0_cert (List.Forall₂.cons skA_E0_Q4_1_cert (List.Forall₂.cons skA_E0_Q4_2_cert (List.Forall₂.cons skA_E0_Q4_3_cert (List.Forall₂.cons skA_E0_Q4_4_cert (List.Forall₂.cons skA_E0_Q4_5_cert (List.Forall₂.cons skA_E0_Q4_6_cert (List.Forall₂.cons skA_E0_Q4_7_cert (List.Forall₂.cons skA_E0_Q4_8_cert (List.Forall₂.cons skA_E0_Q4_9_cert (List.Forall₂.cons skA_E0_Q4_10_cert (List.Forall₂.cons skA_E0_Q4_11_cert (List.Forall₂.cons skA_E0_Q4_12_cert (List.Forall₂.cons skA_E0_Q4_13_cert (List.Forall₂.cons skA_E0_Q4_14_cert (List.Forall₂.cons skA_E0_Q4_15_cert (List.Forall₂.cons skA_E0_Q4_16_cert (List.Forall₂.cons skA_E0_Q4_17_cert (List.Forall₂.cons skA_E0_Q4_18_cert (List.Forall₂.cons skA_E0_Q4_19_cert (List.Forall₂.cons skA_E0_Q4_20_cert (List.Forall₂.cons skA_E0_Q4_21_cert (List.Forall₂.cons skA_E0_Q4_22_cert (List.Forall₂.cons skA_E0_Q4_23_cert (List.Forall₂.cons skA_E0_Q4_24_cert (List.Forall₂.cons skA_E0_Q4_25_cert (List.Forall₂.cons skA_E0_Q4_26_cert (List.Forall₂.cons skA_E0_Q4_27_cert (List.Forall₂.cons skA_E0_Q4_28_cert (List.Forall₂.cons skA_E0_Q4_29_cert (List.Forall₂.cons skA_E0_Q4_30_cert (List.Forall₂.cons skA_E0_Q4_31_cert (List.Forall₂.cons skA_E0_Q4_32_cert (List.Forall₂.cons skA_E0_Q4_33_cert (List.Forall₂.cons skA_E0_Q4_34_cert (List.Forall₂.cons skA_E0_Q4_35_cert (List.Forall₂.cons skA_E0_Q4_36_cert (List.Forall₂.cons skA_E0_Q4_37_cert (List.Forall₂.cons skA_E0_Q4_38_cert (List.Forall₂.cons skA_E0_Q4_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_4 skQ_E0_4_join

def skA_E0_Q5_0 : SectorVector := [(1,
  [((-68719476736 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((-34359738368 : Rat)/2079, [0, 1, 1, 3]),
   ((-8589934592 : Rat)/693, [0, 1, 2, 2]),
   ((-8589934592 : Rat)/3465, [0, 5]),
   ((-137438953472 : Rat)/2079, [1, 1, 1, 2]),
   ((-17179869184 : Rat)/693, [1, 4]),
   ((-34359738368 : Rat)/2079, [2, 3])]),
 (-1,
  [((68719476736 : Rat)/10395, [0, 1, 1, 1, 1, 1]),
   ((34359738368 : Rat)/2079, [0, 1, 1, 3]),
   ((8589934592 : Rat)/693, [0, 1, 2, 2]),
   ((8589934592 : Rat)/3465, [0, 5]),
   ((-137438953472 : Rat)/2079, [1, 1, 1, 2]),
   ((-17179869184 : Rat)/693, [1, 4]),
   ((-34359738368 : Rat)/2079, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_0_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_0)) skA_E0_Q5_0 := by decide +kernel

def skA_E0_Q5_1 : SectorVector := [(1,
  [((-2147483648 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-5368709120 : Rat)/27, [0, 1, 1, 3]),
   ((-1342177280 : Rat)/9, [0, 1, 2, 2]),
   ((-268435456 : Rat)/9, [0, 5]),
   ((-21474836480 : Rat)/27, [1, 1, 1, 2]),
   ((-2684354560 : Rat)/9, [1, 4]),
   ((-5368709120 : Rat)/27, [2, 3])]),
 (-1,
  [((2147483648 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((5368709120 : Rat)/27, [0, 1, 1, 3]),
   ((1342177280 : Rat)/9, [0, 1, 2, 2]),
   ((268435456 : Rat)/9, [0, 5]),
   ((-21474836480 : Rat)/27, [1, 1, 1, 2]),
   ((-2684354560 : Rat)/9, [1, 4]),
   ((-5368709120 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_1_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_1)) skA_E0_Q5_1 := by decide +kernel

def skA_E0_Q5_2 : SectorVector := [(1,
  [((-2147483648 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-5368709120 : Rat)/7, [0, 1, 1, 3]),
   ((-4026531840 : Rat)/7, [0, 1, 2, 2]),
   ((-805306368 : Rat)/7, [0, 5]),
   ((-21474836480 : Rat)/7, [1, 1, 1, 2]),
   ((-8053063680 : Rat)/7, [1, 4]),
   ((-5368709120 : Rat)/7, [2, 3])]),
 (-1,
  [((2147483648 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((5368709120 : Rat)/7, [0, 1, 1, 3]),
   ((4026531840 : Rat)/7, [0, 1, 2, 2]),
   ((805306368 : Rat)/7, [0, 5]),
   ((-21474836480 : Rat)/7, [1, 1, 1, 2]),
   ((-8053063680 : Rat)/7, [1, 4]),
   ((-5368709120 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_2_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_2)) skA_E0_Q5_2 := by decide +kernel

def skA_E0_Q5_3 : SectorVector := [(1,
  [((134217728 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (67108864, [0, 1, 1, 3]),
   (50331648, [0, 1, 2, 2]),
   ((50331648 : Rat)/5, [0, 5]),
   (268435456, [1, 1, 1, 2]),
   (100663296, [1, 4]),
   (67108864, [2, 3])]),
 (-1,
  [((-134217728 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-67108864, [0, 1, 1, 3]),
   (-50331648, [0, 1, 2, 2]),
   ((-50331648 : Rat)/5, [0, 5]),
   (268435456, [1, 1, 1, 2]),
   (100663296, [1, 4]),
   (67108864, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_3_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_3)) skA_E0_Q5_3 := by decide +kernel

def skA_E0_Q5_4 : SectorVector := [(1,
  [(-100663296, [0, 1, 1, 1, 1, 1]),
   (-251658240, [0, 1, 1, 3]),
   (-188743680, [0, 1, 2, 2]),
   (-37748736, [0, 5]),
   (-1006632960, [1, 1, 1, 2]),
   (-377487360, [1, 4]),
   (-251658240, [2, 3])]),
 (-1,
  [(100663296, [0, 1, 1, 1, 1, 1]),
   (251658240, [0, 1, 1, 3]),
   (188743680, [0, 1, 2, 2]),
   (37748736, [0, 5]),
   (-1006632960, [1, 1, 1, 2]),
   (-377487360, [1, 4]),
   (-251658240, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_4_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_4)) skA_E0_Q5_4 := by decide +kernel

def skA_E0_Q5_5 : SectorVector := [(1,
  [((-738197504 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((-1845493760 : Rat)/9, [0, 1, 1, 3]),
   ((-461373440 : Rat)/3, [0, 1, 2, 2]),
   ((-92274688 : Rat)/3, [0, 5]),
   ((-7381975040 : Rat)/9, [1, 1, 1, 2]),
   ((-922746880 : Rat)/3, [1, 4]),
   ((-1845493760 : Rat)/9, [2, 3])]),
 (-1,
  [((738197504 : Rat)/9, [0, 1, 1, 1, 1, 1]),
   ((1845493760 : Rat)/9, [0, 1, 1, 3]),
   ((461373440 : Rat)/3, [0, 1, 2, 2]),
   ((92274688 : Rat)/3, [0, 5]),
   ((-7381975040 : Rat)/9, [1, 1, 1, 2]),
   ((-922746880 : Rat)/3, [1, 4]),
   ((-1845493760 : Rat)/9, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_5_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_5)) skA_E0_Q5_5 := by decide +kernel

def skA_E0_Q5_6 : SectorVector := [(1,
  [(-637534208, [0, 1, 1, 1, 1, 1]),
   (-1593835520, [0, 1, 1, 3]),
   (-1195376640, [0, 1, 2, 2]),
   (-239075328, [0, 5]),
   (-6375342080, [1, 1, 1, 2]),
   (-2390753280, [1, 4]),
   (-1593835520, [2, 3])]),
 (-1,
  [(637534208, [0, 1, 1, 1, 1, 1]),
   (1593835520, [0, 1, 1, 3]),
   (1195376640, [0, 1, 2, 2]),
   (239075328, [0, 5]),
   (-6375342080, [1, 1, 1, 2]),
   (-2390753280, [1, 4]),
   (-1593835520, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_6_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_6)) skA_E0_Q5_6 := by decide +kernel

def skA_E0_Q5_7 : SectorVector := [(1,
  [((163577856 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((408944640 : Rat)/7, [0, 1, 1, 3]),
   ((306708480 : Rat)/7, [0, 1, 2, 2]),
   ((61341696 : Rat)/7, [0, 5]),
   ((1635778560 : Rat)/7, [1, 1, 1, 2]),
   ((613416960 : Rat)/7, [1, 4]),
   ((408944640 : Rat)/7, [2, 3])]),
 (-1,
  [((-163577856 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-408944640 : Rat)/7, [0, 1, 1, 3]),
   ((-306708480 : Rat)/7, [0, 1, 2, 2]),
   ((-61341696 : Rat)/7, [0, 5]),
   ((1635778560 : Rat)/7, [1, 1, 1, 2]),
   ((613416960 : Rat)/7, [1, 4]),
   ((408944640 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_7_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_7)) skA_E0_Q5_7 := by decide +kernel

def skA_E0_Q5_8 : SectorVector := [(1,
  [(-251658240, [0, 1, 1, 1, 1, 1]),
   (-629145600, [0, 1, 1, 3]),
   (-471859200, [0, 1, 2, 2]),
   (-94371840, [0, 5]),
   (-2516582400, [1, 1, 1, 2]),
   (-943718400, [1, 4]),
   (-629145600, [2, 3])]),
 (-1,
  [(251658240, [0, 1, 1, 1, 1, 1]),
   (629145600, [0, 1, 1, 3]),
   (471859200, [0, 1, 2, 2]),
   (94371840, [0, 5]),
   (-2516582400, [1, 1, 1, 2]),
   (-943718400, [1, 4]),
   (-629145600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_8_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_8)) skA_E0_Q5_8 := by decide +kernel

def skA_E0_Q5_9 : SectorVector := [(1,
  [(251658240, [0, 1, 1, 1, 1, 1]),
   (629145600, [0, 1, 1, 3]),
   (471859200, [0, 1, 2, 2]),
   (94371840, [0, 5]),
   (2516582400, [1, 1, 1, 2]),
   (943718400, [1, 4]),
   (629145600, [2, 3])]),
 (-1,
  [(-251658240, [0, 1, 1, 1, 1, 1]),
   (-629145600, [0, 1, 1, 3]),
   (-471859200, [0, 1, 2, 2]),
   (-94371840, [0, 5]),
   (2516582400, [1, 1, 1, 2]),
   (943718400, [1, 4]),
   (629145600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_9_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_9)) skA_E0_Q5_9 := by decide +kernel

def skA_E0_Q5_10 : SectorVector := [(1,
  [(255852544, [0, 1, 1, 1, 1, 1]),
   (639631360, [0, 1, 1, 3]),
   (479723520, [0, 1, 2, 2]),
   (95944704, [0, 5]),
   (2558525440, [1, 1, 1, 2]),
   (959447040, [1, 4]),
   (639631360, [2, 3])]),
 (-1,
  [(-255852544, [0, 1, 1, 1, 1, 1]),
   (-639631360, [0, 1, 1, 3]),
   (-479723520, [0, 1, 2, 2]),
   (-95944704, [0, 5]),
   (2558525440, [1, 1, 1, 2]),
   (959447040, [1, 4]),
   (639631360, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_10_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_10)) skA_E0_Q5_10 := by decide +kernel

def skA_E0_Q5_11 : SectorVector := [(1,
  [(125829120, [0, 1, 1, 1, 1, 1]),
   (314572800, [0, 1, 1, 3]),
   (235929600, [0, 1, 2, 2]),
   (47185920, [0, 5]),
   (1258291200, [1, 1, 1, 2]),
   (471859200, [1, 4]),
   (314572800, [2, 3])]),
 (-1,
  [(-125829120, [0, 1, 1, 1, 1, 1]),
   (-314572800, [0, 1, 1, 3]),
   (-235929600, [0, 1, 2, 2]),
   (-47185920, [0, 5]),
   (1258291200, [1, 1, 1, 2]),
   (471859200, [1, 4]),
   (314572800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_11_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_11)) skA_E0_Q5_11 := by decide +kernel

def skA_E0_Q5_12 : SectorVector := [(1,
  [(182452224, [0, 1, 1, 1, 1, 1]),
   (456130560, [0, 1, 1, 3]),
   (342097920, [0, 1, 2, 2]),
   (68419584, [0, 5]),
   (1824522240, [1, 1, 1, 2]),
   (684195840, [1, 4]),
   (456130560, [2, 3])]),
 (-1,
  [(-182452224, [0, 1, 1, 1, 1, 1]),
   (-456130560, [0, 1, 1, 3]),
   (-342097920, [0, 1, 2, 2]),
   (-68419584, [0, 5]),
   (1824522240, [1, 1, 1, 2]),
   (684195840, [1, 4]),
   (456130560, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_12_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_12)) skA_E0_Q5_12 := by decide +kernel

def skA_E0_Q5_13 : SectorVector := [(1,
  [(173015040, [0, 1, 1, 1, 1, 1]),
   (432537600, [0, 1, 1, 3]),
   (324403200, [0, 1, 2, 2]),
   (64880640, [0, 5]),
   (1730150400, [1, 1, 1, 2]),
   (648806400, [1, 4]),
   (432537600, [2, 3])]),
 (-1,
  [(-173015040, [0, 1, 1, 1, 1, 1]),
   (-432537600, [0, 1, 1, 3]),
   (-324403200, [0, 1, 2, 2]),
   (-64880640, [0, 5]),
   (1730150400, [1, 1, 1, 2]),
   (648806400, [1, 4]),
   (432537600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_13_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_13)) skA_E0_Q5_13 := by decide +kernel

def skA_E0_Q5_14 : SectorVector := [(1,
  [((41943040 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((104857600 : Rat)/27, [0, 1, 1, 3]),
   ((26214400 : Rat)/9, [0, 1, 2, 2]),
   ((5242880 : Rat)/9, [0, 5]),
   ((419430400 : Rat)/27, [1, 1, 1, 2]),
   ((52428800 : Rat)/9, [1, 4]),
   ((104857600 : Rat)/27, [2, 3])]),
 (-1,
  [((-41943040 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-104857600 : Rat)/27, [0, 1, 1, 3]),
   ((-26214400 : Rat)/9, [0, 1, 2, 2]),
   ((-5242880 : Rat)/9, [0, 5]),
   ((419430400 : Rat)/27, [1, 1, 1, 2]),
   ((52428800 : Rat)/9, [1, 4]),
   ((104857600 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_14_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_14)) skA_E0_Q5_14 := by decide +kernel

def skA_E0_Q5_15 : SectorVector := [(1,
  [((-364380160 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-910950400 : Rat)/3, [0, 1, 1, 3]),
   (-227737600, [0, 1, 2, 2]),
   (-45547520, [0, 5]),
   ((-3643801600 : Rat)/3, [1, 1, 1, 2]),
   (-455475200, [1, 4]),
   ((-910950400 : Rat)/3, [2, 3])]),
 (-1,
  [((364380160 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((910950400 : Rat)/3, [0, 1, 1, 3]),
   (227737600, [0, 1, 2, 2]),
   (45547520, [0, 5]),
   ((-3643801600 : Rat)/3, [1, 1, 1, 2]),
   (-455475200, [1, 4]),
   ((-910950400 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_15_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_15)) skA_E0_Q5_15 := by decide +kernel

def skA_E0_Q5_16 : SectorVector := [(1,
  [(-7864320, [0, 1, 1, 1, 1, 1]),
   (-19660800, [0, 1, 1, 3]),
   (-14745600, [0, 1, 2, 2]),
   (-2949120, [0, 5]),
   (-78643200, [1, 1, 1, 2]),
   (-29491200, [1, 4]),
   (-19660800, [2, 3])]),
 (-1,
  [(7864320, [0, 1, 1, 1, 1, 1]),
   (19660800, [0, 1, 1, 3]),
   (14745600, [0, 1, 2, 2]),
   (2949120, [0, 5]),
   (-78643200, [1, 1, 1, 2]),
   (-29491200, [1, 4]),
   (-19660800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_16_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_16)) skA_E0_Q5_16 := by decide +kernel

def skA_E0_Q5_17 : SectorVector := [(1,
  [(-68157440, [0, 1, 1, 1, 1, 1]),
   (-170393600, [0, 1, 1, 3]),
   (-127795200, [0, 1, 2, 2]),
   (-25559040, [0, 5]),
   (-681574400, [1, 1, 1, 2]),
   (-255590400, [1, 4]),
   (-170393600, [2, 3])]),
 (-1,
  [(68157440, [0, 1, 1, 1, 1, 1]),
   (170393600, [0, 1, 1, 3]),
   (127795200, [0, 1, 2, 2]),
   (25559040, [0, 5]),
   (-681574400, [1, 1, 1, 2]),
   (-255590400, [1, 4]),
   (-170393600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_17_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_17)) skA_E0_Q5_17 := by decide +kernel

def skA_E0_Q5_18 : SectorVector := [(1,
  [(11796480, [0, 1, 1, 1, 1, 1]),
   (29491200, [0, 1, 1, 3]),
   (22118400, [0, 1, 2, 2]),
   (4423680, [0, 5]),
   (117964800, [1, 1, 1, 2]),
   (44236800, [1, 4]),
   (29491200, [2, 3])]),
 (-1,
  [(-11796480, [0, 1, 1, 1, 1, 1]),
   (-29491200, [0, 1, 1, 3]),
   (-22118400, [0, 1, 2, 2]),
   (-4423680, [0, 5]),
   (117964800, [1, 1, 1, 2]),
   (44236800, [1, 4]),
   (29491200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_18_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_18)) skA_E0_Q5_18 := by decide +kernel

def skA_E0_Q5_19 : SectorVector := [(1,
  [(110100480, [0, 1, 1, 1, 1, 1]),
   (275251200, [0, 1, 1, 3]),
   (206438400, [0, 1, 2, 2]),
   (41287680, [0, 5]),
   (1101004800, [1, 1, 1, 2]),
   (412876800, [1, 4]),
   (275251200, [2, 3])]),
 (-1,
  [(-110100480, [0, 1, 1, 1, 1, 1]),
   (-275251200, [0, 1, 1, 3]),
   (-206438400, [0, 1, 2, 2]),
   (-41287680, [0, 5]),
   (1101004800, [1, 1, 1, 2]),
   (412876800, [1, 4]),
   (275251200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_19_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_19)) skA_E0_Q5_19 := by decide +kernel

def skA_E0_Q5_20 : SectorVector := [(1,
  [(143523840, [0, 1, 1, 1, 1, 1]),
   (358809600, [0, 1, 1, 3]),
   (269107200, [0, 1, 2, 2]),
   (53821440, [0, 5]),
   (1435238400, [1, 1, 1, 2]),
   (538214400, [1, 4]),
   (358809600, [2, 3])]),
 (-1,
  [(-143523840, [0, 1, 1, 1, 1, 1]),
   (-358809600, [0, 1, 1, 3]),
   (-269107200, [0, 1, 2, 2]),
   (-53821440, [0, 5]),
   (1435238400, [1, 1, 1, 2]),
   (538214400, [1, 4]),
   (358809600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_20_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_20)) skA_E0_Q5_20 := by decide +kernel

def skA_E0_Q5_21 : SectorVector := [(1,
  [((379846656 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (189923328, [0, 1, 1, 3]),
   (142442496, [0, 1, 2, 2]),
   ((142442496 : Rat)/5, [0, 5]),
   (759693312, [1, 1, 1, 2]),
   (284884992, [1, 4]),
   (189923328, [2, 3])]),
 (-1,
  [((-379846656 : Rat)/5, [0, 1, 1, 1, 1, 1]),
   (-189923328, [0, 1, 1, 3]),
   (-142442496, [0, 1, 2, 2]),
   ((-142442496 : Rat)/5, [0, 5]),
   (759693312, [1, 1, 1, 2]),
   (284884992, [1, 4]),
   (189923328, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_21_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_21)) skA_E0_Q5_21 := by decide +kernel

def skA_E0_Q5_22 : SectorVector := [(1,
  [(-31457280, [0, 1, 1, 1, 1, 1]),
   (-78643200, [0, 1, 1, 3]),
   (-58982400, [0, 1, 2, 2]),
   (-11796480, [0, 5]),
   (-314572800, [1, 1, 1, 2]),
   (-117964800, [1, 4]),
   (-78643200, [2, 3])]),
 (-1,
  [(31457280, [0, 1, 1, 1, 1, 1]),
   (78643200, [0, 1, 1, 3]),
   (58982400, [0, 1, 2, 2]),
   (11796480, [0, 5]),
   (-314572800, [1, 1, 1, 2]),
   (-117964800, [1, 4]),
   (-78643200, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_22_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_22)) skA_E0_Q5_22 := by decide +kernel

def skA_E0_Q5_23 : SectorVector := [(1,
  [((324403200 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((811008000 : Rat)/7, [0, 1, 1, 3]),
   ((608256000 : Rat)/7, [0, 1, 2, 2]),
   ((121651200 : Rat)/7, [0, 5]),
   ((3244032000 : Rat)/7, [1, 1, 1, 2]),
   ((1216512000 : Rat)/7, [1, 4]),
   ((811008000 : Rat)/7, [2, 3])]),
 (-1,
  [((-324403200 : Rat)/7, [0, 1, 1, 1, 1, 1]),
   ((-811008000 : Rat)/7, [0, 1, 1, 3]),
   ((-608256000 : Rat)/7, [0, 1, 2, 2]),
   ((-121651200 : Rat)/7, [0, 5]),
   ((3244032000 : Rat)/7, [1, 1, 1, 2]),
   ((1216512000 : Rat)/7, [1, 4]),
   ((811008000 : Rat)/7, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_23_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_23)) skA_E0_Q5_23 := by decide +kernel

def skA_E0_Q5_24 : SectorVector := [(1,
  [(102236160, [0, 1, 1, 1, 1, 1]),
   (255590400, [0, 1, 1, 3]),
   (191692800, [0, 1, 2, 2]),
   (38338560, [0, 5]),
   (1022361600, [1, 1, 1, 2]),
   (383385600, [1, 4]),
   (255590400, [2, 3])]),
 (-1,
  [(-102236160, [0, 1, 1, 1, 1, 1]),
   (-255590400, [0, 1, 1, 3]),
   (-191692800, [0, 1, 2, 2]),
   (-38338560, [0, 5]),
   (1022361600, [1, 1, 1, 2]),
   (383385600, [1, 4]),
   (255590400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_24_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_24)) skA_E0_Q5_24 := by decide +kernel

def skA_E0_Q5_25 : SectorVector := [(1,
  [(102629376, [0, 1, 1, 1, 1, 1]),
   (256573440, [0, 1, 1, 3]),
   (192430080, [0, 1, 2, 2]),
   (38486016, [0, 5]),
   (1026293760, [1, 1, 1, 2]),
   (384860160, [1, 4]),
   (256573440, [2, 3])]),
 (-1,
  [(-102629376, [0, 1, 1, 1, 1, 1]),
   (-256573440, [0, 1, 1, 3]),
   (-192430080, [0, 1, 2, 2]),
   (-38486016, [0, 5]),
   (1026293760, [1, 1, 1, 2]),
   (384860160, [1, 4]),
   (256573440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_25_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_25)) skA_E0_Q5_25 := by decide +kernel

def skA_E0_Q5_26 : SectorVector := [(1,
  [(32505856, [0, 1, 1, 1, 1, 1]),
   (81264640, [0, 1, 1, 3]),
   (60948480, [0, 1, 2, 2]),
   (12189696, [0, 5]),
   (325058560, [1, 1, 1, 2]),
   (121896960, [1, 4]),
   (81264640, [2, 3])]),
 (-1,
  [(-32505856, [0, 1, 1, 1, 1, 1]),
   (-81264640, [0, 1, 1, 3]),
   (-60948480, [0, 1, 2, 2]),
   (-12189696, [0, 5]),
   (325058560, [1, 1, 1, 2]),
   (121896960, [1, 4]),
   (81264640, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_26_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_26)) skA_E0_Q5_26 := by decide +kernel

def skA_E0_Q5_27 : SectorVector := [(1,
  [(27525120, [0, 1, 1, 1, 1, 1]),
   (68812800, [0, 1, 1, 3]),
   (51609600, [0, 1, 2, 2]),
   (10321920, [0, 5]),
   (275251200, [1, 1, 1, 2]),
   (103219200, [1, 4]),
   (68812800, [2, 3])]),
 (-1,
  [(-27525120, [0, 1, 1, 1, 1, 1]),
   (-68812800, [0, 1, 1, 3]),
   (-51609600, [0, 1, 2, 2]),
   (-10321920, [0, 5]),
   (275251200, [1, 1, 1, 2]),
   (103219200, [1, 4]),
   (68812800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_27_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_27)) skA_E0_Q5_27 := by decide +kernel

def skA_E0_Q5_28 : SectorVector := [(1,
  [((-570654720 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((-1426636800 : Rat)/11, [0, 1, 1, 3]),
   ((-1069977600 : Rat)/11, [0, 1, 2, 2]),
   ((-213995520 : Rat)/11, [0, 5]),
   ((-5706547200 : Rat)/11, [1, 1, 1, 2]),
   ((-2139955200 : Rat)/11, [1, 4]),
   ((-1426636800 : Rat)/11, [2, 3])]),
 (-1,
  [((570654720 : Rat)/11, [0, 1, 1, 1, 1, 1]),
   ((1426636800 : Rat)/11, [0, 1, 1, 3]),
   ((1069977600 : Rat)/11, [0, 1, 2, 2]),
   ((213995520 : Rat)/11, [0, 5]),
   ((-5706547200 : Rat)/11, [1, 1, 1, 2]),
   ((-2139955200 : Rat)/11, [1, 4]),
   ((-1426636800 : Rat)/11, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_28_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_28)) skA_E0_Q5_28 := by decide +kernel

def skA_E0_Q5_29 : SectorVector := [(1,
  [(-1048576, [0, 1, 1, 1, 1, 1]),
   (-2621440, [0, 1, 1, 3]),
   (-1966080, [0, 1, 2, 2]),
   (-393216, [0, 5]),
   (-10485760, [1, 1, 1, 2]),
   (-3932160, [1, 4]),
   (-2621440, [2, 3])]),
 (-1,
  [(1048576, [0, 1, 1, 1, 1, 1]),
   (2621440, [0, 1, 1, 3]),
   (1966080, [0, 1, 2, 2]),
   (393216, [0, 5]),
   (-10485760, [1, 1, 1, 2]),
   (-3932160, [1, 4]),
   (-2621440, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_29_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_29)) skA_E0_Q5_29 := by decide +kernel

def skA_E0_Q5_30 : SectorVector := [(1,
  [(8192000, [0, 1, 1, 1, 1, 1]),
   (20480000, [0, 1, 1, 3]),
   (15360000, [0, 1, 2, 2]),
   (3072000, [0, 5]),
   (81920000, [1, 1, 1, 2]),
   (30720000, [1, 4]),
   (20480000, [2, 3])]),
 (-1,
  [(-8192000, [0, 1, 1, 1, 1, 1]),
   (-20480000, [0, 1, 1, 3]),
   (-15360000, [0, 1, 2, 2]),
   (-3072000, [0, 5]),
   (81920000, [1, 1, 1, 2]),
   (30720000, [1, 4]),
   (20480000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_30_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_30)) skA_E0_Q5_30 := by decide +kernel

def skA_E0_Q5_31 : SectorVector := [(1,
  [(16908288, [0, 1, 1, 1, 1, 1]),
   (42270720, [0, 1, 1, 3]),
   (31703040, [0, 1, 2, 2]),
   (6340608, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (63406080, [1, 4]),
   (42270720, [2, 3])]),
 (-1,
  [(-16908288, [0, 1, 1, 1, 1, 1]),
   (-42270720, [0, 1, 1, 3]),
   (-31703040, [0, 1, 2, 2]),
   (-6340608, [0, 5]),
   (169082880, [1, 1, 1, 2]),
   (63406080, [1, 4]),
   (42270720, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_31_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_31)) skA_E0_Q5_31 := by decide +kernel

def skA_E0_Q5_32 : SectorVector := [(1,
  [(7372800, [0, 1, 1, 1, 1, 1]),
   (18432000, [0, 1, 1, 3]),
   (13824000, [0, 1, 2, 2]),
   (2764800, [0, 5]),
   (73728000, [1, 1, 1, 2]),
   (27648000, [1, 4]),
   (18432000, [2, 3])]),
 (-1,
  [(-7372800, [0, 1, 1, 1, 1, 1]),
   (-18432000, [0, 1, 1, 3]),
   (-13824000, [0, 1, 2, 2]),
   (-2764800, [0, 5]),
   (73728000, [1, 1, 1, 2]),
   (27648000, [1, 4]),
   (18432000, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_32_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_32)) skA_E0_Q5_32 := by decide +kernel

def skA_E0_Q5_33 : SectorVector := [(1,
  [(7864320, [0, 1, 1, 1, 1, 1]),
   (19660800, [0, 1, 1, 3]),
   (14745600, [0, 1, 2, 2]),
   (2949120, [0, 5]),
   (78643200, [1, 1, 1, 2]),
   (29491200, [1, 4]),
   (19660800, [2, 3])]),
 (-1,
  [(-7864320, [0, 1, 1, 1, 1, 1]),
   (-19660800, [0, 1, 1, 3]),
   (-14745600, [0, 1, 2, 2]),
   (-2949120, [0, 5]),
   (78643200, [1, 1, 1, 2]),
   (29491200, [1, 4]),
   (19660800, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_33_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_33)) skA_E0_Q5_33 := by decide +kernel

def skA_E0_Q5_34 : SectorVector := [(1,
  [(-10174464, [0, 1, 1, 1, 1, 1]),
   (-25436160, [0, 1, 1, 3]),
   (-19077120, [0, 1, 2, 2]),
   (-3815424, [0, 5]),
   (-101744640, [1, 1, 1, 2]),
   (-38154240, [1, 4]),
   (-25436160, [2, 3])]),
 (-1,
  [(10174464, [0, 1, 1, 1, 1, 1]),
   (25436160, [0, 1, 1, 3]),
   (19077120, [0, 1, 2, 2]),
   (3815424, [0, 5]),
   (-101744640, [1, 1, 1, 2]),
   (-38154240, [1, 4]),
   (-25436160, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_34_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_34)) skA_E0_Q5_34 := by decide +kernel

def skA_E0_Q5_35 : SectorVector := [(1,
  [((7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((18022400 : Rat)/27, [0, 1, 1, 3]),
   ((4505600 : Rat)/9, [0, 1, 2, 2]),
   ((901120 : Rat)/9, [0, 5]),
   ((72089600 : Rat)/27, [1, 1, 1, 2]),
   ((9011200 : Rat)/9, [1, 4]),
   ((18022400 : Rat)/27, [2, 3])]),
 (-1,
  [((-7208960 : Rat)/27, [0, 1, 1, 1, 1, 1]),
   ((-18022400 : Rat)/27, [0, 1, 1, 3]),
   ((-4505600 : Rat)/9, [0, 1, 2, 2]),
   ((-901120 : Rat)/9, [0, 5]),
   ((72089600 : Rat)/27, [1, 1, 1, 2]),
   ((9011200 : Rat)/9, [1, 4]),
   ((18022400 : Rat)/27, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_35_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_35)) skA_E0_Q5_35 := by decide +kernel

def skA_E0_Q5_36 : SectorVector := [(1,
  [((6062080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((15155200 : Rat)/3, [0, 1, 1, 3]),
   (3788800, [0, 1, 2, 2]),
   (757760, [0, 5]),
   ((60620800 : Rat)/3, [1, 1, 1, 2]),
   (7577600, [1, 4]),
   ((15155200 : Rat)/3, [2, 3])]),
 (-1,
  [((-6062080 : Rat)/3, [0, 1, 1, 1, 1, 1]),
   ((-15155200 : Rat)/3, [0, 1, 1, 3]),
   (-3788800, [0, 1, 2, 2]),
   (-757760, [0, 5]),
   ((60620800 : Rat)/3, [1, 1, 1, 2]),
   (7577600, [1, 4]),
   ((15155200 : Rat)/3, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_36_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_36)) skA_E0_Q5_36 := by decide +kernel

def skA_E0_Q5_37 : SectorVector := [(1,
  [(7004160, [0, 1, 1, 1, 1, 1]),
   (17510400, [0, 1, 1, 3]),
   (13132800, [0, 1, 2, 2]),
   (2626560, [0, 5]),
   (70041600, [1, 1, 1, 2]),
   (26265600, [1, 4]),
   (17510400, [2, 3])]),
 (-1,
  [(-7004160, [0, 1, 1, 1, 1, 1]),
   (-17510400, [0, 1, 1, 3]),
   (-13132800, [0, 1, 2, 2]),
   (-2626560, [0, 5]),
   (70041600, [1, 1, 1, 2]),
   (26265600, [1, 4]),
   (17510400, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_37_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_37)) skA_E0_Q5_37 := by decide +kernel

def skA_E0_Q5_38 : SectorVector := [(1,
  [(9142272, [0, 1, 1, 1, 1, 1]),
   (22855680, [0, 1, 1, 3]),
   (17141760, [0, 1, 2, 2]),
   (3428352, [0, 5]),
   (91422720, [1, 1, 1, 2]),
   (34283520, [1, 4]),
   (22855680, [2, 3])]),
 (-1,
  [(-9142272, [0, 1, 1, 1, 1, 1]),
   (-22855680, [0, 1, 1, 3]),
   (-17141760, [0, 1, 2, 2]),
   (-3428352, [0, 5]),
   (91422720, [1, 1, 1, 2]),
   (34283520, [1, 4]),
   (22855680, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_38_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_38)) skA_E0_Q5_38 := by decide +kernel

def skA_E0_Q5_39 : SectorVector := [(1,
  [(4874240, [0, 1, 1, 1, 1, 1]),
   (12185600, [0, 1, 1, 3]),
   (9139200, [0, 1, 2, 2]),
   (1827840, [0, 5]),
   (48742400, [1, 1, 1, 2]),
   (18278400, [1, 4]),
   (12185600, [2, 3])]),
 (-1,
  [(-4874240, [0, 1, 1, 1, 1, 1]),
   (-12185600, [0, 1, 1, 3]),
   (-9139200, [0, 1, 2, 2]),
   (-1827840, [0, 5]),
   (48742400, [1, 1, 1, 2]),
   (18278400, [1, 4]),
   (12185600, [2, 3])])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q5_39_cert : VectorCertificate (Tpow 5 (aLeft false (11 : ℤ) skM_E0_39)) skA_E0_Q5_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_5_join : VectorCertificate ([skA_E0_Q5_0, skA_E0_Q5_1, skA_E0_Q5_2, skA_E0_Q5_3, skA_E0_Q5_4, skA_E0_Q5_5, skA_E0_Q5_6, skA_E0_Q5_7, skA_E0_Q5_8, skA_E0_Q5_9, skA_E0_Q5_10, skA_E0_Q5_11, skA_E0_Q5_12, skA_E0_Q5_13, skA_E0_Q5_14, skA_E0_Q5_15, skA_E0_Q5_16, skA_E0_Q5_17, skA_E0_Q5_18, skA_E0_Q5_19, skA_E0_Q5_20, skA_E0_Q5_21, skA_E0_Q5_22, skA_E0_Q5_23, skA_E0_Q5_24, skA_E0_Q5_25, skA_E0_Q5_26, skA_E0_Q5_27, skA_E0_Q5_28, skA_E0_Q5_29, skA_E0_Q5_30, skA_E0_Q5_31, skA_E0_Q5_32, skA_E0_Q5_33, skA_E0_Q5_34, skA_E0_Q5_35, skA_E0_Q5_36, skA_E0_Q5_37, skA_E0_Q5_38, skA_E0_Q5_39] : List SectorVector).flatten skQ_E0_5 := by decide +kernel

theorem skQ_E0_5_val : evaluate skQ_E0_5 = evaluate (OrbSgl.vTerm false skY_E0 0 5) :=
  vTerm_of_chunks false skY_E0 0 5 (11 : ℤ) (by norm_num) skM_E0 [skA_E0_Q5_0, skA_E0_Q5_1, skA_E0_Q5_2, skA_E0_Q5_3, skA_E0_Q5_4, skA_E0_Q5_5, skA_E0_Q5_6, skA_E0_Q5_7, skA_E0_Q5_8, skA_E0_Q5_9, skA_E0_Q5_10, skA_E0_Q5_11, skA_E0_Q5_12, skA_E0_Q5_13, skA_E0_Q5_14, skA_E0_Q5_15, skA_E0_Q5_16, skA_E0_Q5_17, skA_E0_Q5_18, skA_E0_Q5_19, skA_E0_Q5_20, skA_E0_Q5_21, skA_E0_Q5_22, skA_E0_Q5_23, skA_E0_Q5_24, skA_E0_Q5_25, skA_E0_Q5_26, skA_E0_Q5_27, skA_E0_Q5_28, skA_E0_Q5_29, skA_E0_Q5_30, skA_E0_Q5_31, skA_E0_Q5_32, skA_E0_Q5_33, skA_E0_Q5_34, skA_E0_Q5_35, skA_E0_Q5_36, skA_E0_Q5_37, skA_E0_Q5_38, skA_E0_Q5_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q5_0_cert (List.Forall₂.cons skA_E0_Q5_1_cert (List.Forall₂.cons skA_E0_Q5_2_cert (List.Forall₂.cons skA_E0_Q5_3_cert (List.Forall₂.cons skA_E0_Q5_4_cert (List.Forall₂.cons skA_E0_Q5_5_cert (List.Forall₂.cons skA_E0_Q5_6_cert (List.Forall₂.cons skA_E0_Q5_7_cert (List.Forall₂.cons skA_E0_Q5_8_cert (List.Forall₂.cons skA_E0_Q5_9_cert (List.Forall₂.cons skA_E0_Q5_10_cert (List.Forall₂.cons skA_E0_Q5_11_cert (List.Forall₂.cons skA_E0_Q5_12_cert (List.Forall₂.cons skA_E0_Q5_13_cert (List.Forall₂.cons skA_E0_Q5_14_cert (List.Forall₂.cons skA_E0_Q5_15_cert (List.Forall₂.cons skA_E0_Q5_16_cert (List.Forall₂.cons skA_E0_Q5_17_cert (List.Forall₂.cons skA_E0_Q5_18_cert (List.Forall₂.cons skA_E0_Q5_19_cert (List.Forall₂.cons skA_E0_Q5_20_cert (List.Forall₂.cons skA_E0_Q5_21_cert (List.Forall₂.cons skA_E0_Q5_22_cert (List.Forall₂.cons skA_E0_Q5_23_cert (List.Forall₂.cons skA_E0_Q5_24_cert (List.Forall₂.cons skA_E0_Q5_25_cert (List.Forall₂.cons skA_E0_Q5_26_cert (List.Forall₂.cons skA_E0_Q5_27_cert (List.Forall₂.cons skA_E0_Q5_28_cert (List.Forall₂.cons skA_E0_Q5_29_cert (List.Forall₂.cons skA_E0_Q5_30_cert (List.Forall₂.cons skA_E0_Q5_31_cert (List.Forall₂.cons skA_E0_Q5_32_cert (List.Forall₂.cons skA_E0_Q5_33_cert (List.Forall₂.cons skA_E0_Q5_34_cert (List.Forall₂.cons skA_E0_Q5_35_cert (List.Forall₂.cons skA_E0_Q5_36_cert (List.Forall₂.cons skA_E0_Q5_37_cert (List.Forall₂.cons skA_E0_Q5_38_cert (List.Forall₂.cons skA_E0_Q5_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_5 skQ_E0_5_join

def skA_E0_Q6_0 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_0_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_0)) skA_E0_Q6_0 := by decide +kernel

def skA_E0_Q6_1 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_1_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_1)) skA_E0_Q6_1 := by decide +kernel

def skA_E0_Q6_2 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_2_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_2)) skA_E0_Q6_2 := by decide +kernel

def skA_E0_Q6_3 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_3_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_3)) skA_E0_Q6_3 := by decide +kernel

def skA_E0_Q6_4 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_4_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_4)) skA_E0_Q6_4 := by decide +kernel

def skA_E0_Q6_5 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_5_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_5)) skA_E0_Q6_5 := by decide +kernel

def skA_E0_Q6_6 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_6_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_6)) skA_E0_Q6_6 := by decide +kernel

def skA_E0_Q6_7 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_7_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_7)) skA_E0_Q6_7 := by decide +kernel

def skA_E0_Q6_8 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_8_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_8)) skA_E0_Q6_8 := by decide +kernel

def skA_E0_Q6_9 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_9_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_9)) skA_E0_Q6_9 := by decide +kernel

def skA_E0_Q6_10 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_10_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_10)) skA_E0_Q6_10 := by decide +kernel

def skA_E0_Q6_11 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_11_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_11)) skA_E0_Q6_11 := by decide +kernel

def skA_E0_Q6_12 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_12_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_12)) skA_E0_Q6_12 := by decide +kernel

def skA_E0_Q6_13 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_13_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_13)) skA_E0_Q6_13 := by decide +kernel

def skA_E0_Q6_14 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_14_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_14)) skA_E0_Q6_14 := by decide +kernel

def skA_E0_Q6_15 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_15_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_15)) skA_E0_Q6_15 := by decide +kernel

def skA_E0_Q6_16 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_16_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_16)) skA_E0_Q6_16 := by decide +kernel

def skA_E0_Q6_17 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_17_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_17)) skA_E0_Q6_17 := by decide +kernel

def skA_E0_Q6_18 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_18_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_18)) skA_E0_Q6_18 := by decide +kernel

def skA_E0_Q6_19 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_19_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_19)) skA_E0_Q6_19 := by decide +kernel

def skA_E0_Q6_20 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_20_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_20)) skA_E0_Q6_20 := by decide +kernel

def skA_E0_Q6_21 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_21_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_21)) skA_E0_Q6_21 := by decide +kernel

def skA_E0_Q6_22 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_22_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_22)) skA_E0_Q6_22 := by decide +kernel

def skA_E0_Q6_23 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_23_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_23)) skA_E0_Q6_23 := by decide +kernel

def skA_E0_Q6_24 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_24_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_24)) skA_E0_Q6_24 := by decide +kernel

def skA_E0_Q6_25 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_25_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_25)) skA_E0_Q6_25 := by decide +kernel

def skA_E0_Q6_26 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_26_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_26)) skA_E0_Q6_26 := by decide +kernel

def skA_E0_Q6_27 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_27_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_27)) skA_E0_Q6_27 := by decide +kernel

def skA_E0_Q6_28 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_28_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_28)) skA_E0_Q6_28 := by decide +kernel

def skA_E0_Q6_29 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_29_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_29)) skA_E0_Q6_29 := by decide +kernel

def skA_E0_Q6_30 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_30_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_30)) skA_E0_Q6_30 := by decide +kernel

def skA_E0_Q6_31 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_31_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_31)) skA_E0_Q6_31 := by decide +kernel

def skA_E0_Q6_32 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_32_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_32)) skA_E0_Q6_32 := by decide +kernel

def skA_E0_Q6_33 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_33_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_33)) skA_E0_Q6_33 := by decide +kernel

def skA_E0_Q6_34 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_34_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_34)) skA_E0_Q6_34 := by decide +kernel

def skA_E0_Q6_35 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_35_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_35)) skA_E0_Q6_35 := by decide +kernel

def skA_E0_Q6_36 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_36_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_36)) skA_E0_Q6_36 := by decide +kernel

def skA_E0_Q6_37 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_37_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_37)) skA_E0_Q6_37 := by decide +kernel

def skA_E0_Q6_38 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_38_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_38)) skA_E0_Q6_38 := by decide +kernel

def skA_E0_Q6_39 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q6_39_cert : VectorCertificate (Tpow 6 (aLeft false (12 : ℤ) skM_E0_39)) skA_E0_Q6_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_6_join : VectorCertificate ([skA_E0_Q6_0, skA_E0_Q6_1, skA_E0_Q6_2, skA_E0_Q6_3, skA_E0_Q6_4, skA_E0_Q6_5, skA_E0_Q6_6, skA_E0_Q6_7, skA_E0_Q6_8, skA_E0_Q6_9, skA_E0_Q6_10, skA_E0_Q6_11, skA_E0_Q6_12, skA_E0_Q6_13, skA_E0_Q6_14, skA_E0_Q6_15, skA_E0_Q6_16, skA_E0_Q6_17, skA_E0_Q6_18, skA_E0_Q6_19, skA_E0_Q6_20, skA_E0_Q6_21, skA_E0_Q6_22, skA_E0_Q6_23, skA_E0_Q6_24, skA_E0_Q6_25, skA_E0_Q6_26, skA_E0_Q6_27, skA_E0_Q6_28, skA_E0_Q6_29, skA_E0_Q6_30, skA_E0_Q6_31, skA_E0_Q6_32, skA_E0_Q6_33, skA_E0_Q6_34, skA_E0_Q6_35, skA_E0_Q6_36, skA_E0_Q6_37, skA_E0_Q6_38, skA_E0_Q6_39] : List SectorVector).flatten skQ_E0_6 := by decide +kernel

theorem skQ_E0_6_val : evaluate skQ_E0_6 = evaluate (OrbSgl.vTerm false skY_E0 0 6) :=
  vTerm_of_chunks false skY_E0 0 6 (12 : ℤ) (by norm_num) skM_E0 [skA_E0_Q6_0, skA_E0_Q6_1, skA_E0_Q6_2, skA_E0_Q6_3, skA_E0_Q6_4, skA_E0_Q6_5, skA_E0_Q6_6, skA_E0_Q6_7, skA_E0_Q6_8, skA_E0_Q6_9, skA_E0_Q6_10, skA_E0_Q6_11, skA_E0_Q6_12, skA_E0_Q6_13, skA_E0_Q6_14, skA_E0_Q6_15, skA_E0_Q6_16, skA_E0_Q6_17, skA_E0_Q6_18, skA_E0_Q6_19, skA_E0_Q6_20, skA_E0_Q6_21, skA_E0_Q6_22, skA_E0_Q6_23, skA_E0_Q6_24, skA_E0_Q6_25, skA_E0_Q6_26, skA_E0_Q6_27, skA_E0_Q6_28, skA_E0_Q6_29, skA_E0_Q6_30, skA_E0_Q6_31, skA_E0_Q6_32, skA_E0_Q6_33, skA_E0_Q6_34, skA_E0_Q6_35, skA_E0_Q6_36, skA_E0_Q6_37, skA_E0_Q6_38, skA_E0_Q6_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q6_0_cert (List.Forall₂.cons skA_E0_Q6_1_cert (List.Forall₂.cons skA_E0_Q6_2_cert (List.Forall₂.cons skA_E0_Q6_3_cert (List.Forall₂.cons skA_E0_Q6_4_cert (List.Forall₂.cons skA_E0_Q6_5_cert (List.Forall₂.cons skA_E0_Q6_6_cert (List.Forall₂.cons skA_E0_Q6_7_cert (List.Forall₂.cons skA_E0_Q6_8_cert (List.Forall₂.cons skA_E0_Q6_9_cert (List.Forall₂.cons skA_E0_Q6_10_cert (List.Forall₂.cons skA_E0_Q6_11_cert (List.Forall₂.cons skA_E0_Q6_12_cert (List.Forall₂.cons skA_E0_Q6_13_cert (List.Forall₂.cons skA_E0_Q6_14_cert (List.Forall₂.cons skA_E0_Q6_15_cert (List.Forall₂.cons skA_E0_Q6_16_cert (List.Forall₂.cons skA_E0_Q6_17_cert (List.Forall₂.cons skA_E0_Q6_18_cert (List.Forall₂.cons skA_E0_Q6_19_cert (List.Forall₂.cons skA_E0_Q6_20_cert (List.Forall₂.cons skA_E0_Q6_21_cert (List.Forall₂.cons skA_E0_Q6_22_cert (List.Forall₂.cons skA_E0_Q6_23_cert (List.Forall₂.cons skA_E0_Q6_24_cert (List.Forall₂.cons skA_E0_Q6_25_cert (List.Forall₂.cons skA_E0_Q6_26_cert (List.Forall₂.cons skA_E0_Q6_27_cert (List.Forall₂.cons skA_E0_Q6_28_cert (List.Forall₂.cons skA_E0_Q6_29_cert (List.Forall₂.cons skA_E0_Q6_30_cert (List.Forall₂.cons skA_E0_Q6_31_cert (List.Forall₂.cons skA_E0_Q6_32_cert (List.Forall₂.cons skA_E0_Q6_33_cert (List.Forall₂.cons skA_E0_Q6_34_cert (List.Forall₂.cons skA_E0_Q6_35_cert (List.Forall₂.cons skA_E0_Q6_36_cert (List.Forall₂.cons skA_E0_Q6_37_cert (List.Forall₂.cons skA_E0_Q6_38_cert (List.Forall₂.cons skA_E0_Q6_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_6 skQ_E0_6_join

def skA_E0_Q7_0 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_0_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_0)) skA_E0_Q7_0 := by decide +kernel

def skA_E0_Q7_1 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_1_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_1)) skA_E0_Q7_1 := by decide +kernel

def skA_E0_Q7_2 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_2_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_2)) skA_E0_Q7_2 := by decide +kernel

def skA_E0_Q7_3 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_3_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_3)) skA_E0_Q7_3 := by decide +kernel

def skA_E0_Q7_4 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_4_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_4)) skA_E0_Q7_4 := by decide +kernel

def skA_E0_Q7_5 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_5_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_5)) skA_E0_Q7_5 := by decide +kernel

def skA_E0_Q7_6 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_6_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_6)) skA_E0_Q7_6 := by decide +kernel

def skA_E0_Q7_7 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_7_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_7)) skA_E0_Q7_7 := by decide +kernel

def skA_E0_Q7_8 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_8_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_8)) skA_E0_Q7_8 := by decide +kernel

def skA_E0_Q7_9 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_9_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_9)) skA_E0_Q7_9 := by decide +kernel

def skA_E0_Q7_10 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_10_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_10)) skA_E0_Q7_10 := by decide +kernel

def skA_E0_Q7_11 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_11_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_11)) skA_E0_Q7_11 := by decide +kernel

def skA_E0_Q7_12 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_12_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_12)) skA_E0_Q7_12 := by decide +kernel

def skA_E0_Q7_13 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_13_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_13)) skA_E0_Q7_13 := by decide +kernel

def skA_E0_Q7_14 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_14_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_14)) skA_E0_Q7_14 := by decide +kernel

def skA_E0_Q7_15 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_15_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_15)) skA_E0_Q7_15 := by decide +kernel

def skA_E0_Q7_16 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_16_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_16)) skA_E0_Q7_16 := by decide +kernel

def skA_E0_Q7_17 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_17_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_17)) skA_E0_Q7_17 := by decide +kernel

def skA_E0_Q7_18 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_18_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_18)) skA_E0_Q7_18 := by decide +kernel

def skA_E0_Q7_19 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_19_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_19)) skA_E0_Q7_19 := by decide +kernel

def skA_E0_Q7_20 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_20_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_20)) skA_E0_Q7_20 := by decide +kernel

def skA_E0_Q7_21 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_21_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_21)) skA_E0_Q7_21 := by decide +kernel

def skA_E0_Q7_22 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_22_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_22)) skA_E0_Q7_22 := by decide +kernel

def skA_E0_Q7_23 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_23_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_23)) skA_E0_Q7_23 := by decide +kernel

def skA_E0_Q7_24 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_24_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_24)) skA_E0_Q7_24 := by decide +kernel

def skA_E0_Q7_25 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_25_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_25)) skA_E0_Q7_25 := by decide +kernel

def skA_E0_Q7_26 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_26_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_26)) skA_E0_Q7_26 := by decide +kernel

def skA_E0_Q7_27 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_27_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_27)) skA_E0_Q7_27 := by decide +kernel

def skA_E0_Q7_28 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_28_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_28)) skA_E0_Q7_28 := by decide +kernel

def skA_E0_Q7_29 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_29_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_29)) skA_E0_Q7_29 := by decide +kernel

def skA_E0_Q7_30 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_30_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_30)) skA_E0_Q7_30 := by decide +kernel

def skA_E0_Q7_31 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_31_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_31)) skA_E0_Q7_31 := by decide +kernel

def skA_E0_Q7_32 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_32_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_32)) skA_E0_Q7_32 := by decide +kernel

def skA_E0_Q7_33 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_33_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_33)) skA_E0_Q7_33 := by decide +kernel

def skA_E0_Q7_34 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_34_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_34)) skA_E0_Q7_34 := by decide +kernel

def skA_E0_Q7_35 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_35_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_35)) skA_E0_Q7_35 := by decide +kernel

def skA_E0_Q7_36 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_36_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_36)) skA_E0_Q7_36 := by decide +kernel

def skA_E0_Q7_37 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_37_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_37)) skA_E0_Q7_37 := by decide +kernel

def skA_E0_Q7_38 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_38_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_38)) skA_E0_Q7_38 := by decide +kernel

def skA_E0_Q7_39 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q7_39_cert : VectorCertificate (Tpow 7 (aLeft false (13 : ℤ) skM_E0_39)) skA_E0_Q7_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_7_join : VectorCertificate ([skA_E0_Q7_0, skA_E0_Q7_1, skA_E0_Q7_2, skA_E0_Q7_3, skA_E0_Q7_4, skA_E0_Q7_5, skA_E0_Q7_6, skA_E0_Q7_7, skA_E0_Q7_8, skA_E0_Q7_9, skA_E0_Q7_10, skA_E0_Q7_11, skA_E0_Q7_12, skA_E0_Q7_13, skA_E0_Q7_14, skA_E0_Q7_15, skA_E0_Q7_16, skA_E0_Q7_17, skA_E0_Q7_18, skA_E0_Q7_19, skA_E0_Q7_20, skA_E0_Q7_21, skA_E0_Q7_22, skA_E0_Q7_23, skA_E0_Q7_24, skA_E0_Q7_25, skA_E0_Q7_26, skA_E0_Q7_27, skA_E0_Q7_28, skA_E0_Q7_29, skA_E0_Q7_30, skA_E0_Q7_31, skA_E0_Q7_32, skA_E0_Q7_33, skA_E0_Q7_34, skA_E0_Q7_35, skA_E0_Q7_36, skA_E0_Q7_37, skA_E0_Q7_38, skA_E0_Q7_39] : List SectorVector).flatten skQ_E0_7 := by decide +kernel

theorem skQ_E0_7_val : evaluate skQ_E0_7 = evaluate (OrbSgl.vTerm false skY_E0 0 7) :=
  vTerm_of_chunks false skY_E0 0 7 (13 : ℤ) (by norm_num) skM_E0 [skA_E0_Q7_0, skA_E0_Q7_1, skA_E0_Q7_2, skA_E0_Q7_3, skA_E0_Q7_4, skA_E0_Q7_5, skA_E0_Q7_6, skA_E0_Q7_7, skA_E0_Q7_8, skA_E0_Q7_9, skA_E0_Q7_10, skA_E0_Q7_11, skA_E0_Q7_12, skA_E0_Q7_13, skA_E0_Q7_14, skA_E0_Q7_15, skA_E0_Q7_16, skA_E0_Q7_17, skA_E0_Q7_18, skA_E0_Q7_19, skA_E0_Q7_20, skA_E0_Q7_21, skA_E0_Q7_22, skA_E0_Q7_23, skA_E0_Q7_24, skA_E0_Q7_25, skA_E0_Q7_26, skA_E0_Q7_27, skA_E0_Q7_28, skA_E0_Q7_29, skA_E0_Q7_30, skA_E0_Q7_31, skA_E0_Q7_32, skA_E0_Q7_33, skA_E0_Q7_34, skA_E0_Q7_35, skA_E0_Q7_36, skA_E0_Q7_37, skA_E0_Q7_38, skA_E0_Q7_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q7_0_cert (List.Forall₂.cons skA_E0_Q7_1_cert (List.Forall₂.cons skA_E0_Q7_2_cert (List.Forall₂.cons skA_E0_Q7_3_cert (List.Forall₂.cons skA_E0_Q7_4_cert (List.Forall₂.cons skA_E0_Q7_5_cert (List.Forall₂.cons skA_E0_Q7_6_cert (List.Forall₂.cons skA_E0_Q7_7_cert (List.Forall₂.cons skA_E0_Q7_8_cert (List.Forall₂.cons skA_E0_Q7_9_cert (List.Forall₂.cons skA_E0_Q7_10_cert (List.Forall₂.cons skA_E0_Q7_11_cert (List.Forall₂.cons skA_E0_Q7_12_cert (List.Forall₂.cons skA_E0_Q7_13_cert (List.Forall₂.cons skA_E0_Q7_14_cert (List.Forall₂.cons skA_E0_Q7_15_cert (List.Forall₂.cons skA_E0_Q7_16_cert (List.Forall₂.cons skA_E0_Q7_17_cert (List.Forall₂.cons skA_E0_Q7_18_cert (List.Forall₂.cons skA_E0_Q7_19_cert (List.Forall₂.cons skA_E0_Q7_20_cert (List.Forall₂.cons skA_E0_Q7_21_cert (List.Forall₂.cons skA_E0_Q7_22_cert (List.Forall₂.cons skA_E0_Q7_23_cert (List.Forall₂.cons skA_E0_Q7_24_cert (List.Forall₂.cons skA_E0_Q7_25_cert (List.Forall₂.cons skA_E0_Q7_26_cert (List.Forall₂.cons skA_E0_Q7_27_cert (List.Forall₂.cons skA_E0_Q7_28_cert (List.Forall₂.cons skA_E0_Q7_29_cert (List.Forall₂.cons skA_E0_Q7_30_cert (List.Forall₂.cons skA_E0_Q7_31_cert (List.Forall₂.cons skA_E0_Q7_32_cert (List.Forall₂.cons skA_E0_Q7_33_cert (List.Forall₂.cons skA_E0_Q7_34_cert (List.Forall₂.cons skA_E0_Q7_35_cert (List.Forall₂.cons skA_E0_Q7_36_cert (List.Forall₂.cons skA_E0_Q7_37_cert (List.Forall₂.cons skA_E0_Q7_38_cert (List.Forall₂.cons skA_E0_Q7_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_7 skQ_E0_7_join

def skA_E0_Q8_0 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_0_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_0)) skA_E0_Q8_0 := by decide +kernel

def skA_E0_Q8_1 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_1_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_1)) skA_E0_Q8_1 := by decide +kernel

def skA_E0_Q8_2 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_2_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_2)) skA_E0_Q8_2 := by decide +kernel

def skA_E0_Q8_3 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_3_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_3)) skA_E0_Q8_3 := by decide +kernel

def skA_E0_Q8_4 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_4_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_4)) skA_E0_Q8_4 := by decide +kernel

def skA_E0_Q8_5 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_5_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_5)) skA_E0_Q8_5 := by decide +kernel

def skA_E0_Q8_6 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_6_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_6)) skA_E0_Q8_6 := by decide +kernel

def skA_E0_Q8_7 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_7_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_7)) skA_E0_Q8_7 := by decide +kernel

def skA_E0_Q8_8 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_8_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_8)) skA_E0_Q8_8 := by decide +kernel

def skA_E0_Q8_9 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_9_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_9)) skA_E0_Q8_9 := by decide +kernel

def skA_E0_Q8_10 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_10_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_10)) skA_E0_Q8_10 := by decide +kernel

def skA_E0_Q8_11 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_11_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_11)) skA_E0_Q8_11 := by decide +kernel

def skA_E0_Q8_12 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_12_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_12)) skA_E0_Q8_12 := by decide +kernel

def skA_E0_Q8_13 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_13_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_13)) skA_E0_Q8_13 := by decide +kernel

def skA_E0_Q8_14 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_14_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_14)) skA_E0_Q8_14 := by decide +kernel

def skA_E0_Q8_15 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_15_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_15)) skA_E0_Q8_15 := by decide +kernel

def skA_E0_Q8_16 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_16_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_16)) skA_E0_Q8_16 := by decide +kernel

def skA_E0_Q8_17 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_17_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_17)) skA_E0_Q8_17 := by decide +kernel

def skA_E0_Q8_18 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_18_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_18)) skA_E0_Q8_18 := by decide +kernel

def skA_E0_Q8_19 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_19_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_19)) skA_E0_Q8_19 := by decide +kernel

def skA_E0_Q8_20 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_20_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_20)) skA_E0_Q8_20 := by decide +kernel

def skA_E0_Q8_21 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_21_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_21)) skA_E0_Q8_21 := by decide +kernel

def skA_E0_Q8_22 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_22_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_22)) skA_E0_Q8_22 := by decide +kernel

def skA_E0_Q8_23 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_23_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_23)) skA_E0_Q8_23 := by decide +kernel

def skA_E0_Q8_24 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_24_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_24)) skA_E0_Q8_24 := by decide +kernel

def skA_E0_Q8_25 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_25_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_25)) skA_E0_Q8_25 := by decide +kernel

def skA_E0_Q8_26 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_26_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_26)) skA_E0_Q8_26 := by decide +kernel

def skA_E0_Q8_27 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_27_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_27)) skA_E0_Q8_27 := by decide +kernel

def skA_E0_Q8_28 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_28_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_28)) skA_E0_Q8_28 := by decide +kernel

def skA_E0_Q8_29 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_29_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_29)) skA_E0_Q8_29 := by decide +kernel

def skA_E0_Q8_30 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_30_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_30)) skA_E0_Q8_30 := by decide +kernel

def skA_E0_Q8_31 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_31_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_31)) skA_E0_Q8_31 := by decide +kernel

def skA_E0_Q8_32 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_32_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_32)) skA_E0_Q8_32 := by decide +kernel

def skA_E0_Q8_33 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_33_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_33)) skA_E0_Q8_33 := by decide +kernel

def skA_E0_Q8_34 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_34_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_34)) skA_E0_Q8_34 := by decide +kernel

def skA_E0_Q8_35 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_35_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_35)) skA_E0_Q8_35 := by decide +kernel

def skA_E0_Q8_36 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_36_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_36)) skA_E0_Q8_36 := by decide +kernel

def skA_E0_Q8_37 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_37_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_37)) skA_E0_Q8_37 := by decide +kernel

def skA_E0_Q8_38 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_38_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_38)) skA_E0_Q8_38 := by decide +kernel

def skA_E0_Q8_39 : SectorVector := [(-1, []), (1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q8_39_cert : VectorCertificate (Tpow 8 (aLeft false (14 : ℤ) skM_E0_39)) skA_E0_Q8_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_8_join : VectorCertificate ([skA_E0_Q8_0, skA_E0_Q8_1, skA_E0_Q8_2, skA_E0_Q8_3, skA_E0_Q8_4, skA_E0_Q8_5, skA_E0_Q8_6, skA_E0_Q8_7, skA_E0_Q8_8, skA_E0_Q8_9, skA_E0_Q8_10, skA_E0_Q8_11, skA_E0_Q8_12, skA_E0_Q8_13, skA_E0_Q8_14, skA_E0_Q8_15, skA_E0_Q8_16, skA_E0_Q8_17, skA_E0_Q8_18, skA_E0_Q8_19, skA_E0_Q8_20, skA_E0_Q8_21, skA_E0_Q8_22, skA_E0_Q8_23, skA_E0_Q8_24, skA_E0_Q8_25, skA_E0_Q8_26, skA_E0_Q8_27, skA_E0_Q8_28, skA_E0_Q8_29, skA_E0_Q8_30, skA_E0_Q8_31, skA_E0_Q8_32, skA_E0_Q8_33, skA_E0_Q8_34, skA_E0_Q8_35, skA_E0_Q8_36, skA_E0_Q8_37, skA_E0_Q8_38, skA_E0_Q8_39] : List SectorVector).flatten skQ_E0_8 := by decide +kernel

theorem skQ_E0_8_val : evaluate skQ_E0_8 = evaluate (OrbSgl.vTerm false skY_E0 0 8) :=
  vTerm_of_chunks false skY_E0 0 8 (14 : ℤ) (by norm_num) skM_E0 [skA_E0_Q8_0, skA_E0_Q8_1, skA_E0_Q8_2, skA_E0_Q8_3, skA_E0_Q8_4, skA_E0_Q8_5, skA_E0_Q8_6, skA_E0_Q8_7, skA_E0_Q8_8, skA_E0_Q8_9, skA_E0_Q8_10, skA_E0_Q8_11, skA_E0_Q8_12, skA_E0_Q8_13, skA_E0_Q8_14, skA_E0_Q8_15, skA_E0_Q8_16, skA_E0_Q8_17, skA_E0_Q8_18, skA_E0_Q8_19, skA_E0_Q8_20, skA_E0_Q8_21, skA_E0_Q8_22, skA_E0_Q8_23, skA_E0_Q8_24, skA_E0_Q8_25, skA_E0_Q8_26, skA_E0_Q8_27, skA_E0_Q8_28, skA_E0_Q8_29, skA_E0_Q8_30, skA_E0_Q8_31, skA_E0_Q8_32, skA_E0_Q8_33, skA_E0_Q8_34, skA_E0_Q8_35, skA_E0_Q8_36, skA_E0_Q8_37, skA_E0_Q8_38, skA_E0_Q8_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q8_0_cert (List.Forall₂.cons skA_E0_Q8_1_cert (List.Forall₂.cons skA_E0_Q8_2_cert (List.Forall₂.cons skA_E0_Q8_3_cert (List.Forall₂.cons skA_E0_Q8_4_cert (List.Forall₂.cons skA_E0_Q8_5_cert (List.Forall₂.cons skA_E0_Q8_6_cert (List.Forall₂.cons skA_E0_Q8_7_cert (List.Forall₂.cons skA_E0_Q8_8_cert (List.Forall₂.cons skA_E0_Q8_9_cert (List.Forall₂.cons skA_E0_Q8_10_cert (List.Forall₂.cons skA_E0_Q8_11_cert (List.Forall₂.cons skA_E0_Q8_12_cert (List.Forall₂.cons skA_E0_Q8_13_cert (List.Forall₂.cons skA_E0_Q8_14_cert (List.Forall₂.cons skA_E0_Q8_15_cert (List.Forall₂.cons skA_E0_Q8_16_cert (List.Forall₂.cons skA_E0_Q8_17_cert (List.Forall₂.cons skA_E0_Q8_18_cert (List.Forall₂.cons skA_E0_Q8_19_cert (List.Forall₂.cons skA_E0_Q8_20_cert (List.Forall₂.cons skA_E0_Q8_21_cert (List.Forall₂.cons skA_E0_Q8_22_cert (List.Forall₂.cons skA_E0_Q8_23_cert (List.Forall₂.cons skA_E0_Q8_24_cert (List.Forall₂.cons skA_E0_Q8_25_cert (List.Forall₂.cons skA_E0_Q8_26_cert (List.Forall₂.cons skA_E0_Q8_27_cert (List.Forall₂.cons skA_E0_Q8_28_cert (List.Forall₂.cons skA_E0_Q8_29_cert (List.Forall₂.cons skA_E0_Q8_30_cert (List.Forall₂.cons skA_E0_Q8_31_cert (List.Forall₂.cons skA_E0_Q8_32_cert (List.Forall₂.cons skA_E0_Q8_33_cert (List.Forall₂.cons skA_E0_Q8_34_cert (List.Forall₂.cons skA_E0_Q8_35_cert (List.Forall₂.cons skA_E0_Q8_36_cert (List.Forall₂.cons skA_E0_Q8_37_cert (List.Forall₂.cons skA_E0_Q8_38_cert (List.Forall₂.cons skA_E0_Q8_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_8 skQ_E0_8_join

def skA_E0_Q9_0 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_0_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_0)) skA_E0_Q9_0 := by decide +kernel

def skA_E0_Q9_1 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_1_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_1)) skA_E0_Q9_1 := by decide +kernel

def skA_E0_Q9_2 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_2_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_2)) skA_E0_Q9_2 := by decide +kernel

def skA_E0_Q9_3 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_3_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_3)) skA_E0_Q9_3 := by decide +kernel

def skA_E0_Q9_4 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_4_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_4)) skA_E0_Q9_4 := by decide +kernel

def skA_E0_Q9_5 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_5_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_5)) skA_E0_Q9_5 := by decide +kernel

def skA_E0_Q9_6 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_6_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_6)) skA_E0_Q9_6 := by decide +kernel

def skA_E0_Q9_7 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_7_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_7)) skA_E0_Q9_7 := by decide +kernel

def skA_E0_Q9_8 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_8_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_8)) skA_E0_Q9_8 := by decide +kernel

def skA_E0_Q9_9 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_9_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_9)) skA_E0_Q9_9 := by decide +kernel

def skA_E0_Q9_10 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_10_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_10)) skA_E0_Q9_10 := by decide +kernel

def skA_E0_Q9_11 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_11_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_11)) skA_E0_Q9_11 := by decide +kernel

def skA_E0_Q9_12 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_12_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_12)) skA_E0_Q9_12 := by decide +kernel

def skA_E0_Q9_13 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_13_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_13)) skA_E0_Q9_13 := by decide +kernel

def skA_E0_Q9_14 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_14_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_14)) skA_E0_Q9_14 := by decide +kernel

def skA_E0_Q9_15 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_15_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_15)) skA_E0_Q9_15 := by decide +kernel

def skA_E0_Q9_16 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_16_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_16)) skA_E0_Q9_16 := by decide +kernel

def skA_E0_Q9_17 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_17_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_17)) skA_E0_Q9_17 := by decide +kernel

def skA_E0_Q9_18 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_18_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_18)) skA_E0_Q9_18 := by decide +kernel

def skA_E0_Q9_19 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_19_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_19)) skA_E0_Q9_19 := by decide +kernel

def skA_E0_Q9_20 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_20_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_20)) skA_E0_Q9_20 := by decide +kernel

def skA_E0_Q9_21 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_21_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_21)) skA_E0_Q9_21 := by decide +kernel

def skA_E0_Q9_22 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_22_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_22)) skA_E0_Q9_22 := by decide +kernel

def skA_E0_Q9_23 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_23_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_23)) skA_E0_Q9_23 := by decide +kernel

def skA_E0_Q9_24 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_24_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_24)) skA_E0_Q9_24 := by decide +kernel

def skA_E0_Q9_25 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_25_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_25)) skA_E0_Q9_25 := by decide +kernel

def skA_E0_Q9_26 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_26_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_26)) skA_E0_Q9_26 := by decide +kernel

def skA_E0_Q9_27 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_27_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_27)) skA_E0_Q9_27 := by decide +kernel

def skA_E0_Q9_28 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_28_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_28)) skA_E0_Q9_28 := by decide +kernel

def skA_E0_Q9_29 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_29_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_29)) skA_E0_Q9_29 := by decide +kernel

def skA_E0_Q9_30 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_30_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_30)) skA_E0_Q9_30 := by decide +kernel

def skA_E0_Q9_31 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_31_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_31)) skA_E0_Q9_31 := by decide +kernel

def skA_E0_Q9_32 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_32_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_32)) skA_E0_Q9_32 := by decide +kernel

def skA_E0_Q9_33 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_33_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_33)) skA_E0_Q9_33 := by decide +kernel

def skA_E0_Q9_34 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_34_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_34)) skA_E0_Q9_34 := by decide +kernel

def skA_E0_Q9_35 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_35_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_35)) skA_E0_Q9_35 := by decide +kernel

def skA_E0_Q9_36 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_36_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_36)) skA_E0_Q9_36 := by decide +kernel

def skA_E0_Q9_37 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_37_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_37)) skA_E0_Q9_37 := by decide +kernel

def skA_E0_Q9_38 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_38_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_38)) skA_E0_Q9_38 := by decide +kernel

def skA_E0_Q9_39 : SectorVector := [(1, []), (-1, [])]

set_option maxHeartbeats 4000000 in
theorem skA_E0_Q9_39_cert : VectorCertificate (Tpow 9 (aLeft false (15 : ℤ) skM_E0_39)) skA_E0_Q9_39 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E0_9_join : VectorCertificate ([skA_E0_Q9_0, skA_E0_Q9_1, skA_E0_Q9_2, skA_E0_Q9_3, skA_E0_Q9_4, skA_E0_Q9_5, skA_E0_Q9_6, skA_E0_Q9_7, skA_E0_Q9_8, skA_E0_Q9_9, skA_E0_Q9_10, skA_E0_Q9_11, skA_E0_Q9_12, skA_E0_Q9_13, skA_E0_Q9_14, skA_E0_Q9_15, skA_E0_Q9_16, skA_E0_Q9_17, skA_E0_Q9_18, skA_E0_Q9_19, skA_E0_Q9_20, skA_E0_Q9_21, skA_E0_Q9_22, skA_E0_Q9_23, skA_E0_Q9_24, skA_E0_Q9_25, skA_E0_Q9_26, skA_E0_Q9_27, skA_E0_Q9_28, skA_E0_Q9_29, skA_E0_Q9_30, skA_E0_Q9_31, skA_E0_Q9_32, skA_E0_Q9_33, skA_E0_Q9_34, skA_E0_Q9_35, skA_E0_Q9_36, skA_E0_Q9_37, skA_E0_Q9_38, skA_E0_Q9_39] : List SectorVector).flatten skQ_E0_9 := by decide +kernel

theorem skQ_E0_9_val : evaluate skQ_E0_9 = evaluate (OrbSgl.vTerm false skY_E0 0 9) :=
  vTerm_of_chunks false skY_E0 0 9 (15 : ℤ) (by norm_num) skM_E0 [skA_E0_Q9_0, skA_E0_Q9_1, skA_E0_Q9_2, skA_E0_Q9_3, skA_E0_Q9_4, skA_E0_Q9_5, skA_E0_Q9_6, skA_E0_Q9_7, skA_E0_Q9_8, skA_E0_Q9_9, skA_E0_Q9_10, skA_E0_Q9_11, skA_E0_Q9_12, skA_E0_Q9_13, skA_E0_Q9_14, skA_E0_Q9_15, skA_E0_Q9_16, skA_E0_Q9_17, skA_E0_Q9_18, skA_E0_Q9_19, skA_E0_Q9_20, skA_E0_Q9_21, skA_E0_Q9_22, skA_E0_Q9_23, skA_E0_Q9_24, skA_E0_Q9_25, skA_E0_Q9_26, skA_E0_Q9_27, skA_E0_Q9_28, skA_E0_Q9_29, skA_E0_Q9_30, skA_E0_Q9_31, skA_E0_Q9_32, skA_E0_Q9_33, skA_E0_Q9_34, skA_E0_Q9_35, skA_E0_Q9_36, skA_E0_Q9_37, skA_E0_Q9_38, skA_E0_Q9_39] skM_E0_cert
    (List.Forall₂.cons skA_E0_Q9_0_cert (List.Forall₂.cons skA_E0_Q9_1_cert (List.Forall₂.cons skA_E0_Q9_2_cert (List.Forall₂.cons skA_E0_Q9_3_cert (List.Forall₂.cons skA_E0_Q9_4_cert (List.Forall₂.cons skA_E0_Q9_5_cert (List.Forall₂.cons skA_E0_Q9_6_cert (List.Forall₂.cons skA_E0_Q9_7_cert (List.Forall₂.cons skA_E0_Q9_8_cert (List.Forall₂.cons skA_E0_Q9_9_cert (List.Forall₂.cons skA_E0_Q9_10_cert (List.Forall₂.cons skA_E0_Q9_11_cert (List.Forall₂.cons skA_E0_Q9_12_cert (List.Forall₂.cons skA_E0_Q9_13_cert (List.Forall₂.cons skA_E0_Q9_14_cert (List.Forall₂.cons skA_E0_Q9_15_cert (List.Forall₂.cons skA_E0_Q9_16_cert (List.Forall₂.cons skA_E0_Q9_17_cert (List.Forall₂.cons skA_E0_Q9_18_cert (List.Forall₂.cons skA_E0_Q9_19_cert (List.Forall₂.cons skA_E0_Q9_20_cert (List.Forall₂.cons skA_E0_Q9_21_cert (List.Forall₂.cons skA_E0_Q9_22_cert (List.Forall₂.cons skA_E0_Q9_23_cert (List.Forall₂.cons skA_E0_Q9_24_cert (List.Forall₂.cons skA_E0_Q9_25_cert (List.Forall₂.cons skA_E0_Q9_26_cert (List.Forall₂.cons skA_E0_Q9_27_cert (List.Forall₂.cons skA_E0_Q9_28_cert (List.Forall₂.cons skA_E0_Q9_29_cert (List.Forall₂.cons skA_E0_Q9_30_cert (List.Forall₂.cons skA_E0_Q9_31_cert (List.Forall₂.cons skA_E0_Q9_32_cert (List.Forall₂.cons skA_E0_Q9_33_cert (List.Forall₂.cons skA_E0_Q9_34_cert (List.Forall₂.cons skA_E0_Q9_35_cert (List.Forall₂.cons skA_E0_Q9_36_cert (List.Forall₂.cons skA_E0_Q9_37_cert (List.Forall₂.cons skA_E0_Q9_38_cert (List.Forall₂.cons skA_E0_Q9_39_cert List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))
    skQ_E0_9 skQ_E0_9_join

theorem skY_E0_value : evaluate skY_E0 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 0 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E0_cert]
  apply evaluate_uSum false 0 (by norm_num)
  intro i hi
  interval_cases i
  · exact skP_E0_0_val
  · exact skP_E0_1_val
  · exact skP_E0_2_val
  · exact skP_E0_3_val
  · exact skP_E0_4_val
  · exact skP_E0_5_val
  · exact skP_E0_6_val
  · exact skP_E0_7_val
  · exact skP_E0_8_val
  · exact skP_E0_9_val
  · exact skP_E0_10_val
  · exact skP_E0_11_val
  · exact skP_E0_12_val

/-- The certified value of `termE_0`. -/
theorem sk_E0 : evaluate termE_0 = ((Nat.choose 15 0 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 0 (aVec false))
      (6 - (0 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E0_cert]
  apply evaluate_vSum false 0 (by norm_num) skY_E0 skY_E0_value
  intro j hj
  interval_cases j
  · exact skQ_E0_0_val
  · exact skQ_E0_1_val
  · exact skQ_E0_2_val
  · exact skQ_E0_3_val
  · exact skQ_E0_4_val
  · exact skQ_E0_5_val
  · exact skQ_E0_6_val
  · exact skQ_E0_7_val
  · exact skQ_E0_8_val
  · exact skQ_E0_9_val

end VOA.Classification.COne.OrbSgl

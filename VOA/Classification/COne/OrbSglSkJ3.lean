import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,3) (u₍3₎a)₍3₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J3_0 : SectorVector := [(1,
  [(-270, [0, 1, 1, 1, 1, 1]),
   (-540, [0, 1, 1, 3]),
   (-1215, [0, 1, 2, 2]),
   (4860, [0, 5]),
   (4320, [1, 1, 1, 2]),
   (-8100, [1, 4])]),
 (-1,
  [(270, [0, 1, 1, 1, 1, 1]),
   (540, [0, 1, 1, 3]),
   (1215, [0, 1, 2, 2]),
   (-4860, [0, 5]),
   (4320, [1, 1, 1, 2]),
   (-8100, [1, 4])])]

def skP_J3_1 : SectorVector := [(-1,
  [(720, [0, 1, 1, 1, 1, 1]),
   (9360, [0, 1, 1, 3]),
   (-1080, [0, 1, 2, 2]),
   (-21600, [0, 5]),
   (14400, [1, 1, 1, 2]),
   (2160, [1, 4]),
   (-26640, [2, 3])]),
 (1,
  [(-720, [0, 1, 1, 1, 1, 1]),
   (-9360, [0, 1, 1, 3]),
   (1080, [0, 1, 2, 2]),
   (21600, [0, 5]),
   (14400, [1, 1, 1, 2]),
   (2160, [1, 4]),
   (-26640, [2, 3])])]

def skP_J3_2 : SectorVector := [(1,
  [(5760, [0, 1, 1, 1, 1, 1]),
   (-2880, [0, 1, 1, 3]),
   (-24840, [0, 1, 2, 2]),
   (47520, [0, 5]),
   (-37440, [1, 1, 1, 2]),
   (131760, [1, 4]),
   (-26640, [2, 3])]),
 (-1,
  [(-5760, [0, 1, 1, 1, 1, 1]),
   (2880, [0, 1, 1, 3]),
   (24840, [0, 1, 2, 2]),
   (-47520, [0, 5]),
   (-37440, [1, 1, 1, 2]),
   (131760, [1, 4]),
   (-26640, [2, 3])])]

def skP_J3_3 : SectorVector := [(-1,
  [(17280, [0, 1, 1, 1, 1, 1]),
   (-73440, [0, 1, 1, 3]),
   (-25920, [0, 1, 2, 2]),
   (-51840, [0, 5]),
   (-17280, [1, 1, 1, 2]),
   (285120, [1, 4]),
   (112320, [2, 3])]),
 (1,
  [(-17280, [0, 1, 1, 1, 1, 1]),
   (73440, [0, 1, 1, 3]),
   (25920, [0, 1, 2, 2]),
   (51840, [0, 5]),
   (-17280, [1, 1, 1, 2]),
   (285120, [1, 4]),
   (112320, [2, 3])])]

def skP_J3_4 : SectorVector := [(1,
  [(-86400, [0, 1, 1, 1, 1, 1]),
   (-216000, [0, 1, 1, 3]),
   (-162000, [0, 1, 2, 2]),
   (-32400, [0, 5]),
   (-864000, [1, 1, 1, 2]),
   (-324000, [1, 4]),
   (-216000, [2, 3])]),
 (-1,
  [(86400, [0, 1, 1, 1, 1, 1]),
   (216000, [0, 1, 1, 3]),
   (162000, [0, 1, 2, 2]),
   (32400, [0, 5]),
   (-864000, [1, 1, 1, 2]),
   (-324000, [1, 4]),
   (-216000, [2, 3])])]

def skP_J3_5 : SectorVector := [(-1,
  [(-691200, [0, 1, 1, 1, 1, 1]),
   (-1728000, [0, 1, 1, 3]),
   (-1296000, [0, 1, 2, 2]),
   (-259200, [0, 5]),
   (6912000, [1, 1, 1, 2]),
   (2592000, [1, 4]),
   (1728000, [2, 3])]),
 (1,
  [(691200, [0, 1, 1, 1, 1, 1]),
   (1728000, [0, 1, 1, 3]),
   (1296000, [0, 1, 2, 2]),
   (259200, [0, 5]),
   (6912000, [1, 1, 1, 2]),
   (2592000, [1, 4]),
   (1728000, [2, 3])])]

def skP_J3_6 : SectorVector := [(1, []), (-1, [])]

def skP_J3_7 : SectorVector := [(-1, []), (1, [])]

def skP_J3_8 : SectorVector := [(1, []), (-1, [])]

def skP_J3_9 : SectorVector := [(-1, []), (1, [])]

def skY_J3 : SectorVector := [(1,
  [(-3150, [0, 1, 1, 1, 1, 1]),
   (-28260, [0, 1, 1, 3]),
   (-36585, [0, 1, 2, 2]),
   (-5130, [0, 5]),
   (-119520, [1, 1, 1, 2]),
   (-27000, [1, 4]),
   (-28800, [2, 3])]),
 (-1,
  [(3150, [0, 1, 1, 1, 1, 1]),
   (28260, [0, 1, 1, 3]),
   (36585, [0, 1, 2, 2]),
   (5130, [0, 5]),
   (-119520, [1, 1, 1, 2]),
   (-27000, [1, 4]),
   (-28800, [2, 3])])]

def skQ_J3_0 : SectorVector := [(-1,
  [(5192100, [0, 1, 1, 1, 1, 1]),
   (40500000, [0, 1, 1, 3]),
   (36049050, [0, 1, 2, 2]),
   (11824380, [0, 5]),
   (-116899200, [1, 1, 1, 2]),
   (-95197680, [1, 4]),
   (-58423680, [2, 3])]),
 (1,
  [(-5192100, [0, 1, 1, 1, 1, 1]),
   (-40500000, [0, 1, 1, 3]),
   (-36049050, [0, 1, 2, 2]),
   (-11824380, [0, 5]),
   (-116899200, [1, 1, 1, 2]),
   (-95197680, [1, 4]),
   (-58423680, [2, 3])])]

def skQ_J3_1 : SectorVector := [(1,
  [(-47083680, [0, 1, 1, 1, 1, 1]),
   (-253672560, [0, 1, 1, 3]),
   (-187751520, [0, 1, 2, 2]),
   (-51768720, [0, 5]),
   (-734909760, [1, 1, 1, 2]),
   (-454623840, [1, 4]),
   (-321459840, [2, 3])]),
 (-1,
  [(47083680, [0, 1, 1, 1, 1, 1]),
   (253672560, [0, 1, 1, 3]),
   (187751520, [0, 1, 2, 2]),
   (51768720, [0, 5]),
   (-734909760, [1, 1, 1, 2]),
   (-454623840, [1, 4]),
   (-321459840, [2, 3])])]

def skQ_J3_2 : SectorVector := [(-1,
  [(312621120, [0, 1, 1, 1, 1, 1]),
   (1164579120, [0, 1, 1, 3]),
   (830262960, [0, 1, 2, 2]),
   (203575680, [0, 5]),
   (-3777140160, [1, 1, 1, 2]),
   (-2005896960, [1, 4]),
   (-1327311360, [2, 3])]),
 (1,
  [(-312621120, [0, 1, 1, 1, 1, 1]),
   (-1164579120, [0, 1, 1, 3]),
   (-830262960, [0, 1, 2, 2]),
   (-203575680, [0, 5]),
   (-3777140160, [1, 1, 1, 2]),
   (-2005896960, [1, 4]),
   (-1327311360, [2, 3])])]

def skQ_J3_3 : SectorVector := [(1,
  [(-1445091840, [0, 1, 1, 1, 1, 1]),
   (-4066225920, [0, 1, 1, 3]),
   (-2936295360, [0, 1, 2, 2]),
   (-768657600, [0, 5]),
   (-15055580160, [1, 1, 1, 2]),
   (-6779583360, [1, 4]),
   (-4217391360, [2, 3])]),
 (-1,
  [(1445091840, [0, 1, 1, 1, 1, 1]),
   (4066225920, [0, 1, 1, 3]),
   (2936295360, [0, 1, 2, 2]),
   (768657600, [0, 5]),
   (-15055580160, [1, 1, 1, 2]),
   (-6779583360, [1, 4]),
   (-4217391360, [2, 3])])]

def skQ_J3_4 : SectorVector := [(-1,
  [(4051607040, [0, 1, 1, 1, 1, 1]),
   (10129017600, [0, 1, 1, 3]),
   (7596763200, [0, 1, 2, 2]),
   (1519352640, [0, 5]),
   (-40516070400, [1, 1, 1, 2]),
   (-15193526400, [1, 4]),
   (-10129017600, [2, 3])]),
 (1,
  [(-4051607040, [0, 1, 1, 1, 1, 1]),
   (-10129017600, [0, 1, 1, 3]),
   (-7596763200, [0, 1, 2, 2]),
   (-1519352640, [0, 5]),
   (-40516070400, [1, 1, 1, 2]),
   (-15193526400, [1, 4]),
   (-10129017600, [2, 3])])]

def skQ_J3_5 : SectorVector := [(1,
  [(-5013964800, [0, 1, 1, 1, 1, 1]),
   (-12534912000, [0, 1, 1, 3]),
   (-9401184000, [0, 1, 2, 2]),
   (-1880236800, [0, 5]),
   (-50139648000, [1, 1, 1, 2]),
   (-18802368000, [1, 4]),
   (-12534912000, [2, 3])]),
 (-1,
  [(5013964800, [0, 1, 1, 1, 1, 1]),
   (12534912000, [0, 1, 1, 3]),
   (9401184000, [0, 1, 2, 2]),
   (1880236800, [0, 5]),
   (-50139648000, [1, 1, 1, 2]),
   (-18802368000, [1, 4]),
   (-12534912000, [2, 3])])]

def skQ_J3_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J3_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J3_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J3_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J3 : ℕ → SectorVector
  | 0 => skP_J3_0
  | 1 => skP_J3_1
  | 2 => skP_J3_2
  | 3 => skP_J3_3
  | 4 => skP_J3_4
  | 5 => skP_J3_5
  | 6 => skP_J3_6
  | 7 => skP_J3_7
  | 8 => skP_J3_8
  | 9 => skP_J3_9
  | _ => []

def skQf_J3 : ℕ → SectorVector
  | 0 => skQ_J3_0
  | 1 => skQ_J3_1
  | 2 => skQ_J3_2
  | 3 => skQ_J3_3
  | 4 => skQ_J3_4
  | 5 => skQ_J3_5
  | 6 => skQ_J3_6
  | 7 => skQ_J3_7
  | 8 => skQ_J3_8
  | 9 => skQ_J3_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J3_0_cert : VectorCertificate (OrbSgl.uTerm true 3 0) skP_J3_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_1_cert : VectorCertificate (OrbSgl.uTerm true 3 1) skP_J3_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_2_cert : VectorCertificate (OrbSgl.uTerm true 3 2) skP_J3_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_3_cert : VectorCertificate (OrbSgl.uTerm true 3 3) skP_J3_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_4_cert : VectorCertificate (OrbSgl.uTerm true 3 4) skP_J3_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_5_cert : VectorCertificate (OrbSgl.uTerm true 3 5) skP_J3_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_6_cert : VectorCertificate (OrbSgl.uTerm true 3 6) skP_J3_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_7_cert : VectorCertificate (OrbSgl.uTerm true 3 7) skP_J3_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_8_cert : VectorCertificate (OrbSgl.uTerm true 3 8) skP_J3_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J3_9_cert : VectorCertificate (OrbSgl.uTerm true 3 9) skP_J3_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J3_cert : VectorCertificate (OrbSgl.uSum 3 skPf_J3) skY_J3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 0) skQ_J3_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 1) skQ_J3_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 2) skQ_J3_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 3) skQ_J3_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 4) skQ_J3_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 5) skQ_J3_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 6) skQ_J3_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 7) skQ_J3_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 8) skQ_J3_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J3_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J3 3 9) skQ_J3_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J3_cert : VectorCertificate (OrbSgl.vSum 3 skQf_J3) termJ_3 := by decide +kernel

theorem skY_J3_value : evaluate skY_J3 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 3 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J3_cert]
  apply evaluate_uSum true 3 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J3_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J3_9_cert).symm

/-- The certified value of `termJ_3`. -/
theorem sk_J3 : evaluate termJ_3 = ((Nat.choose 15 3 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 3 (aVec true))
      (6 - (3 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J3_cert]
  apply evaluate_vSum true 3 (by norm_num) skY_J3 skY_J3_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J3_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J3_9_cert).symm

end VOA.Classification.COne.OrbSgl

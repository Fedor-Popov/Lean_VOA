import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,4) (u₍4₎a)₍2₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J4_0 : SectorVector := [(1, [(2160, [0, 1, 1, 2]), (5400, [0, 4]), (-720, [1, 1, 1, 1]), (-13680, [1, 3]), (-3240, [2, 2])]),
 (-1, [(-2160, [0, 1, 1, 2]), (-5400, [0, 4]), (-720, [1, 1, 1, 1]), (-13680, [1, 3]), (-3240, [2, 2])])]

def skP_J4_1 : SectorVector := [(-1, [(7560, [0, 1, 1, 2]), (-11880, [0, 4]), (5760, [1, 1, 1, 1]), (12240, [1, 3]), (-9720, [2, 2])]),
 (1, [(-7560, [0, 1, 1, 2]), (11880, [0, 4]), (5760, [1, 1, 1, 1]), (12240, [1, 3]), (-9720, [2, 2])])]

def skP_J4_2 : SectorVector := [(1, [(6480, [0, 1, 1, 2]), (12960, [0, 4]), (-17280, [1, 1, 1, 1]), (60480, [1, 3]), (12960, [2, 2])]),
 (-1, [(-6480, [0, 1, 1, 2]), (-12960, [0, 4]), (-17280, [1, 1, 1, 1]), (60480, [1, 3]), (12960, [2, 2])])]

def skP_J4_3 : SectorVector := [(-1, [(64800, [0, 1, 1, 2]), (8100, [0, 4]), (-86400, [1, 1, 1, 1]), (-86400, [1, 3]), (-32400, [2, 2])]),
 (1, [(-64800, [0, 1, 1, 2]), (-8100, [0, 4]), (-86400, [1, 1, 1, 1]), (-86400, [1, 3]), (-32400, [2, 2])])]

def skP_J4_4 : SectorVector := [(1, [(518400, [0, 1, 1, 2]), (64800, [0, 4]), (691200, [1, 1, 1, 1]), (691200, [1, 3]), (259200, [2, 2])]),
 (-1, [(-518400, [0, 1, 1, 2]), (-64800, [0, 4]), (691200, [1, 1, 1, 1]), (691200, [1, 3]), (259200, [2, 2])])]

def skP_J4_5 : SectorVector := [(-1, []), (1, [])]

def skP_J4_6 : SectorVector := [(1, []), (-1, [])]

def skP_J4_7 : SectorVector := [(-1, []), (1, [])]

def skP_J4_8 : SectorVector := [(1, []), (-1, [])]

def skY_J4 : SectorVector := [(-1, [(45360, [0, 1, 1, 2]), (4050, [0, 4]), (-28080, [1, 1, 1, 1]), (-47520, [1, 3]), (-29160, [2, 2])]),
 (1, [(-45360, [0, 1, 1, 2]), (-4050, [0, 4]), (-28080, [1, 1, 1, 1]), (-47520, [1, 3]), (-29160, [2, 2])])]

def skQ_J4_0 : SectorVector := [(1,
  [(-2553120, [0, 1, 1, 1, 1, 1]),
   (-19815840, [0, 1, 1, 3]),
   (-16465680, [0, 1, 2, 2]),
   (-8300880, [0, 5]),
   (-52669440, [1, 1, 1, 2]),
   (-52682400, [1, 4]),
   (-29496960, [2, 3])]),
 (-1,
  [(2553120, [0, 1, 1, 1, 1, 1]),
   (19815840, [0, 1, 1, 3]),
   (16465680, [0, 1, 2, 2]),
   (8300880, [0, 5]),
   (-52669440, [1, 1, 1, 2]),
   (-52682400, [1, 4]),
   (-29496960, [2, 3])])]

def skQ_J4_1 : SectorVector := [(-1,
  [(23094720, [0, 1, 1, 1, 1, 1]),
   (124416000, [0, 1, 1, 3]),
   (87168960, [0, 1, 2, 2]),
   (35536320, [0, 5]),
   (-345565440, [1, 1, 1, 2]),
   (-254430720, [1, 4]),
   (-156608640, [2, 3])]),
 (1,
  [(-23094720, [0, 1, 1, 1, 1, 1]),
   (-124416000, [0, 1, 1, 3]),
   (-87168960, [0, 1, 2, 2]),
   (-35536320, [0, 5]),
   (-345565440, [1, 1, 1, 2]),
   (-254430720, [1, 4]),
   (-156608640, [2, 3])])]

def skQ_J4_2 : SectorVector := [(1,
  [(-151891200, [0, 1, 1, 1, 1, 1]),
   (-581981760, [0, 1, 1, 3]),
   (-402719040, [0, 1, 2, 2]),
   (-124493760, [0, 5]),
   (-1833373440, [1, 1, 1, 2]),
   (-1075576320, [1, 4]),
   (-660597120, [2, 3])]),
 (-1,
  [(151891200, [0, 1, 1, 1, 1, 1]),
   (581981760, [0, 1, 1, 3]),
   (402719040, [0, 1, 2, 2]),
   (124493760, [0, 5]),
   (-1833373440, [1, 1, 1, 2]),
   (-1075576320, [1, 4]),
   (-660597120, [2, 3])])]

def skQ_J4_3 : SectorVector := [(-1,
  [(710415360, [0, 1, 1, 1, 1, 1]),
   (2046176640, [0, 1, 1, 3]),
   (1467097920, [0, 1, 2, 2]),
   (401474880, [0, 5]),
   (-7464337920, [1, 1, 1, 2]),
   (-3474472320, [1, 4]),
   (-2136222720, [2, 3])]),
 (1,
  [(-710415360, [0, 1, 1, 1, 1, 1]),
   (-2046176640, [0, 1, 1, 3]),
   (-1467097920, [0, 1, 2, 2]),
   (-401474880, [0, 5]),
   (-7464337920, [1, 1, 1, 2]),
   (-3474472320, [1, 4]),
   (-2136222720, [2, 3])])]

def skQ_J4_4 : SectorVector := [(1,
  [(-2093921280, [0, 1, 1, 1, 1, 1]),
   (-5234803200, [0, 1, 1, 3]),
   (-3926102400, [0, 1, 2, 2]),
   (-785220480, [0, 5]),
   (-20939212800, [1, 1, 1, 2]),
   (-7852204800, [1, 4]),
   (-5234803200, [2, 3])]),
 (-1,
  [(2093921280, [0, 1, 1, 1, 1, 1]),
   (5234803200, [0, 1, 1, 3]),
   (3926102400, [0, 1, 2, 2]),
   (785220480, [0, 5]),
   (-20939212800, [1, 1, 1, 2]),
   (-7852204800, [1, 4]),
   (-5234803200, [2, 3])])]

def skQ_J4_5 : SectorVector := [(-1,
  [(2878986240, [0, 1, 1, 1, 1, 1]),
   (7197465600, [0, 1, 1, 3]),
   (5398099200, [0, 1, 2, 2]),
   (1079619840, [0, 5]),
   (-28789862400, [1, 1, 1, 2]),
   (-10796198400, [1, 4]),
   (-7197465600, [2, 3])]),
 (1,
  [(-2878986240, [0, 1, 1, 1, 1, 1]),
   (-7197465600, [0, 1, 1, 3]),
   (-5398099200, [0, 1, 2, 2]),
   (-1079619840, [0, 5]),
   (-28789862400, [1, 1, 1, 2]),
   (-10796198400, [1, 4]),
   (-7197465600, [2, 3])])]

def skQ_J4_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J4_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J4_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J4_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J4 : ℕ → SectorVector
  | 0 => skP_J4_0
  | 1 => skP_J4_1
  | 2 => skP_J4_2
  | 3 => skP_J4_3
  | 4 => skP_J4_4
  | 5 => skP_J4_5
  | 6 => skP_J4_6
  | 7 => skP_J4_7
  | 8 => skP_J4_8
  | _ => []

def skQf_J4 : ℕ → SectorVector
  | 0 => skQ_J4_0
  | 1 => skQ_J4_1
  | 2 => skQ_J4_2
  | 3 => skQ_J4_3
  | 4 => skQ_J4_4
  | 5 => skQ_J4_5
  | 6 => skQ_J4_6
  | 7 => skQ_J4_7
  | 8 => skQ_J4_8
  | 9 => skQ_J4_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J4_0_cert : VectorCertificate (OrbSgl.uTerm true 4 0) skP_J4_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_1_cert : VectorCertificate (OrbSgl.uTerm true 4 1) skP_J4_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_2_cert : VectorCertificate (OrbSgl.uTerm true 4 2) skP_J4_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_3_cert : VectorCertificate (OrbSgl.uTerm true 4 3) skP_J4_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_4_cert : VectorCertificate (OrbSgl.uTerm true 4 4) skP_J4_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_5_cert : VectorCertificate (OrbSgl.uTerm true 4 5) skP_J4_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_6_cert : VectorCertificate (OrbSgl.uTerm true 4 6) skP_J4_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_7_cert : VectorCertificate (OrbSgl.uTerm true 4 7) skP_J4_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J4_8_cert : VectorCertificate (OrbSgl.uTerm true 4 8) skP_J4_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J4_cert : VectorCertificate (OrbSgl.uSum 4 skPf_J4) skY_J4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 0) skQ_J4_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 1) skQ_J4_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 2) skQ_J4_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 3) skQ_J4_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 4) skQ_J4_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 5) skQ_J4_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 6) skQ_J4_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 7) skQ_J4_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 8) skQ_J4_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J4_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J4 4 9) skQ_J4_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J4_cert : VectorCertificate (OrbSgl.vSum 4 skQf_J4) termJ_4 := by decide +kernel

theorem skY_J4_value : evaluate skY_J4 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 4 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J4_cert]
  apply evaluate_uSum true 4 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J4_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J4_8_cert).symm

/-- The certified value of `termJ_4`. -/
theorem sk_J4 : evaluate termJ_4 = ((Nat.choose 15 4 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 4 (aVec true))
      (6 - (4 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J4_cert]
  apply evaluate_vSum true 4 (by norm_num) skY_J4 skY_J4_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J4_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J4_9_cert).symm

end VOA.Classification.COne.OrbSgl

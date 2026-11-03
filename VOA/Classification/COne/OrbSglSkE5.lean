import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,5) (u₍5₎a)₍1₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E5_0 : SectorVector := [(0,
  [(-24, [1, 1, 1, 1, 1, 2]),
   (-640, [1, 1, 1, 4]),
   (1200, [1, 1, 2, 3]),
   (-580, [1, 2, 2, 2]),
   (80, [1, 6]),
   (-144, [2, 5]),
   (80, [3, 4])]),
 (-2, []),
 (2, [])]

def skP_E5_1 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(-288, [1, 1, 1, 1, 1, 2]),
   (-480, [1, 1, 1, 4]),
   (240, [1, 2, 2, 2]),
   (960, [1, 6]),
   (-1728, [2, 5]),
   (960, [3, 4])])]

def skP_E5_2 : SectorVector := [(0, [(1200, [1, 1, 1, 4]), (3600, [1, 1, 2, 3]), (1200, [1, 2, 2, 2]), (-6000, [1, 6]), (3000, [3, 4])]),
 (-2, []),
 (2, [])]

def skP_E5_3 : SectorVector := [(2, []),
 (-2, []),
 (0, [(-9600, [1, 1, 1, 4]), (-28800, [1, 1, 2, 3]), (-9600, [1, 2, 2, 2]), (48000, [1, 6]), (-24000, [3, 4])])]

def skP_E5_4 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E5_5 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E5_6 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E5_7 : SectorVector := [(2, []), (-2, []), (0, [])]

def skY_E5 : SectorVector := [(0,
  [(264, [1, 1, 1, 1, 1, 2]),
   (2040, [1, 1, 1, 4]),
   (7800, [1, 1, 2, 3]),
   (1380, [1, 2, 2, 2]),
   (-11880, [1, 6]),
   (1584, [2, 5]),
   (4620, [3, 4])]),
 (-2, []),
 (2, [])]

def skQ_E5_0 : SectorVector := [(1,
  [(35864, [0, 1, 1, 1, 1, 1]),
   (333080, [0, 1, 1, 3]),
   (244620, [0, 1, 2, 2]),
   (159984, [0, 5]),
   (762080, [1, 1, 1, 2]),
   (982320, [1, 4]),
   (567440, [2, 3])]),
 (-3, []),
 (-1,
  [(-35864, [0, 1, 1, 1, 1, 1]),
   (-333080, [0, 1, 1, 3]),
   (-244620, [0, 1, 2, 2]),
   (-159984, [0, 5]),
   (762080, [1, 1, 1, 2]),
   (982320, [1, 4]),
   (567440, [2, 3])]),
 (3, [])]

def skQ_E5_1 : SectorVector := [(3, []),
 (-1,
  [(-355200, [0, 1, 1, 1, 1, 1]),
   (-2023920, [0, 1, 1, 3]),
   (-1352400, [0, 1, 2, 2]),
   (-724080, [0, 5]),
   (5290560, [1, 1, 1, 2]),
   (4617600, [1, 4]),
   (2596320, [2, 3])]),
 (-3, []),
 (1,
  [(355200, [0, 1, 1, 1, 1, 1]),
   (2023920, [0, 1, 1, 3]),
   (1352400, [0, 1, 2, 2]),
   (724080, [0, 5]),
   (5290560, [1, 1, 1, 2]),
   (4617600, [1, 4]),
   (2596320, [2, 3])])]

def skQ_E5_2 : SectorVector := [(1,
  [(2437440, [0, 1, 1, 1, 1, 1]),
   (9574800, [0, 1, 1, 3]),
   (6424560, [0, 1, 2, 2]),
   (2427120, [0, 5]),
   (29319360, [1, 1, 1, 2]),
   (18901440, [1, 4]),
   (10811040, [2, 3])]),
 (-3, []),
 (-1,
  [(-2437440, [0, 1, 1, 1, 1, 1]),
   (-9574800, [0, 1, 1, 3]),
   (-6424560, [0, 1, 2, 2]),
   (-2427120, [0, 5]),
   (29319360, [1, 1, 1, 2]),
   (18901440, [1, 4]),
   (10811040, [2, 3])]),
 (3, [])]

def skQ_E5_3 : SectorVector := [(3, []),
 (-1,
  [(-11619840, [0, 1, 1, 1, 1, 1]),
   (-34250880, [0, 1, 1, 3]),
   (-24387840, [0, 1, 2, 2]),
   (-6958080, [0, 5]),
   (123133440, [1, 1, 1, 2]),
   (59178240, [1, 4]),
   (35984640, [2, 3])]),
 (-3, []),
 (1,
  [(11619840, [0, 1, 1, 1, 1, 1]),
   (34250880, [0, 1, 1, 3]),
   (24387840, [0, 1, 2, 2]),
   (6958080, [0, 5]),
   (123133440, [1, 1, 1, 2]),
   (59178240, [1, 4]),
   (35984640, [2, 3])])]

def skQ_E5_4 : SectorVector := [(1,
  [(35228160, [0, 1, 1, 1, 1, 1]),
   (88070400, [0, 1, 1, 3]),
   (66052800, [0, 1, 2, 2]),
   (13210560, [0, 5]),
   (352281600, [1, 1, 1, 2]),
   (132105600, [1, 4]),
   (88070400, [2, 3])]),
 (-3, []),
 (-1,
  [(-35228160, [0, 1, 1, 1, 1, 1]),
   (-88070400, [0, 1, 1, 3]),
   (-66052800, [0, 1, 2, 2]),
   (-13210560, [0, 5]),
   (352281600, [1, 1, 1, 2]),
   (132105600, [1, 4]),
   (88070400, [2, 3])]),
 (3, [])]

def skQ_E5_5 : SectorVector := [(3, []),
 (-1,
  [(-51701760, [0, 1, 1, 1, 1, 1]),
   (-129254400, [0, 1, 1, 3]),
   (-96940800, [0, 1, 2, 2]),
   (-19388160, [0, 5]),
   (517017600, [1, 1, 1, 2]),
   (193881600, [1, 4]),
   (129254400, [2, 3])]),
 (-3, []),
 (1,
  [(51701760, [0, 1, 1, 1, 1, 1]),
   (129254400, [0, 1, 1, 3]),
   (96940800, [0, 1, 2, 2]),
   (19388160, [0, 5]),
   (517017600, [1, 1, 1, 2]),
   (193881600, [1, 4]),
   (129254400, [2, 3])])]

def skQ_E5_6 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E5_7 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E5_8 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E5_9 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skPf_E5 : ℕ → SectorVector
  | 0 => skP_E5_0
  | 1 => skP_E5_1
  | 2 => skP_E5_2
  | 3 => skP_E5_3
  | 4 => skP_E5_4
  | 5 => skP_E5_5
  | 6 => skP_E5_6
  | 7 => skP_E5_7
  | _ => []

def skQf_E5 : ℕ → SectorVector
  | 0 => skQ_E5_0
  | 1 => skQ_E5_1
  | 2 => skQ_E5_2
  | 3 => skQ_E5_3
  | 4 => skQ_E5_4
  | 5 => skQ_E5_5
  | 6 => skQ_E5_6
  | 7 => skQ_E5_7
  | 8 => skQ_E5_8
  | 9 => skQ_E5_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E5_0_cert : VectorCertificate (OrbSgl.uTerm false 5 0) skP_E5_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_1_cert : VectorCertificate (OrbSgl.uTerm false 5 1) skP_E5_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_2_cert : VectorCertificate (OrbSgl.uTerm false 5 2) skP_E5_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_3_cert : VectorCertificate (OrbSgl.uTerm false 5 3) skP_E5_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_4_cert : VectorCertificate (OrbSgl.uTerm false 5 4) skP_E5_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_5_cert : VectorCertificate (OrbSgl.uTerm false 5 5) skP_E5_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_6_cert : VectorCertificate (OrbSgl.uTerm false 5 6) skP_E5_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E5_7_cert : VectorCertificate (OrbSgl.uTerm false 5 7) skP_E5_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E5_cert : VectorCertificate (OrbSgl.uSum 5 skPf_E5) skY_E5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 0) skQ_E5_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 1) skQ_E5_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 2) skQ_E5_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 3) skQ_E5_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 4) skQ_E5_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 5) skQ_E5_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 6) skQ_E5_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 7) skQ_E5_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 8) skQ_E5_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E5_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E5 5 9) skQ_E5_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E5_cert : VectorCertificate (OrbSgl.vSum 5 skQf_E5) termE_5 := by decide +kernel

theorem skY_E5_value : evaluate skY_E5 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 5 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E5_cert]
  apply evaluate_uSum false 5 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E5_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E5_7_cert).symm

/-- The certified value of `termE_5`. -/
theorem sk_E5 : evaluate termE_5 = ((Nat.choose 15 5 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 5 (aVec false))
      (6 - (5 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E5_cert]
  apply evaluate_vSum false 5 (by norm_num) skY_E5 skY_E5_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E5_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E5_9_cert).symm

end VOA.Classification.COne.OrbSgl

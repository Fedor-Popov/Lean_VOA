import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,7) (u₍7₎a)₍-1₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E7_0 : SectorVector := [(0, [(200, [1, 1, 1, 2]), (-300, [1, 4]), (200, [2, 3])]), (-2, []), (2, [])]

def skP_E7_1 : SectorVector := [(2, []), (-2, []), (0, [(-1600, [1, 1, 1, 2]), (2400, [1, 4]), (-1600, [2, 3])])]

def skP_E7_2 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E7_3 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E7_4 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E7_5 : SectorVector := [(2, []), (-2, []), (0, [])]

def skY_E7 : SectorVector := [(0, [(1800, [1, 1, 1, 2]), (-2700, [1, 4]), (1800, [2, 3])]), (-2, []), (2, [])]

def skQ_E7_0 : SectorVector := [(1,
  [(43200, [0, 1, 1, 3]),
   (24300, [0, 1, 2, 2]),
   (21600, [0, 5]),
   (52200, [1, 1, 1, 2]),
   (153900, [1, 4]),
   (95400, [2, 3])]),
 (-3, []),
 (-1,
  [(-43200, [0, 1, 1, 3]),
   (-24300, [0, 1, 2, 2]),
   (-21600, [0, 5]),
   (52200, [1, 1, 1, 2]),
   (153900, [1, 4]),
   (95400, [2, 3])]),
 (3, [])]

def skQ_E7_1 : SectorVector := [(3, []),
 (-1,
  [(-14400, [0, 1, 1, 1, 1, 1]),
   (-262800, [0, 1, 1, 3]),
   (-140400, [0, 1, 2, 2]),
   (-118800, [0, 5]),
   (446400, [1, 1, 1, 2]),
   (734400, [1, 4]),
   (338400, [2, 3])]),
 (-3, []),
 (1,
  [(14400, [0, 1, 1, 1, 1, 1]),
   (262800, [0, 1, 1, 3]),
   (140400, [0, 1, 2, 2]),
   (118800, [0, 5]),
   (446400, [1, 1, 1, 2]),
   (734400, [1, 4]),
   (338400, [2, 3])])]

def skQ_E7_2 : SectorVector := [(1,
  [(187200, [0, 1, 1, 1, 1, 1]),
   (1148400, [0, 1, 1, 3]),
   (691200, [0, 1, 2, 2]),
   (410400, [0, 5]),
   (2779200, [1, 1, 1, 2]),
   (2743200, [1, 4]),
   (1375200, [2, 3])]),
 (-3, []),
 (-1,
  [(-187200, [0, 1, 1, 1, 1, 1]),
   (-1148400, [0, 1, 1, 3]),
   (-691200, [0, 1, 2, 2]),
   (-410400, [0, 5]),
   (2779200, [1, 1, 1, 2]),
   (2743200, [1, 4]),
   (1375200, [2, 3])]),
 (3, [])]

def skQ_E7_3 : SectorVector := [(3, []),
 (-1,
  [(-1209600, [0, 1, 1, 1, 1, 1]),
   (-3931200, [0, 1, 1, 3]),
   (-2721600, [0, 1, 2, 2]),
   (-907200, [0, 5]),
   (13305600, [1, 1, 1, 2]),
   (7257600, [1, 4]),
   (4233600, [2, 3])]),
 (-3, []),
 (1,
  [(1209600, [0, 1, 1, 1, 1, 1]),
   (3931200, [0, 1, 1, 3]),
   (2721600, [0, 1, 2, 2]),
   (907200, [0, 5]),
   (13305600, [1, 1, 1, 2]),
   (7257600, [1, 4]),
   (4233600, [2, 3])])]

def skQ_E7_4 : SectorVector := [(1,
  [(4320000, [0, 1, 1, 1, 1, 1]),
   (10800000, [0, 1, 1, 3]),
   (8100000, [0, 1, 2, 2]),
   (1620000, [0, 5]),
   (43200000, [1, 1, 1, 2]),
   (16200000, [1, 4]),
   (10800000, [2, 3])]),
 (-3, []),
 (-1,
  [(-4320000, [0, 1, 1, 1, 1, 1]),
   (-10800000, [0, 1, 1, 3]),
   (-8100000, [0, 1, 2, 2]),
   (-1620000, [0, 5]),
   (43200000, [1, 1, 1, 2]),
   (16200000, [1, 4]),
   (10800000, [2, 3])]),
 (3, [])]

def skQ_E7_5 : SectorVector := [(3, []),
 (-1,
  [(-6912000, [0, 1, 1, 1, 1, 1]),
   (-17280000, [0, 1, 1, 3]),
   (-12960000, [0, 1, 2, 2]),
   (-2592000, [0, 5]),
   (69120000, [1, 1, 1, 2]),
   (25920000, [1, 4]),
   (17280000, [2, 3])]),
 (-3, []),
 (1,
  [(6912000, [0, 1, 1, 1, 1, 1]),
   (17280000, [0, 1, 1, 3]),
   (12960000, [0, 1, 2, 2]),
   (2592000, [0, 5]),
   (69120000, [1, 1, 1, 2]),
   (25920000, [1, 4]),
   (17280000, [2, 3])])]

def skQ_E7_6 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E7_7 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E7_8 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E7_9 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skPf_E7 : ℕ → SectorVector
  | 0 => skP_E7_0
  | 1 => skP_E7_1
  | 2 => skP_E7_2
  | 3 => skP_E7_3
  | 4 => skP_E7_4
  | 5 => skP_E7_5
  | _ => []

def skQf_E7 : ℕ → SectorVector
  | 0 => skQ_E7_0
  | 1 => skQ_E7_1
  | 2 => skQ_E7_2
  | 3 => skQ_E7_3
  | 4 => skQ_E7_4
  | 5 => skQ_E7_5
  | 6 => skQ_E7_6
  | 7 => skQ_E7_7
  | 8 => skQ_E7_8
  | 9 => skQ_E7_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E7_0_cert : VectorCertificate (OrbSgl.uTerm false 7 0) skP_E7_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E7_1_cert : VectorCertificate (OrbSgl.uTerm false 7 1) skP_E7_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E7_2_cert : VectorCertificate (OrbSgl.uTerm false 7 2) skP_E7_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E7_3_cert : VectorCertificate (OrbSgl.uTerm false 7 3) skP_E7_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E7_4_cert : VectorCertificate (OrbSgl.uTerm false 7 4) skP_E7_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E7_5_cert : VectorCertificate (OrbSgl.uTerm false 7 5) skP_E7_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E7_cert : VectorCertificate (OrbSgl.uSum 7 skPf_E7) skY_E7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 0) skQ_E7_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 1) skQ_E7_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 2) skQ_E7_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 3) skQ_E7_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 4) skQ_E7_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 5) skQ_E7_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 6) skQ_E7_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 7) skQ_E7_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 8) skQ_E7_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E7_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E7 7 9) skQ_E7_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E7_cert : VectorCertificate (OrbSgl.vSum 7 skQf_E7) termE_7 := by decide +kernel

theorem skY_E7_value : evaluate skY_E7 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 7 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E7_cert]
  apply evaluate_uSum false 7 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E7_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E7_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E7_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E7_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E7_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E7_5_cert).symm

/-- The certified value of `termE_7`. -/
theorem sk_E7 : evaluate termE_7 = ((Nat.choose 15 7 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 7 (aVec false))
      (6 - (7 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E7_cert]
  apply evaluate_vSum false 7 (by norm_num) skY_E7 skY_E7_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E7_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E7_9_cert).symm

end VOA.Classification.COne.OrbSgl

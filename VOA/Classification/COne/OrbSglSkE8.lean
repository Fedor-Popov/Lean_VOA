import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,8) (u₍8₎a)₍-2₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E8_0 : SectorVector := [(0, [(-400, [1, 1, 1, 1]), (800, [1, 3]), (-600, [2, 2])]), (-2, []), (2, [])]

def skP_E8_1 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E8_2 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E8_3 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E8_4 : SectorVector := [(0, []), (-2, []), (2, [])]

def skY_E8 : SectorVector := [(2, []), (-2, []), (0, [(400, [1, 1, 1, 1]), (-800, [1, 3]), (600, [2, 2])])]

def skQ_E8_0 : SectorVector := [(-1,
  [(-400, [0, 1, 1, 1, 1, 1]),
   (-8800, [0, 1, 1, 3]),
   (-7800, [0, 1, 2, 2]),
   (-4800, [0, 5]),
   (-6400, [1, 1, 1, 2]),
   (24000, [1, 4]),
   (32000, [2, 3])]),
 (-3, []),
 (1,
  [(400, [0, 1, 1, 1, 1, 1]),
   (8800, [0, 1, 1, 3]),
   (7800, [0, 1, 2, 2]),
   (4800, [0, 5]),
   (-6400, [1, 1, 1, 2]),
   (24000, [1, 4]),
   (32000, [2, 3])]),
 (3, [])]

def skQ_E8_1 : SectorVector := [(3, []),
 (1,
  [(400, [0, 1, 1, 1, 1, 1]),
   (47200, [0, 1, 1, 3]),
   (29400, [0, 1, 2, 2]),
   (24000, [0, 5]),
   (40000, [1, 1, 1, 2]),
   (160800, [1, 4]),
   (116800, [2, 3])]),
 (-3, []),
 (-1,
  [(-400, [0, 1, 1, 1, 1, 1]),
   (-47200, [0, 1, 1, 3]),
   (-29400, [0, 1, 2, 2]),
   (-24000, [0, 5]),
   (40000, [1, 1, 1, 2]),
   (160800, [1, 4]),
   (116800, [2, 3])])]

def skQ_E8_2 : SectorVector := [(-1,
  [(-12800, [0, 1, 1, 1, 1, 1]),
   (-233600, [0, 1, 1, 3]),
   (-124800, [0, 1, 2, 2]),
   (-105600, [0, 5]),
   (396800, [1, 1, 1, 2]),
   (652800, [1, 4]),
   (300800, [2, 3])]),
 (-3, []),
 (1,
  [(12800, [0, 1, 1, 1, 1, 1]),
   (233600, [0, 1, 1, 3]),
   (124800, [0, 1, 2, 2]),
   (105600, [0, 5]),
   (396800, [1, 1, 1, 2]),
   (652800, [1, 4]),
   (300800, [2, 3])]),
 (3, [])]

def skQ_E8_3 : SectorVector := [(3, []),
 (1,
  [(153600, [0, 1, 1, 1, 1, 1]),
   (787200, [0, 1, 1, 3]),
   (489600, [0, 1, 2, 2]),
   (259200, [0, 5]),
   (2073600, [1, 1, 1, 2]),
   (1785600, [1, 4]),
   (921600, [2, 3])]),
 (-3, []),
 (-1,
  [(-153600, [0, 1, 1, 1, 1, 1]),
   (-787200, [0, 1, 1, 3]),
   (-489600, [0, 1, 2, 2]),
   (-259200, [0, 5]),
   (2073600, [1, 1, 1, 2]),
   (1785600, [1, 4]),
   (921600, [2, 3])])]

def skQ_E8_4 : SectorVector := [(-1,
  [(-768000, [0, 1, 1, 1, 1, 1]),
   (-1920000, [0, 1, 1, 3]),
   (-1440000, [0, 1, 2, 2]),
   (-288000, [0, 5]),
   (7680000, [1, 1, 1, 2]),
   (2880000, [1, 4]),
   (1920000, [2, 3])]),
 (-3, []),
 (1,
  [(768000, [0, 1, 1, 1, 1, 1]),
   (1920000, [0, 1, 1, 3]),
   (1440000, [0, 1, 2, 2]),
   (288000, [0, 5]),
   (7680000, [1, 1, 1, 2]),
   (2880000, [1, 4]),
   (1920000, [2, 3])]),
 (3, [])]

def skQ_E8_5 : SectorVector := [(3, []),
 (1,
  [(1536000, [0, 1, 1, 1, 1, 1]),
   (3840000, [0, 1, 1, 3]),
   (2880000, [0, 1, 2, 2]),
   (576000, [0, 5]),
   (15360000, [1, 1, 1, 2]),
   (5760000, [1, 4]),
   (3840000, [2, 3])]),
 (-3, []),
 (-1,
  [(-1536000, [0, 1, 1, 1, 1, 1]),
   (-3840000, [0, 1, 1, 3]),
   (-2880000, [0, 1, 2, 2]),
   (-576000, [0, 5]),
   (15360000, [1, 1, 1, 2]),
   (5760000, [1, 4]),
   (3840000, [2, 3])])]

def skQ_E8_6 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E8_7 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E8_8 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E8_9 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skPf_E8 : ℕ → SectorVector
  | 0 => skP_E8_0
  | 1 => skP_E8_1
  | 2 => skP_E8_2
  | 3 => skP_E8_3
  | 4 => skP_E8_4
  | _ => []

def skQf_E8 : ℕ → SectorVector
  | 0 => skQ_E8_0
  | 1 => skQ_E8_1
  | 2 => skQ_E8_2
  | 3 => skQ_E8_3
  | 4 => skQ_E8_4
  | 5 => skQ_E8_5
  | 6 => skQ_E8_6
  | 7 => skQ_E8_7
  | 8 => skQ_E8_8
  | 9 => skQ_E8_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E8_0_cert : VectorCertificate (OrbSgl.uTerm false 8 0) skP_E8_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E8_1_cert : VectorCertificate (OrbSgl.uTerm false 8 1) skP_E8_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E8_2_cert : VectorCertificate (OrbSgl.uTerm false 8 2) skP_E8_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E8_3_cert : VectorCertificate (OrbSgl.uTerm false 8 3) skP_E8_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E8_4_cert : VectorCertificate (OrbSgl.uTerm false 8 4) skP_E8_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E8_cert : VectorCertificate (OrbSgl.uSum 8 skPf_E8) skY_E8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 0) skQ_E8_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 1) skQ_E8_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 2) skQ_E8_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 3) skQ_E8_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 4) skQ_E8_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 5) skQ_E8_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 6) skQ_E8_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 7) skQ_E8_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 8) skQ_E8_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E8_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E8 8 9) skQ_E8_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E8_cert : VectorCertificate (OrbSgl.vSum 8 skQf_E8) termE_8 := by decide +kernel

theorem skY_E8_value : evaluate skY_E8 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 8 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E8_cert]
  apply evaluate_uSum false 8 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E8_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E8_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E8_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E8_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E8_4_cert).symm

/-- The certified value of `termE_8`. -/
theorem sk_E8 : evaluate termE_8 = ((Nat.choose 15 8 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 8 (aVec false))
      (6 - (8 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E8_cert]
  apply evaluate_vSum false 8 (by norm_num) skY_E8 skY_E8_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E8_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E8_9_cert).symm

end VOA.Classification.COne.OrbSgl

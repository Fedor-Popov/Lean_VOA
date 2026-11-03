import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,6) (u₍6₎a)₍0₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E6_0 : SectorVector := [(0,
  [(-48, [1, 1, 1, 1, 1, 1]), (-160, [1, 1, 1, 3]), (120, [1, 1, 2, 2]), (192, [1, 5]), (-480, [2, 4]), (320, [3, 3])]),
 (-2, []),
 (2, [])]

def skP_E6_1 : SectorVector := [(2, []), (-2, []), (0, [(400, [1, 1, 1, 3]), (600, [1, 1, 2, 2]), (-1200, [1, 5]), (300, [2, 4]), (400, [3, 3])])]

def skP_E6_2 : SectorVector := [(0, [(-3200, [1, 1, 1, 3]), (-4800, [1, 1, 2, 2]), (9600, [1, 5]), (-2400, [2, 4]), (-3200, [3, 3])]),
 (-2, []),
 (2, [])]

def skP_E6_3 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E6_4 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E6_5 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E6_6 : SectorVector := [(0, []), (-2, []), (2, [])]

def skY_E6 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(48, [1, 1, 1, 1, 1, 1]),
   (2160, [1, 1, 1, 3]),
   (2880, [1, 1, 2, 2]),
   (-6192, [1, 5]),
   (1980, [2, 4]),
   (1680, [3, 3])])]

def skQ_E6_0 : SectorVector := [(-1,
  [(-7968, [0, 1, 1, 1, 1, 1]),
   (-145200, [0, 1, 1, 3]),
   (-87840, [0, 1, 2, 2]),
   (-71568, [0, 5]),
   (235200, [1, 1, 1, 2]),
   (417600, [1, 4]),
   (225120, [2, 3])]),
 (-3, []),
 (1,
  [(7968, [0, 1, 1, 1, 1, 1]),
   (145200, [0, 1, 1, 3]),
   (87840, [0, 1, 2, 2]),
   (71568, [0, 5]),
   (235200, [1, 1, 1, 2]),
   (417600, [1, 4]),
   (225120, [2, 3])]),
 (3, [])]

def skQ_E6_1 : SectorVector := [(3, []),
 (1,
  [(107520, [0, 1, 1, 1, 1, 1]),
   (800160, [0, 1, 1, 3]),
   (493200, [0, 1, 2, 2]),
   (318960, [0, 5]),
   (1772160, [1, 1, 1, 2]),
   (2031840, [1, 4]),
   (1095360, [2, 3])]),
 (-3, []),
 (-1,
  [(-107520, [0, 1, 1, 1, 1, 1]),
   (-800160, [0, 1, 1, 3]),
   (-493200, [0, 1, 2, 2]),
   (-318960, [0, 5]),
   (1772160, [1, 1, 1, 2]),
   (2031840, [1, 4]),
   (1095360, [2, 3])])]

def skQ_E6_2 : SectorVector := [(-1,
  [(-850560, [0, 1, 1, 1, 1, 1]),
   (-3642720, [0, 1, 1, 3]),
   (-2361600, [0, 1, 2, 2]),
   (-1059840, [0, 5]),
   (10550400, [1, 1, 1, 2]),
   (7686720, [1, 4]),
   (4153920, [2, 3])]),
 (-3, []),
 (1,
  [(850560, [0, 1, 1, 1, 1, 1]),
   (3642720, [0, 1, 1, 3]),
   (2361600, [0, 1, 2, 2]),
   (1059840, [0, 5]),
   (10550400, [1, 1, 1, 2]),
   (7686720, [1, 4]),
   (4153920, [2, 3])]),
 (3, [])]

def skQ_E6_3 : SectorVector := [(3, []),
 (1,
  [(4377600, [0, 1, 1, 1, 1, 1]),
   (13199040, [0, 1, 1, 3]),
   (9335520, [0, 1, 2, 2]),
   (2769120, [0, 5]),
   (46782720, [1, 1, 1, 2]),
   (23181120, [1, 4]),
   (13950720, [2, 3])]),
 (-3, []),
 (-1,
  [(-4377600, [0, 1, 1, 1, 1, 1]),
   (-13199040, [0, 1, 1, 3]),
   (-9335520, [0, 1, 2, 2]),
   (-2769120, [0, 5]),
   (46782720, [1, 1, 1, 2]),
   (23181120, [1, 4]),
   (13950720, [2, 3])])]

def skQ_E6_4 : SectorVector := [(-1,
  [(-13870080, [0, 1, 1, 1, 1, 1]),
   (-34675200, [0, 1, 1, 3]),
   (-26006400, [0, 1, 2, 2]),
   (-5201280, [0, 5]),
   (138700800, [1, 1, 1, 2]),
   (52012800, [1, 4]),
   (34675200, [2, 3])]),
 (-3, []),
 (1,
  [(13870080, [0, 1, 1, 1, 1, 1]),
   (34675200, [0, 1, 1, 3]),
   (26006400, [0, 1, 2, 2]),
   (5201280, [0, 5]),
   (138700800, [1, 1, 1, 2]),
   (52012800, [1, 4]),
   (34675200, [2, 3])]),
 (3, [])]

def skQ_E6_5 : SectorVector := [(3, []),
 (1,
  [(20920320, [0, 1, 1, 1, 1, 1]),
   (52300800, [0, 1, 1, 3]),
   (39225600, [0, 1, 2, 2]),
   (7845120, [0, 5]),
   (209203200, [1, 1, 1, 2]),
   (78451200, [1, 4]),
   (52300800, [2, 3])]),
 (-3, []),
 (-1,
  [(-20920320, [0, 1, 1, 1, 1, 1]),
   (-52300800, [0, 1, 1, 3]),
   (-39225600, [0, 1, 2, 2]),
   (-7845120, [0, 5]),
   (209203200, [1, 1, 1, 2]),
   (78451200, [1, 4]),
   (52300800, [2, 3])])]

def skQ_E6_6 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E6_7 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E6_8 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E6_9 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skPf_E6 : ℕ → SectorVector
  | 0 => skP_E6_0
  | 1 => skP_E6_1
  | 2 => skP_E6_2
  | 3 => skP_E6_3
  | 4 => skP_E6_4
  | 5 => skP_E6_5
  | 6 => skP_E6_6
  | _ => []

def skQf_E6 : ℕ → SectorVector
  | 0 => skQ_E6_0
  | 1 => skQ_E6_1
  | 2 => skQ_E6_2
  | 3 => skQ_E6_3
  | 4 => skQ_E6_4
  | 5 => skQ_E6_5
  | 6 => skQ_E6_6
  | 7 => skQ_E6_7
  | 8 => skQ_E6_8
  | 9 => skQ_E6_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E6_0_cert : VectorCertificate (OrbSgl.uTerm false 6 0) skP_E6_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_1_cert : VectorCertificate (OrbSgl.uTerm false 6 1) skP_E6_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_2_cert : VectorCertificate (OrbSgl.uTerm false 6 2) skP_E6_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_3_cert : VectorCertificate (OrbSgl.uTerm false 6 3) skP_E6_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_4_cert : VectorCertificate (OrbSgl.uTerm false 6 4) skP_E6_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_5_cert : VectorCertificate (OrbSgl.uTerm false 6 5) skP_E6_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E6_6_cert : VectorCertificate (OrbSgl.uTerm false 6 6) skP_E6_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E6_cert : VectorCertificate (OrbSgl.uSum 6 skPf_E6) skY_E6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 0) skQ_E6_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 1) skQ_E6_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 2) skQ_E6_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 3) skQ_E6_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 4) skQ_E6_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 5) skQ_E6_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 6) skQ_E6_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 7) skQ_E6_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 8) skQ_E6_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E6_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E6 6 9) skQ_E6_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E6_cert : VectorCertificate (OrbSgl.vSum 6 skQf_E6) termE_6 := by decide +kernel

theorem skY_E6_value : evaluate skY_E6 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 6 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E6_cert]
  apply evaluate_uSum false 6 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E6_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E6_6_cert).symm

/-- The certified value of `termE_6`. -/
theorem sk_E6 : evaluate termE_6 = ((Nat.choose 15 6 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 6 (aVec false))
      (6 - (6 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E6_cert]
  apply evaluate_vSum false 6 (by norm_num) skY_E6 skY_E6_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E6_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E6_9_cert).symm

end VOA.Classification.COne.OrbSgl

import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,5) (u₍5₎a)₍1₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J5_0 : SectorVector := [(1, [(720, [0, 1, 1, 1]), (3960, [0, 3]), (-9720, [1, 2])]),
 (-1, [(-720, [0, 1, 1, 1]), (-3960, [0, 3]), (-9720, [1, 2])])]

def skP_J5_1 : SectorVector := [(-1, [(2160, [0, 1, 1, 1]), (-4320, [0, 3]), (12960, [1, 2])]),
 (1, [(-2160, [0, 1, 1, 1]), (4320, [0, 3]), (12960, [1, 2])])]

def skP_J5_2 : SectorVector := [(1, [(-10800, [0, 1, 1, 1]), (-2700, [0, 3]), (-32400, [1, 2])]),
 (-1, [(10800, [0, 1, 1, 1]), (2700, [0, 3]), (-32400, [1, 2])])]

def skP_J5_3 : SectorVector := [(-1, [(-86400, [0, 1, 1, 1]), (-21600, [0, 3]), (259200, [1, 2])]),
 (1, [(86400, [0, 1, 1, 1]), (21600, [0, 3]), (259200, [1, 2])])]

def skP_J5_4 : SectorVector := [(1, []), (-1, [])]

def skP_J5_5 : SectorVector := [(-1, []), (1, [])]

def skP_J5_6 : SectorVector := [(1, []), (-1, [])]

def skP_J5_7 : SectorVector := [(-1, []), (1, [])]

def skY_J5 : SectorVector := [(1, [(-16920, [0, 1, 1, 1]), (-5310, [0, 3]), (-82080, [1, 2])]),
 (-1, [(16920, [0, 1, 1, 1]), (5310, [0, 3]), (-82080, [1, 2])])]

def skQ_J5_0 : SectorVector := [(-1,
  [(1015200, [0, 1, 1, 1, 1, 1]),
   (9461880, [0, 1, 1, 3]),
   (6956280, [0, 1, 2, 2]),
   (4600800, [0, 5]),
   (-19638720, [1, 1, 1, 2]),
   (-25116480, [1, 4]),
   (-14383440, [2, 3])]),
 (1,
  [(-1015200, [0, 1, 1, 1, 1, 1]),
   (-9461880, [0, 1, 1, 3]),
   (-6956280, [0, 1, 2, 2]),
   (-4600800, [0, 5]),
   (-19638720, [1, 1, 1, 2]),
   (-25116480, [1, 4]),
   (-14383440, [2, 3])])]

def skQ_J5_1 : SectorVector := [(1,
  [(-9590400, [0, 1, 1, 1, 1, 1]),
   (-54645840, [0, 1, 1, 3]),
   (-36514800, [0, 1, 2, 2]),
   (-19550160, [0, 5]),
   (-142845120, [1, 1, 1, 2]),
   (-124675200, [1, 4]),
   (-70100640, [2, 3])]),
 (-1,
  [(9590400, [0, 1, 1, 1, 1, 1]),
   (54645840, [0, 1, 1, 3]),
   (36514800, [0, 1, 2, 2]),
   (19550160, [0, 5]),
   (-142845120, [1, 1, 1, 2]),
   (-124675200, [1, 4]),
   (-70100640, [2, 3])])]

def skQ_J5_2 : SectorVector := [(-1,
  [(65810880, [0, 1, 1, 1, 1, 1]),
   (258519600, [0, 1, 1, 3]),
   (173463120, [0, 1, 2, 2]),
   (65532240, [0, 5]),
   (-791622720, [1, 1, 1, 2]),
   (-510338880, [1, 4]),
   (-291898080, [2, 3])]),
 (1,
  [(-65810880, [0, 1, 1, 1, 1, 1]),
   (-258519600, [0, 1, 1, 3]),
   (-173463120, [0, 1, 2, 2]),
   (-65532240, [0, 5]),
   (-791622720, [1, 1, 1, 2]),
   (-510338880, [1, 4]),
   (-291898080, [2, 3])])]

def skQ_J5_3 : SectorVector := [(1,
  [(-313735680, [0, 1, 1, 1, 1, 1]),
   (-924773760, [0, 1, 1, 3]),
   (-658471680, [0, 1, 2, 2]),
   (-187868160, [0, 5]),
   (-3324602880, [1, 1, 1, 2]),
   (-1597812480, [1, 4]),
   (-971585280, [2, 3])]),
 (-1,
  [(313735680, [0, 1, 1, 1, 1, 1]),
   (924773760, [0, 1, 1, 3]),
   (658471680, [0, 1, 2, 2]),
   (187868160, [0, 5]),
   (-3324602880, [1, 1, 1, 2]),
   (-1597812480, [1, 4]),
   (-971585280, [2, 3])])]

def skQ_J5_4 : SectorVector := [(-1,
  [(951160320, [0, 1, 1, 1, 1, 1]),
   (2377900800, [0, 1, 1, 3]),
   (1783425600, [0, 1, 2, 2]),
   (356685120, [0, 5]),
   (-9511603200, [1, 1, 1, 2]),
   (-3566851200, [1, 4]),
   (-2377900800, [2, 3])]),
 (1,
  [(-951160320, [0, 1, 1, 1, 1, 1]),
   (-2377900800, [0, 1, 1, 3]),
   (-1783425600, [0, 1, 2, 2]),
   (-356685120, [0, 5]),
   (-9511603200, [1, 1, 1, 2]),
   (-3566851200, [1, 4]),
   (-2377900800, [2, 3])])]

def skQ_J5_5 : SectorVector := [(1,
  [(-1395947520, [0, 1, 1, 1, 1, 1]),
   (-3489868800, [0, 1, 1, 3]),
   (-2617401600, [0, 1, 2, 2]),
   (-523480320, [0, 5]),
   (-13959475200, [1, 1, 1, 2]),
   (-5234803200, [1, 4]),
   (-3489868800, [2, 3])]),
 (-1,
  [(1395947520, [0, 1, 1, 1, 1, 1]),
   (3489868800, [0, 1, 1, 3]),
   (2617401600, [0, 1, 2, 2]),
   (523480320, [0, 5]),
   (-13959475200, [1, 1, 1, 2]),
   (-5234803200, [1, 4]),
   (-3489868800, [2, 3])])]

def skQ_J5_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J5_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J5_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J5_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J5 : ℕ → SectorVector
  | 0 => skP_J5_0
  | 1 => skP_J5_1
  | 2 => skP_J5_2
  | 3 => skP_J5_3
  | 4 => skP_J5_4
  | 5 => skP_J5_5
  | 6 => skP_J5_6
  | 7 => skP_J5_7
  | _ => []

def skQf_J5 : ℕ → SectorVector
  | 0 => skQ_J5_0
  | 1 => skQ_J5_1
  | 2 => skQ_J5_2
  | 3 => skQ_J5_3
  | 4 => skQ_J5_4
  | 5 => skQ_J5_5
  | 6 => skQ_J5_6
  | 7 => skQ_J5_7
  | 8 => skQ_J5_8
  | 9 => skQ_J5_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J5_0_cert : VectorCertificate (OrbSgl.uTerm true 5 0) skP_J5_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_1_cert : VectorCertificate (OrbSgl.uTerm true 5 1) skP_J5_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_2_cert : VectorCertificate (OrbSgl.uTerm true 5 2) skP_J5_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_3_cert : VectorCertificate (OrbSgl.uTerm true 5 3) skP_J5_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_4_cert : VectorCertificate (OrbSgl.uTerm true 5 4) skP_J5_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_5_cert : VectorCertificate (OrbSgl.uTerm true 5 5) skP_J5_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_6_cert : VectorCertificate (OrbSgl.uTerm true 5 6) skP_J5_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J5_7_cert : VectorCertificate (OrbSgl.uTerm true 5 7) skP_J5_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J5_cert : VectorCertificate (OrbSgl.uSum 5 skPf_J5) skY_J5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 0) skQ_J5_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 1) skQ_J5_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 2) skQ_J5_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 3) skQ_J5_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 4) skQ_J5_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 5) skQ_J5_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 6) skQ_J5_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 7) skQ_J5_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 8) skQ_J5_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J5_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J5 5 9) skQ_J5_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J5_cert : VectorCertificate (OrbSgl.vSum 5 skQf_J5) termJ_5 := by decide +kernel

theorem skY_J5_value : evaluate skY_J5 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 5 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J5_cert]
  apply evaluate_uSum true 5 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J5_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J5_7_cert).symm

/-- The certified value of `termJ_5`. -/
theorem sk_J5 : evaluate termJ_5 = ((Nat.choose 15 5 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 5 (aVec true))
      (6 - (5 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J5_cert]
  apply evaluate_vSum true 5 (by norm_num) skY_J5 skY_J5_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J5_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J5_9_cert).symm

end VOA.Classification.COne.OrbSgl

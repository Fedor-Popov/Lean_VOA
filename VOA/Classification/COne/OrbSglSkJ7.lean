import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,7) (u₍7₎a)₍-1₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J7_0 : SectorVector := [(1, [(-1350, [0, 1])]), (-1, [(1350, [0, 1])])]

def skP_J7_1 : SectorVector := [(-1, [(-10800, [0, 1])]), (1, [(10800, [0, 1])])]

def skP_J7_2 : SectorVector := [(1, []), (-1, [])]

def skP_J7_3 : SectorVector := [(-1, []), (1, [])]

def skP_J7_4 : SectorVector := [(1, []), (-1, [])]

def skP_J7_5 : SectorVector := [(-1, []), (1, [])]

def skY_J7 : SectorVector := [(1, [(-12150, [0, 1])]), (-1, [(12150, [0, 1])])]

def skQ_J7_0 : SectorVector := [(-1,
  [(12150, [0, 1, 1, 1, 1, 1]),
   (1287900, [0, 1, 1, 3]),
   (747225, [0, 1, 2, 2]),
   (656100, [0, 5]),
   (-1166400, [1, 1, 1, 2]),
   (-3790800, [1, 4]),
   (-2332800, [2, 3])]),
 (1,
  [(-12150, [0, 1, 1, 1, 1, 1]),
   (-1287900, [0, 1, 1, 3]),
   (-747225, [0, 1, 2, 2]),
   (-656100, [0, 5]),
   (-1166400, [1, 1, 1, 2]),
   (-3790800, [1, 4]),
   (-2332800, [2, 3])])]

def skQ_J7_1 : SectorVector := [(1,
  [(-388800, [0, 1, 1, 1, 1, 1]),
   (-7095600, [0, 1, 1, 3]),
   (-3790800, [0, 1, 2, 2]),
   (-3207600, [0, 5]),
   (-12052800, [1, 1, 1, 2]),
   (-19828800, [1, 4]),
   (-9136800, [2, 3])]),
 (-1,
  [(388800, [0, 1, 1, 1, 1, 1]),
   (7095600, [0, 1, 1, 3]),
   (3790800, [0, 1, 2, 2]),
   (3207600, [0, 5]),
   (-12052800, [1, 1, 1, 2]),
   (-19828800, [1, 4]),
   (-9136800, [2, 3])])]

def skQ_J7_2 : SectorVector := [(-1,
  [(5054400, [0, 1, 1, 1, 1, 1]),
   (31006800, [0, 1, 1, 3]),
   (18662400, [0, 1, 2, 2]),
   (11080800, [0, 5]),
   (-75038400, [1, 1, 1, 2]),
   (-74066400, [1, 4]),
   (-37130400, [2, 3])]),
 (1,
  [(-5054400, [0, 1, 1, 1, 1, 1]),
   (-31006800, [0, 1, 1, 3]),
   (-18662400, [0, 1, 2, 2]),
   (-11080800, [0, 5]),
   (-75038400, [1, 1, 1, 2]),
   (-74066400, [1, 4]),
   (-37130400, [2, 3])])]

def skQ_J7_3 : SectorVector := [(1,
  [(-32659200, [0, 1, 1, 1, 1, 1]),
   (-106142400, [0, 1, 1, 3]),
   (-73483200, [0, 1, 2, 2]),
   (-24494400, [0, 5]),
   (-359251200, [1, 1, 1, 2]),
   (-195955200, [1, 4]),
   (-114307200, [2, 3])]),
 (-1,
  [(32659200, [0, 1, 1, 1, 1, 1]),
   (106142400, [0, 1, 1, 3]),
   (73483200, [0, 1, 2, 2]),
   (24494400, [0, 5]),
   (-359251200, [1, 1, 1, 2]),
   (-195955200, [1, 4]),
   (-114307200, [2, 3])])]

def skQ_J7_4 : SectorVector := [(-1,
  [(116640000, [0, 1, 1, 1, 1, 1]),
   (291600000, [0, 1, 1, 3]),
   (218700000, [0, 1, 2, 2]),
   (43740000, [0, 5]),
   (-1166400000, [1, 1, 1, 2]),
   (-437400000, [1, 4]),
   (-291600000, [2, 3])]),
 (1,
  [(-116640000, [0, 1, 1, 1, 1, 1]),
   (-291600000, [0, 1, 1, 3]),
   (-218700000, [0, 1, 2, 2]),
   (-43740000, [0, 5]),
   (-1166400000, [1, 1, 1, 2]),
   (-437400000, [1, 4]),
   (-291600000, [2, 3])])]

def skQ_J7_5 : SectorVector := [(1,
  [(-186624000, [0, 1, 1, 1, 1, 1]),
   (-466560000, [0, 1, 1, 3]),
   (-349920000, [0, 1, 2, 2]),
   (-69984000, [0, 5]),
   (-1866240000, [1, 1, 1, 2]),
   (-699840000, [1, 4]),
   (-466560000, [2, 3])]),
 (-1,
  [(186624000, [0, 1, 1, 1, 1, 1]),
   (466560000, [0, 1, 1, 3]),
   (349920000, [0, 1, 2, 2]),
   (69984000, [0, 5]),
   (-1866240000, [1, 1, 1, 2]),
   (-699840000, [1, 4]),
   (-466560000, [2, 3])])]

def skQ_J7_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J7_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J7_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J7_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J7 : ℕ → SectorVector
  | 0 => skP_J7_0
  | 1 => skP_J7_1
  | 2 => skP_J7_2
  | 3 => skP_J7_3
  | 4 => skP_J7_4
  | 5 => skP_J7_5
  | _ => []

def skQf_J7 : ℕ → SectorVector
  | 0 => skQ_J7_0
  | 1 => skQ_J7_1
  | 2 => skQ_J7_2
  | 3 => skQ_J7_3
  | 4 => skQ_J7_4
  | 5 => skQ_J7_5
  | 6 => skQ_J7_6
  | 7 => skQ_J7_7
  | 8 => skQ_J7_8
  | 9 => skQ_J7_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J7_0_cert : VectorCertificate (OrbSgl.uTerm true 7 0) skP_J7_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J7_1_cert : VectorCertificate (OrbSgl.uTerm true 7 1) skP_J7_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J7_2_cert : VectorCertificate (OrbSgl.uTerm true 7 2) skP_J7_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J7_3_cert : VectorCertificate (OrbSgl.uTerm true 7 3) skP_J7_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J7_4_cert : VectorCertificate (OrbSgl.uTerm true 7 4) skP_J7_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J7_5_cert : VectorCertificate (OrbSgl.uTerm true 7 5) skP_J7_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J7_cert : VectorCertificate (OrbSgl.uSum 7 skPf_J7) skY_J7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 0) skQ_J7_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 1) skQ_J7_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 2) skQ_J7_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 3) skQ_J7_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 4) skQ_J7_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 5) skQ_J7_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 6) skQ_J7_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 7) skQ_J7_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 8) skQ_J7_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J7_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J7 7 9) skQ_J7_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J7_cert : VectorCertificate (OrbSgl.vSum 7 skQf_J7) termJ_7 := by decide +kernel

theorem skY_J7_value : evaluate skY_J7 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 7 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J7_cert]
  apply evaluate_uSum true 7 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J7_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J7_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J7_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J7_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J7_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J7_5_cert).symm

/-- The certified value of `termJ_7`. -/
theorem sk_J7 : evaluate termJ_7 = ((Nat.choose 15 7 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 7 (aVec true))
      (6 - (7 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J7_cert]
  apply evaluate_vSum true 7 (by norm_num) skY_J7 skY_J7_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J7_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J7_9_cert).symm

end VOA.Classification.COne.OrbSgl

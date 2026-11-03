import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,8) (u₍8₎a)₍-2₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J8_0 : SectorVector := [(1, [(10800, [])]), (-1, [(10800, [])])]

def skP_J8_1 : SectorVector := [(-1, []), (1, [])]

def skP_J8_2 : SectorVector := [(1, []), (-1, [])]

def skP_J8_3 : SectorVector := [(-1, []), (1, [])]

def skP_J8_4 : SectorVector := [(1, []), (-1, [])]

def skY_J8 : SectorVector := [(-1, [(-10800, [])]), (1, [(-10800, [])])]

def skQ_J8_0 : SectorVector := [(1,
  [(-129600, [0, 1, 1, 3]),
   (-129600, [0, 1, 2, 2]),
   (-64800, [0, 5]),
   (-43200, [1, 1, 1, 2]),
   (-972000, [1, 4]),
   (-1080000, [2, 3])]),
 (-1,
  [(129600, [0, 1, 1, 3]),
   (129600, [0, 1, 2, 2]),
   (64800, [0, 5]),
   (-43200, [1, 1, 1, 2]),
   (-972000, [1, 4]),
   (-1080000, [2, 3])])]

def skQ_J8_1 : SectorVector := [(-1,
  [(10800, [0, 1, 1, 1, 1, 1]),
   (1274400, [0, 1, 1, 3]),
   (793800, [0, 1, 2, 2]),
   (648000, [0, 5]),
   (-1080000, [1, 1, 1, 2]),
   (-4341600, [1, 4]),
   (-3153600, [2, 3])]),
 (1,
  [(-10800, [0, 1, 1, 1, 1, 1]),
   (-1274400, [0, 1, 1, 3]),
   (-793800, [0, 1, 2, 2]),
   (-648000, [0, 5]),
   (-1080000, [1, 1, 1, 2]),
   (-4341600, [1, 4]),
   (-3153600, [2, 3])])]

def skQ_J8_2 : SectorVector := [(1,
  [(-345600, [0, 1, 1, 1, 1, 1]),
   (-6307200, [0, 1, 1, 3]),
   (-3369600, [0, 1, 2, 2]),
   (-2851200, [0, 5]),
   (-10713600, [1, 1, 1, 2]),
   (-17625600, [1, 4]),
   (-8121600, [2, 3])]),
 (-1,
  [(345600, [0, 1, 1, 1, 1, 1]),
   (6307200, [0, 1, 1, 3]),
   (3369600, [0, 1, 2, 2]),
   (2851200, [0, 5]),
   (-10713600, [1, 1, 1, 2]),
   (-17625600, [1, 4]),
   (-8121600, [2, 3])])]

def skQ_J8_3 : SectorVector := [(-1,
  [(4147200, [0, 1, 1, 1, 1, 1]),
   (21254400, [0, 1, 1, 3]),
   (13219200, [0, 1, 2, 2]),
   (6998400, [0, 5]),
   (-55987200, [1, 1, 1, 2]),
   (-48211200, [1, 4]),
   (-24883200, [2, 3])]),
 (1,
  [(-4147200, [0, 1, 1, 1, 1, 1]),
   (-21254400, [0, 1, 1, 3]),
   (-13219200, [0, 1, 2, 2]),
   (-6998400, [0, 5]),
   (-55987200, [1, 1, 1, 2]),
   (-48211200, [1, 4]),
   (-24883200, [2, 3])])]

def skQ_J8_4 : SectorVector := [(1,
  [(-20736000, [0, 1, 1, 1, 1, 1]),
   (-51840000, [0, 1, 1, 3]),
   (-38880000, [0, 1, 2, 2]),
   (-7776000, [0, 5]),
   (-207360000, [1, 1, 1, 2]),
   (-77760000, [1, 4]),
   (-51840000, [2, 3])]),
 (-1,
  [(20736000, [0, 1, 1, 1, 1, 1]),
   (51840000, [0, 1, 1, 3]),
   (38880000, [0, 1, 2, 2]),
   (7776000, [0, 5]),
   (-207360000, [1, 1, 1, 2]),
   (-77760000, [1, 4]),
   (-51840000, [2, 3])])]

def skQ_J8_5 : SectorVector := [(-1,
  [(41472000, [0, 1, 1, 1, 1, 1]),
   (103680000, [0, 1, 1, 3]),
   (77760000, [0, 1, 2, 2]),
   (15552000, [0, 5]),
   (-414720000, [1, 1, 1, 2]),
   (-155520000, [1, 4]),
   (-103680000, [2, 3])]),
 (1,
  [(-41472000, [0, 1, 1, 1, 1, 1]),
   (-103680000, [0, 1, 1, 3]),
   (-77760000, [0, 1, 2, 2]),
   (-15552000, [0, 5]),
   (-414720000, [1, 1, 1, 2]),
   (-155520000, [1, 4]),
   (-103680000, [2, 3])])]

def skQ_J8_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J8_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J8_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J8_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J8 : ℕ → SectorVector
  | 0 => skP_J8_0
  | 1 => skP_J8_1
  | 2 => skP_J8_2
  | 3 => skP_J8_3
  | 4 => skP_J8_4
  | _ => []

def skQf_J8 : ℕ → SectorVector
  | 0 => skQ_J8_0
  | 1 => skQ_J8_1
  | 2 => skQ_J8_2
  | 3 => skQ_J8_3
  | 4 => skQ_J8_4
  | 5 => skQ_J8_5
  | 6 => skQ_J8_6
  | 7 => skQ_J8_7
  | 8 => skQ_J8_8
  | 9 => skQ_J8_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J8_0_cert : VectorCertificate (OrbSgl.uTerm true 8 0) skP_J8_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J8_1_cert : VectorCertificate (OrbSgl.uTerm true 8 1) skP_J8_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J8_2_cert : VectorCertificate (OrbSgl.uTerm true 8 2) skP_J8_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J8_3_cert : VectorCertificate (OrbSgl.uTerm true 8 3) skP_J8_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J8_4_cert : VectorCertificate (OrbSgl.uTerm true 8 4) skP_J8_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J8_cert : VectorCertificate (OrbSgl.uSum 8 skPf_J8) skY_J8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 0) skQ_J8_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 1) skQ_J8_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 2) skQ_J8_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 3) skQ_J8_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 4) skQ_J8_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 5) skQ_J8_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 6) skQ_J8_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 7) skQ_J8_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 8) skQ_J8_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J8_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J8 8 9) skQ_J8_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J8_cert : VectorCertificate (OrbSgl.vSum 8 skQf_J8) termJ_8 := by decide +kernel

theorem skY_J8_value : evaluate skY_J8 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 8 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J8_cert]
  apply evaluate_uSum true 8 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J8_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J8_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J8_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J8_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J8_4_cert).symm

/-- The certified value of `termJ_8`. -/
theorem sk_J8 : evaluate termJ_8 = ((Nat.choose 15 8 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 8 (aVec true))
      (6 - (8 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J8_cert]
  apply evaluate_vSum true 8 (by norm_num) skY_J8 skY_J8_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J8_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J8_9_cert).symm

end VOA.Classification.COne.OrbSgl

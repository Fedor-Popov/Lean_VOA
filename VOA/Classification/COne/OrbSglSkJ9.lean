import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,9) (u₍9₎a)₍-3₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J9_0 : SectorVector := [(1, []), (-1, [])]

def skP_J9_1 : SectorVector := [(-1, []), (1, [])]

def skP_J9_2 : SectorVector := [(1, []), (-1, [])]

def skP_J9_3 : SectorVector := [(-1, []), (1, [])]

def skY_J9 : SectorVector := [(1, []), (-1, [])]

def skQ_J9_0 : SectorVector := [(-1, []), (1, [])]

def skQ_J9_1 : SectorVector := [(1, []), (-1, [])]

def skQ_J9_2 : SectorVector := [(-1, []), (1, [])]

def skQ_J9_3 : SectorVector := [(1, []), (-1, [])]

def skQ_J9_4 : SectorVector := [(-1, []), (1, [])]

def skQ_J9_5 : SectorVector := [(1, []), (-1, [])]

def skQ_J9_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J9_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J9_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J9_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J9 : ℕ → SectorVector
  | 0 => skP_J9_0
  | 1 => skP_J9_1
  | 2 => skP_J9_2
  | 3 => skP_J9_3
  | _ => []

def skQf_J9 : ℕ → SectorVector
  | 0 => skQ_J9_0
  | 1 => skQ_J9_1
  | 2 => skQ_J9_2
  | 3 => skQ_J9_3
  | 4 => skQ_J9_4
  | 5 => skQ_J9_5
  | 6 => skQ_J9_6
  | 7 => skQ_J9_7
  | 8 => skQ_J9_8
  | 9 => skQ_J9_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J9_0_cert : VectorCertificate (OrbSgl.uTerm true 9 0) skP_J9_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J9_1_cert : VectorCertificate (OrbSgl.uTerm true 9 1) skP_J9_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J9_2_cert : VectorCertificate (OrbSgl.uTerm true 9 2) skP_J9_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J9_3_cert : VectorCertificate (OrbSgl.uTerm true 9 3) skP_J9_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J9_cert : VectorCertificate (OrbSgl.uSum 9 skPf_J9) skY_J9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 0) skQ_J9_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 1) skQ_J9_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 2) skQ_J9_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 3) skQ_J9_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 4) skQ_J9_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 5) skQ_J9_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 6) skQ_J9_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 7) skQ_J9_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 8) skQ_J9_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J9_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J9 9 9) skQ_J9_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J9_cert : VectorCertificate (OrbSgl.vSum 9 skQf_J9) termJ_9 := by decide +kernel

theorem skY_J9_value : evaluate skY_J9 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 9 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J9_cert]
  apply evaluate_uSum true 9 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J9_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J9_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J9_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J9_3_cert).symm

/-- The certified value of `termJ_9`. -/
theorem sk_J9 : evaluate termJ_9 = ((Nat.choose 15 9 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 9 (aVec true))
      (6 - (9 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J9_cert]
  apply evaluate_vSum true 9 (by norm_num) skY_J9 skY_J9_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J9_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J9_9_cert).symm

end VOA.Classification.COne.OrbSgl
